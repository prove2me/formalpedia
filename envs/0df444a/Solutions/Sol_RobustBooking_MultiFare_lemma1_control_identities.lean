-- Prove2me | solution 1 for RobustBooking.MultiFare.lemma1_control_identities
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:34:48.034254+00:00
-- url     : https://prove2.me/submissions/e4c50caa-9069-4858-afcc-5017aba975a5

import Mathlib
import Definitions.Def_RobustBooking_MultiFare_ProtectionLevels

namespace Aux_RB_l1

lemma reindex (g : ℕ → ℝ) (k : ℕ) :
    ∑ i ∈ Finset.Icc 2 (k + 1), g i = ∑ j ∈ Finset.Icc 1 k, g (j + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_Icc_succ_top (by omega)]

end Aux_RB_l1

open RobustBooking.MultiFare in
theorem solution (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n) :
    (∀ i ∈ Finset.Icc 1 (m - 1),
        f i * (Q m f n i - Q m f n (i + 1)) = n / Delta m f * (f i - f (i + 1))) ∧
    f m * (Q m f n m - Q m f n (m + 1)) = f m * n / Delta m f ∧
    (∀ i' ∈ Finset.Icc 1 m,
        ∑ i ∈ Finset.Icc i' m, f i * (Q m f n i - Q m f n (i + 1)) = f i' * (n / Delta m f)) := by
  set S : ℕ → ℝ := fun k => ∑ j ∈ Finset.Icc 1 k, f (j + 1) / f j with hSdef
  have hS_succ : ∀ k, S (k + 1) = S k + f (k + 1 + 1) / f (k + 1) := by
    intro k
    simp only [hSdef]
    rw [Finset.sum_Icc_succ_top (by omega)]
  have hpos : ∀ i, 1 ≤ i → i ≤ m → 0 < f i := by
    intro i h1 h2
    rcases h2.lt_or_eq with h | h
    · exact lt_trans hfm (hf ⟨h1, h2⟩ ⟨by omega, le_refl m⟩ h)
    · rw [h]; exact hfm
  have hΔ : Delta m f = (m : ℝ) - S (m - 1) := by
    unfold Delta
    have : m = (m - 1) + 1 := by omega
    conv_lhs => rw [this]
    rw [Aux_RB_l1.reindex]
    simp only [hSdef, Nat.add_sub_cancel]
    rw [← this]
  have hSlt : S (m - 1) < ((m - 1 : ℕ) : ℝ) := by
    simp only [hSdef]
    have hne : (Finset.Icc 1 (m - 1)).Nonempty := ⟨1, by simp; omega⟩
    calc ∑ j ∈ Finset.Icc 1 (m - 1), f (j + 1) / f j < ∑ j ∈ Finset.Icc 1 (m - 1), (1 : ℝ) := by
          apply Finset.sum_lt_sum_of_nonempty hne
          intro j hj
          rw [Finset.mem_Icc] at hj
          have hj0 := hpos j hj.1 (by omega)
          rw [div_lt_one hj0]
          exact hf ⟨hj.1, by omega⟩ ⟨by omega, by omega⟩ (by omega)
      _ = ((m - 1 : ℕ) : ℝ) := by simp
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]; simp
  have hΔpos : 0 < Delta m f := by rw [hΔ]; linarith
  have hθ : ∀ k, k < m → theta m f n k = n / Delta m f * ((k : ℝ) - S k) := by
    intro k hk
    unfold theta
    by_cases h0 : k = 0
    · subst h0; simp [hSdef]
    · rw [if_neg h0, if_pos hk]
  have hθm : theta m f n m = n := by
    unfold theta
    rw [if_neg (by omega), if_neg (lt_irrefl m)]
  have hpart1 : ∀ i ∈ Finset.Icc 1 (m - 1),
      f i * (Q m f n i - Q m f n (i + 1)) = n / Delta m f * (f i - f (i + 1)) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have e1 : Q m f n (k + 1) - Q m f n (k + 1 + 1) = theta m f n (k + 1) - theta m f n k := by
      unfold Q; simp only [Nat.add_sub_cancel]; ring
    rw [e1, hθ (k + 1) (by omega), hθ k (by omega), hS_succ]
    have hk0 := hpos (k + 1) (by omega) (by omega)
    push_cast
    field_simp
    ring
  have hpart2 : f m * (Q m f n m - Q m f n (m + 1)) = f m * n / Delta m f := by
    have e2 : Q m f n m - Q m f n (m + 1) = theta m f n m - theta m f n (m - 1) := by
      unfold Q; simp only [Nat.add_sub_cancel]; ring
    rw [e2, hθm, hθ (m - 1) (by omega)]
    have hc : ((m - 1 : ℕ) : ℝ) - S (m - 1) = Delta m f - 1 := by
      rw [hΔ, hcast]; ring
    rw [hc]
    field_simp
    ring
  refine ⟨hpart1, hpart2, ?_⟩
  have hTm : f m * (Q m f n m - Q m f n (m + 1)) = f m * (n / Delta m f) := by
    rw [hpart2]; ring
  have claim : ∀ d a, a + d = m → 1 ≤ a →
      ∑ i ∈ Finset.Icc a m, f i * (Q m f n i - Q m f n (i + 1)) = f a * (n / Delta m f) := by
    intro d
    induction d with
    | zero =>
      intro a ha _
      have : a = m := by omega
      subst this
      rw [Finset.Icc_self, Finset.sum_singleton, hTm]
    | succ d ih =>
      intro a ha h1
      rw [← Finset.add_sum_Ioc_eq_sum_Icc (by omega : a ≤ m), ← Finset.Icc_add_one_left_eq_Ioc,
        ih (a + 1) (by omega) (by omega),
        hpart1 a (Finset.mem_Icc.mpr ⟨h1, by omega⟩)]
      ring
  intro i' hi'
  rw [Finset.mem_Icc] at hi'
  exact claim (m - i') i' (by omega) hi'.1
