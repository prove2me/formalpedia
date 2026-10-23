-- Prove2me | solution 1 for TeleDriving.ScarceFleet.theorem_1A
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T07:19:04.748388+00:00
-- url     : https://prove2.me/submissions/15ae073d-c44f-4c2d-ad1f-15c3523a5c51

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

set_option autoImplicit false

namespace TD1A

open TeleDriving.ScarceFleet

lemma weight_succ (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m j : ℕ) :
    weight mu lam m (j + 1) = weight mu lam m j * rho mu lam m ((j + 1 : ℕ) : ℝ) := by
  unfold weight
  rw [Finset.prod_Icc_succ_top (by omega)]

lemma weight_pos (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m : ℕ)
    (hρ : ∀ k : ℕ, 1 ≤ k → k ≤ m → 0 < rho mu lam m (k : ℝ)) (n : ℕ) (hn : n ≤ m) :
    0 < weight mu lam m n := by
  unfold weight
  apply Finset.prod_pos
  intro k hk
  have := Finset.mem_Icc.mp hk
  exact hρ k this.1 (by omega)

lemma W_succ (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m n : ℕ) :
    1 + ∑ i ∈ Finset.Icc 1 (n + 1), weight mu lam m i
      = (1 + ∑ i ∈ Finset.Icc 1 n, weight mu lam m i) + weight mu lam m (n + 1) := by
  rw [Finset.sum_Icc_succ_top (by omega)]; ring

lemma W_pos (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m : ℕ)
    (hρ : ∀ k : ℕ, 1 ≤ k → k ≤ m → 0 < rho mu lam m (k : ℝ)) (n : ℕ) (hn : n ≤ m) :
    0 < 1 + ∑ i ∈ Finset.Icc 1 n, weight mu lam m i := by
  have : 0 ≤ ∑ i ∈ Finset.Icc 1 n, weight mu lam m i := by
    apply Finset.sum_nonneg
    intro i hi
    have := Finset.mem_Icc.mp hi
    exact (weight_pos mu lam m hρ i (by omega)).le
  linarith

lemma SL_zero (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m : ℕ) : SL mu lam m 0 = 0 := by
  unfold SL piMN weight
  simp

lemma alg_SL (wn Wn g lam : ℝ) (hW : 0 < Wn) (hg : 0 < g) (hw : 0 ≤ wn) (hl : 0 ≤ lam) :
    (1 - wn * (lam / g) / (Wn + wn * (lam / g))) - (1 - wn / Wn)
      = wn / ((Wn + wn * (lam / g)) * g) * (g - lam * (1 - wn / Wn)) := by
  have h1 : 0 < Wn + wn * (lam / g) := by positivity
  field_simp
  ring

lemma alg_T (wn Wn g lam : ℝ) (hW : 0 < Wn) (hg : 0 < g) (hw : 0 ≤ wn) (hl : 0 ≤ lam) :
    lam * (1 - wn * (lam / g) / (Wn + wn * (lam / g))) - g
      = Wn / (Wn + wn * (lam / g)) * (lam * (1 - wn / Wn) - g) := by
  have h1 : 0 < Wn + wn * (lam / g) := by positivity
  field_simp
  ring

lemma step_SL (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m n : ℕ)
    (hρ : ∀ k : ℕ, 1 ≤ k → k ≤ m → 0 < rho mu lam m (k : ℝ)) (hn : n + 1 ≤ m)
    (hg : 0 < ((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ)) (hl : 0 ≤ lam) :
    ∃ c > 0, SL mu lam m (n + 1) - SL mu lam m n
      = c * (((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ) - lam * SL mu lam m n) := by
  have hW := W_pos mu lam m hρ n (by omega)
  have hw := weight_pos mu lam m hρ n (by omega)
  have h1 : 0 < (1 + ∑ i ∈ Finset.Icc 1 n, weight mu lam m i)
      + weight mu lam m n * (lam / (((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ))) := by
    positivity
  refine ⟨weight mu lam m n / (((1 + ∑ i ∈ Finset.Icc 1 n, weight mu lam m i)
      + weight mu lam m n * (lam / (((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ))))
      * (((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ))), by positivity, ?_⟩
  unfold SL piMN
  rw [W_succ, weight_succ]
  unfold rho
  exact alg_SL _ _ _ _ hW hg hw.le hl

lemma step_T (mu : ℕ → ℝ → ℝ) (lam : ℝ) (m n : ℕ)
    (hρ : ∀ k : ℕ, 1 ≤ k → k ≤ m → 0 < rho mu lam m (k : ℝ)) (hn : n + 1 ≤ m)
    (hg : 0 < ((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ)) (hl : 0 ≤ lam) :
    ∃ d > 0, lam * SL mu lam m (n + 1) - ((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ)
      = d * (lam * SL mu lam m n - ((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ)) := by
  have hW := W_pos mu lam m hρ n (by omega)
  have hw := weight_pos mu lam m hρ n (by omega)
  have h1 : 0 < (1 + ∑ i ∈ Finset.Icc 1 n, weight mu lam m i)
      + weight mu lam m n * (lam / (((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ))) := by
    positivity
  refine ⟨(1 + ∑ i ∈ Finset.Icc 1 n, weight mu lam m i) / ((1 + ∑ i ∈ Finset.Icc 1 n, weight mu lam m i)
      + weight mu lam m n * (lam / (((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ)))), by positivity, ?_⟩
  unfold SL piMN
  rw [W_succ, weight_succ]
  unfold rho
  exact alg_T _ _ _ _ hW hg hw.le hl

end TD1A

open TD1A in
open TeleDriving.ScarceFleet in
theorem solution (mu : ℕ → ℝ → ℝ) (s lam : ℝ) (mbar m : ℕ) (hA1 : Assumption1 mu s)
    (hA2 : Assumption2 mu mbar) (hsize : StandingSize mu s mbar m lam)
    (hreg : IsSupplyLimited mu lam m) :
    (lam * SL mu lam m m > (m : ℝ) * mu m (m : ℝ) →
      ∃ n1 : ℕ, 1 ≤ n1 ∧ n1 ≤ m - 1 ∧
        StrictMonoOn (SL mu lam m) (Set.Icc 1 n1) ∧
        AntitoneOn (SL mu lam m) (Set.Icc n1 m) ∧
        StrictAntiOn (SL mu lam m) (Set.Icc (n1 + 1) m)) ∧
    (¬ (lam * SL mu lam m m > (m : ℝ) * mu m (m : ℝ)) →
      MonotoneOn (SL mu lam m) (Set.Icc 1 m)) := by
  classical
  obtain ⟨hs, hmupos, -, -, -, -, -⟩ := hA1
  obtain ⟨hmbar, hlam, -⟩ := hsize
  obtain ⟨-, hA2'⟩ := hA2
  obtain ⟨qhat, ⟨hq1, hqm⟩, hinc, hdec⟩ := hA2' m hmbar
  have hlam0 : 0 < lam := lt_trans (by positivity) hlam
  have hρ : ∀ k : ℕ, 1 ≤ k → k ≤ m → 0 < rho mu lam m (k : ℝ) := by
    intro k hk1 hkm
    have := hreg (k : ℝ) ⟨by exact_mod_cast hk1, by exact_mod_cast hkm⟩
    linarith
  have hg : ∀ k : ℕ, 1 ≤ k → k ≤ m → 0 < (k : ℝ) * mu m (k : ℝ) := by
    intro k hk1 hkm
    have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have := hmupos m (k : ℝ) ⟨h1, by exact_mod_cast hkm⟩
    positivity
  -- (i)-(iv): the sign of SL(n+1) - SL(n) is the sign of g(n+1) - λ SL(n)
  have sI : ∀ n : ℕ, n + 1 ≤ m →
      lam * SL mu lam m n ≤ ((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ) →
      SL mu lam m n ≤ SL mu lam m (n + 1) := by
    intro n hn h
    obtain ⟨c, hc, he⟩ := step_SL mu lam m n hρ hn (hg (n + 1) (by omega) hn) hlam0.le
    have := mul_nonneg hc.le (sub_nonneg.2 h)
    linarith
  have sII : ∀ n : ℕ, n + 1 ≤ m →
      lam * SL mu lam m n < ((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ) →
      SL mu lam m n < SL mu lam m (n + 1) := by
    intro n hn h
    obtain ⟨c, hc, he⟩ := step_SL mu lam m n hρ hn (hg (n + 1) (by omega) hn) hlam0.le
    have := mul_pos hc (sub_pos.2 h)
    linarith
  have sIII : ∀ n : ℕ, n + 1 ≤ m →
      ((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ) ≤ lam * SL mu lam m n →
      SL mu lam m (n + 1) ≤ SL mu lam m n := by
    intro n hn h
    obtain ⟨c, hc, he⟩ := step_SL mu lam m n hρ hn (hg (n + 1) (by omega) hn) hlam0.le
    have := mul_nonneg hc.le (sub_nonneg.2 h)
    nlinarith
  have sIV : ∀ n : ℕ, n + 1 ≤ m →
      ((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ) < lam * SL mu lam m n →
      SL mu lam m (n + 1) < SL mu lam m n := by
    intro n hn h
    obtain ⟨c, hc, he⟩ := step_SL mu lam m n hρ hn (hg (n + 1) (by omega) hn) hlam0.le
    have := mul_pos hc (sub_pos.2 h)
    nlinarith
  -- in the increasing phase of q ↦ q µ(m,q), λ SL(n) < g(n+1)
  have INC : ∀ n : ℕ, n + 1 ≤ m → ((n + 1 : ℕ) : ℝ) ≤ qhat →
      lam * SL mu lam m n < ((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ) := by
    intro n
    induction n with
    | zero =>
      intro h1 _
      have := hg 1 le_rfl h1
      simpa [SL_zero] using this
    | succ n ih =>
      intro h1 h2
      have hcast : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show n + 1 ≤ n + 1 + 1 by omega)
      have ih' := ih (by omega) (le_trans hcast h2)
      obtain ⟨d, hd, he⟩ := step_T mu lam m n hρ (by omega) (hg (n + 1) (by omega) (by omega))
        hlam0.le
      have hlt : lam * SL mu lam m (n + 1) < ((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ) := by
        have := mul_pos hd (sub_pos.2 ih')
        nlinarith
      have hmono : ((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ)
          < ((n + 1 + 1 : ℕ) : ℝ) * mu m ((n + 1 + 1 : ℕ) : ℝ) :=
        hinc ⟨by exact_mod_cast (show 1 ≤ n + 1 by omega), le_trans hcast h2⟩
          ⟨by exact_mod_cast (show 1 ≤ n + 1 + 1 by omega), h2⟩
          (by exact_mod_cast (show n + 1 < n + 1 + 1 by omega))
      linarith
  -- once λ SL(n) ≥ g(n+1), it stays strictly above
  have PROP : ∀ n : ℕ, n + 1 + 1 ≤ m →
      ((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ) ≤ lam * SL mu lam m n →
      ((n + 1 + 1 : ℕ) : ℝ) * mu m ((n + 1 + 1 : ℕ) : ℝ) < lam * SL mu lam m (n + 1) := by
    intro n hn h
    have hq : qhat < ((n + 1 : ℕ) : ℝ) := by
      by_contra hc
      push_neg at hc
      have := INC n (by omega) hc
      linarith
    have hcast : ((n + 1 : ℕ) : ℝ) < ((n + 1 + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show n + 1 < n + 1 + 1 by omega)
    have hdec' : ((n + 1 + 1 : ℕ) : ℝ) * mu m ((n + 1 + 1 : ℕ) : ℝ)
        < ((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ) :=
      hdec ⟨hq.le, by exact_mod_cast (show n + 1 ≤ m by omega)⟩
        ⟨(hq.trans hcast).le, by exact_mod_cast hn⟩ hcast
    obtain ⟨d, hd, he⟩ := step_T mu lam m n hρ (by omega) (hg (n + 1) (by omega) (by omega))
      hlam0.le
    have := mul_nonneg hd.le (sub_nonneg.2 h)
    linarith
  have PROPstar : ∀ n k : ℕ,
      ((n + 1 : ℕ) : ℝ) * mu m ((n + 1 : ℕ) : ℝ) ≤ lam * SL mu lam m n → n + 1 ≤ k →
      k + 1 ≤ m → ((k + 1 : ℕ) : ℝ) * mu m ((k + 1 : ℕ) : ℝ) < lam * SL mu lam m k := by
    intro n k h hnk
    induction k, hnk using Nat.le_induction with
    | base => intro hk; exact PROP n hk h
    | succ k hk ih => intro hk1; exact PROP k hk1 (ih (by omega)).le
  refine ⟨fun h5 => ?_, fun h5 => ?_⟩
  · have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h
        simp [SL_zero] at h5
      · exact h
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hk : ((k + 1 : ℕ) : ℝ) * mu (k + 1) ((k + 1 : ℕ) : ℝ) < lam * SL mu lam (k + 1) k := by
      obtain ⟨d, hd, he⟩ := step_T mu lam (k + 1) k hρ le_rfl (hg (k + 1) (by omega) le_rfl)
        hlam0.le
      by_contra hc
      push_neg at hc
      have := mul_nonneg hd.le (sub_nonneg.2 hc)
      have h5' : ((k + 1 : ℕ) : ℝ) * mu (k + 1) ((k + 1 : ℕ) : ℝ)
          < lam * SL mu lam (k + 1) (k + 1) := h5
      nlinarith
    have hex : ∃ n, ((n + 1 : ℕ) : ℝ) * mu (k + 1) ((n + 1 : ℕ) : ℝ) ≤ lam * SL mu lam (k + 1) n :=
      ⟨k, hk.le⟩
    have hn1spec := Nat.find_spec hex
    have hn1le : Nat.find hex ≤ k := Nat.find_min' hex hk.le
    have hn1pos : 1 ≤ Nat.find hex := by
      by_contra h0
      push_neg at h0
      have h00 : Nat.find hex = 0 := by omega
      have h0' := hn1spec
      rw [h00] at h0'
      have := INC 0 (by omega) (by simp; linarith)
      linarith
    refine ⟨Nat.find hex, hn1pos, by omega, ?_, ?_, ?_⟩
    · apply strictMonoOn_of_lt_succ Set.ordConnected_Icc
      intro a _ ha hb
      simp only [Order.succ_eq_add_one] at hb ⊢
      have ha' := Set.mem_Icc.mp ha
      have hb' := Set.mem_Icc.mp hb
      have hlt : a < Nat.find hex := by omega
      have hnot := Nat.find_min hex hlt
      push_neg at hnot
      exact sII a (by omega) hnot
    · apply antitoneOn_of_succ_le Set.ordConnected_Icc
      intro a _ ha hb
      simp only [Order.succ_eq_add_one] at hb ⊢
      have ha' := Set.mem_Icc.mp ha
      have hb' := Set.mem_Icc.mp hb
      have hP : ((a + 1 : ℕ) : ℝ) * mu (k + 1) ((a + 1 : ℕ) : ℝ) ≤ lam * SL mu lam (k + 1) a := by
        rcases eq_or_lt_of_le ha'.1 with h | h
        · rw [← h]; exact hn1spec
        · exact (PROPstar _ a hn1spec (by omega) (by omega)).le
      exact sIII a (by omega) hP
    · apply strictAntiOn_of_succ_lt Set.ordConnected_Icc
      intro a _ ha hb
      simp only [Order.succ_eq_add_one] at hb ⊢
      have ha' := Set.mem_Icc.mp ha
      have hb' := Set.mem_Icc.mp hb
      exact sIV a (by omega) (PROPstar _ a hn1spec (by omega) (by omega))
  · apply monotoneOn_of_le_succ Set.ordConnected_Icc
    intro a _ ha hb
    simp only [Order.succ_eq_add_one] at hb ⊢
    have ha' := Set.mem_Icc.mp ha
    have hb' := Set.mem_Icc.mp hb
    by_contra hc
    have hP : ((a + 1 : ℕ) : ℝ) * mu m ((a + 1 : ℕ) : ℝ) < lam * SL mu lam m a := by
      by_contra h'
      push_neg at h'
      exact hc (sI a (by omega) h')
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hQ : ((k + 1 : ℕ) : ℝ) * mu (k + 1) ((k + 1 : ℕ) : ℝ) < lam * SL mu lam (k + 1) k := by
      rcases eq_or_lt_of_le (show a ≤ k by omega) with h | h
      · rw [h] at hP; exact hP
      · exact PROPstar a k hP.le (by omega) le_rfl
    obtain ⟨d, hd, he⟩ := step_T mu lam (k + 1) k hρ le_rfl (hg (k + 1) (by omega) le_rfl)
      hlam0.le
    apply h5
    have := mul_pos hd (sub_pos.2 hQ)
    show ((k + 1 : ℕ) : ℝ) * mu (k + 1) ((k + 1 : ℕ) : ℝ) < lam * SL mu lam (k + 1) (k + 1)
    linarith
