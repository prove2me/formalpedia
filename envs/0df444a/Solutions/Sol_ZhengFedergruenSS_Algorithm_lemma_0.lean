-- Prove2me | solution 1 for ZhengFedergruenSS.Algorithm.lemma_0
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:10:33.689216+00:00
-- url     : https://prove2.me/submissions/857340b4-3e9f-43dc-b9df-a93c48e20fad

import Mathlib
import Definitions.Def_VeinottWagnerSS_RenewalCost_Demand
import Definitions.Def_ZhengFedergruenSS_Algorithm_Model

set_option autoImplicit false

open ZhengFedergruenSS.Algorithm

lemma zfs_m_nonneg (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hp0 : p 0 < 1) : ∀ j, 0 ≤ m p j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    cases j with
    | zero =>
      rw [m]
      exact inv_nonneg.2 (by linarith)
    | succ j =>
      rw [m]
      refine mul_nonneg (inv_nonneg.2 (by linarith)) (Finset.sum_nonneg (fun i _ => ?_))
      exact mul_nonneg (hp _) (ih i.val (by omega))

lemma zfs_core (D : VeinottWagnerSS.RenewalCost.DemandDist) (hp0 : D.φ 0 < 1)
    (K : ℝ) (G : ℤ → ℝ) (s S : ℤ) (hsS : s < S) :
    0 < alpha D.φ (S - s).toNat ∧ alpha D.φ (S - s).toNat ≤ 1 ∧
      c D.φ K G (s - 1) S =
        alpha D.φ (S - s).toNat * c D.φ K G s S + (1 - alpha D.φ (S - s).toNat) * G s := by
  have hm := zfs_m_nonneg D.φ D.nonneg hp0
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = (S - s).toNat := ⟨_, rfl⟩
  have hn1 : 1 ≤ n := by omega
  have hnZ : (n : ℤ) = S - s := by omega
  have hn2 : (S - (s - 1)).toNat = n + 1 := by omega
  have hM0 : 0 < M D.φ n := by
    unfold M
    have h0 : 0 < m D.φ 0 := by
      rw [m]; exact inv_pos.2 (by linarith)
    refine lt_of_lt_of_le h0 ?_
    exact Finset.single_le_sum (f := fun i => m D.φ i) (fun i _ => hm i)
      (Finset.mem_range.2 (by omega))
  have hMs : M D.φ (n + 1) = M D.φ n + m D.φ n := by
    unfold M; rw [Finset.sum_range_succ]
  have hmn := hm n
  rw [← hn]
  refine ⟨?_, ?_, ?_⟩
  · unfold alpha
    rw [hMs]
    exact div_pos hM0 (by linarith)
  · unfold alpha
    rw [hMs, div_le_one (by linarith)]
    linarith
  · unfold alpha c
    rw [hn2, ← hn, hMs, Finset.sum_range_succ]
    have hGs : G (S - (n : ℤ)) = G s := by rw [hnZ]; congr 1; ring
    rw [hGs]
    have hsub : S - (s - 1) = (n : ℤ) + 1 := by omega
    field_simp
    ring

theorem solution (D : VeinottWagnerSS.RenewalCost.DemandDist) (hp0 : D.φ 0 < 1)
    (K : ℝ) (hK : 0 < K) (G : ℤ → ℝ) (hG : NegUnimodal G) (hgrowth : GrowthCond K G)
    (s S : ℤ) (hsS : s < S) :
    (G s < c D.φ K G s S → G s < c D.φ K G (s - 1) S ∧ c D.φ K G (s - 1) S ≤ c D.φ K G s S) ∧
    (G s = c D.φ K G s S → G s = c D.φ K G (s - 1) S ∧ c D.φ K G (s - 1) S = c D.φ K G s S) ∧
    (G s > c D.φ K G s S → G s > c D.φ K G (s - 1) S ∧ c D.φ K G (s - 1) S ≥ c D.φ K G s S) ∧
    (G s < c D.φ K G (s - 1) S → c D.φ K G (s - 1) S ≤ c D.φ K G s S) ∧
    (G s = c D.φ K G (s - 1) S → c D.φ K G (s - 1) S = c D.φ K G s S) ∧
    (G s > c D.φ K G (s - 1) S → c D.φ K G (s - 1) S ≥ c D.φ K G s S) := by
  obtain ⟨hα, hα1, h⟩ := zfs_core D hp0 K G s S hsS
  generalize alpha D.φ (S - s).toNat = α at hα hα1 h
  generalize c D.φ K G (s - 1) S = cs1 at h ⊢
  generalize c D.φ K G s S = cs at h ⊢
  generalize G s = g at h ⊢
  have d1 : cs1 - g = α * (cs - g) := by rw [h]; ring
  have d2 : cs1 - cs = (1 - α) * (g - cs) := by rw [h]; ring
  have h1α : 0 ≤ 1 - α := by linarith
  refine ⟨fun hlt => ⟨?_, ?_⟩, fun heq => ⟨?_, ?_⟩, fun hgt => ⟨?_, ?_⟩, fun hlt => ?_,
    fun heq => ?_, fun hgt => ?_⟩
  · have := mul_pos hα (sub_pos.2 hlt); linarith
  · have := mul_nonneg h1α (sub_pos.2 hlt).le; nlinarith
  · have : cs1 - g = 0 := by rw [d1, heq]; ring
    linarith
  · have : cs1 - cs = 0 := by rw [d2, heq]; ring
    linarith
  · have := mul_pos hα (sub_pos.2 hgt); nlinarith
  · have := mul_nonneg h1α (sub_pos.2 hgt).le; linarith
  · have h1 : 0 < α * (cs - g) := by rw [← d1]; linarith
    have h2 : 0 < cs - g := (mul_pos_iff_of_pos_left hα).1 h1
    have := mul_nonneg h1α h2.le
    nlinarith
  · have h1 : α * (cs - g) = 0 := by rw [← d1]; linarith
    have h2 : cs - g = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · linarith
      · exact h
    nlinarith
  · have h1 : 0 < α * (g - cs) := by nlinarith
    have h2 : 0 < g - cs := (mul_pos_iff_of_pos_left hα).1 h1
    have := mul_nonneg h1α h2.le
    nlinarith
