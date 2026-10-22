-- Prove2me | solution 1 for ZhengFedergruenSS.Algorithm.eq6_weighted_average
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:59:43.36725+00:00
-- url     : https://prove2.me/submissions/0eecb39c-d713-4671-9327-5c66b72a073f

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
    0 < alpha D.φ (S - s).toNat ∧ alpha D.φ (S - s).toNat ≤ 1 ∧
      c D.φ K G (s - 1) S =
        alpha D.φ (S - s).toNat * c D.φ K G s S + (1 - alpha D.φ (S - s).toNat) * G s :=
  zfs_core D hp0 K G s S hsS
