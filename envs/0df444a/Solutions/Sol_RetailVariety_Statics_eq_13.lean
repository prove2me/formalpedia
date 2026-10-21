-- Prove2me | solution 1 for RetailVariety.Statics.eq_13
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:24:13.118001+00:00
-- url     : https://prove2.me/submissions/2f1a3a06-c6bb-4cd9-8f23-3d2ce03251ae

import Mathlib
import Definitions.Def_RetailVariety_Statics_Model
set_option autoImplicit false
open Filter Topology
open RetailVariety.Statics

theorem A_succ (n i : ℕ) (hin : i < n) :
    A n (i + 1) = insert ⟨i, hin⟩ (A n i) := by
  ext j
  simp only [A, RetailVariety.Structure.popularSet, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Fin.ext_iff]
  omega

theorem sum_share (n : ℕ) (v : Fin n → ℝ) (v0 : ℝ) (S : Finset (Fin n)) :
    ∑ j ∈ S, RetailVariety.Structure.share v v0 S j = (∑ j ∈ S, v j) / (∑ j ∈ S, v j + v0) := by
  unfold RetailVariety.Structure.share
  rw [Finset.sum_div]

theorem alg (P K R T T' Tb Tb' : ℝ) (hK : 0 < K) (hKR : K * R = P) (hY : 0 < T' - T) :
    (P * T - K * Tb ≤ P * T' - K * Tb' ↔ (Tb' - Tb) / (T' - T) ≤ R) ∧
    (P * T - K * Tb < P * T' - K * Tb' ↔ (Tb' - Tb) / (T' - T) < R) := by
  have h : P * T' - K * Tb' - (P * T - K * Tb) = K * (R * (T' - T) - (Tb' - Tb)) := by
    rw [← hKR]; ring
  constructor
  · rw [div_le_iff₀ hY, ← sub_nonneg (a := P * T' - K * Tb') (b := P * T - K * Tb), h,
      mul_nonneg_iff_of_pos_left hK, sub_nonneg]
  · rw [div_lt_iff₀ hY, ← sub_pos (a := P * T' - K * Tb') (b := P * T - K * Tb), h,
      mul_pos_iff_of_pos_left hK, sub_pos]

theorem solution (n i : ℕ) (hi : 1 ≤ i) (hin : i < n) (v : Fin n → ℝ) (hv : ∀ j, 0 < v j)
    (v0 : ℝ) (hv0 : 0 < v0) (p c lam σ β : ℝ) (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam)
    (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    (RetailVariety.Structure.profitI p c lam σ β v v0 (A n i) ≤ RetailVariety.Structure.profitI p c lam σ β v v0 (A n (i + 1)) ↔
      (∑ j ∈ A n (i + 1), RetailVariety.Structure.share v v0 (A n (i + 1)) j ^ β - ∑ j ∈ A n i, RetailVariety.Structure.share v v0 (A n i) j ^ β)
          / (∑ j ∈ A n (i + 1), RetailVariety.Structure.share v v0 (A n (i + 1)) j - ∑ j ∈ A n i, RetailVariety.Structure.share v v0 (A n i) j)
        ≤ (1 - c / p) * (Real.sqrt (2 * Real.pi) / σ) * lam ^ (1 - β)
            * Real.exp (criticalFractile p c ^ 2 / 2)) ∧
    (RetailVariety.Structure.profitI p c lam σ β v v0 (A n i) < RetailVariety.Structure.profitI p c lam σ β v v0 (A n (i + 1)) ↔
      (∑ j ∈ A n (i + 1), RetailVariety.Structure.share v v0 (A n (i + 1)) j ^ β - ∑ j ∈ A n i, RetailVariety.Structure.share v v0 (A n i) j ^ β)
          / (∑ j ∈ A n (i + 1), RetailVariety.Structure.share v v0 (A n (i + 1)) j - ∑ j ∈ A n i, RetailVariety.Structure.share v v0 (A n i) j)
        < (1 - c / p) * (Real.sqrt (2 * Real.pi) / σ) * lam ^ (1 - β)
            * Real.exp (criticalFractile p c ^ 2 / 2)) := by
  have hp : 0 < p := by linarith
  set z := criticalFractile p c with hz
  set S := A n i with hS
  set S' := A n (i + 1) with hS'
  set T := ∑ j ∈ S, RetailVariety.Structure.share v v0 S j with hT
  set T' := ∑ j ∈ S', RetailVariety.Structure.share v v0 S' j with hT'
  set Tb := ∑ j ∈ S, RetailVariety.Structure.share v v0 S j ^ β with hTb
  set Tb' := ∑ j ∈ S', RetailVariety.Structure.share v v0 S' j ^ β with hTb'
  set K : ℝ := p * σ * lam ^ β * Real.exp (-z ^ 2 / 2) / Real.sqrt (2 * Real.pi) with hK
  set R : ℝ := (1 - c / p) * (Real.sqrt (2 * Real.pi) / σ) * lam ^ (1 - β) * Real.exp (z ^ 2 / 2) with hR
  have hsq : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hlb : 0 < lam ^ β := Real.rpow_pos_of_pos hlam β
  have hKpos : 0 < K := by positivity
  have hKR : K * R = (p - c) * lam := by
    have h1 : lam ^ (1 - β) = lam / lam ^ β := by
      rw [Real.rpow_sub hlam, Real.rpow_one]
    have h2 : Real.exp (-z ^ 2 / 2) * Real.exp (z ^ 2 / 2) = 1 := by
      rw [← Real.exp_add, show -z ^ 2 / 2 + z ^ 2 / 2 = 0 by ring]; simp
    have e1 : K * R = (p * (1 - c / p)) * lam * (lam ^ β / lam ^ β) * (σ / σ)
        * (Real.sqrt (2 * Real.pi) / Real.sqrt (2 * Real.pi))
        * (Real.exp (-z ^ 2 / 2) * Real.exp (z ^ 2 / 2)) := by
      rw [hK, hR, h1]; ring
    rw [e1, h2, div_self hlb.ne', div_self hσ.ne', div_self hsq.ne']
    field_simp
  -- positivity of Y = T' - T
  have hY : 0 < T' - T := by
    have hmem : (⟨i, hin⟩ : Fin n) ∉ S := by
      simp [hS, A, RetailVariety.Structure.popularSet]
    have hV' : ∑ j ∈ S', v j = ∑ j ∈ S, v j + v ⟨i, hin⟩ := by
      rw [hS', A_succ n i hin, Finset.sum_insert hmem]; ring
    have hV0 : 0 ≤ ∑ j ∈ S, v j := Finset.sum_nonneg (fun j _ => (hv j).le)
    have hvi := hv ⟨i, hin⟩
    rw [hT, hT', sum_share, sum_share, hV']
    set V := ∑ j ∈ S, v j
    set vi := v ⟨i, hin⟩
    have h1 : 0 < V + v0 := by linarith
    have h2 : 0 < V + vi + v0 := by linarith
    rw [div_sub_div _ _ h2.ne' h1.ne']
    apply div_pos _ (mul_pos h2 h1)
    nlinarith
  exact alg ((p - c) * lam) K R T T' Tb Tb' hKpos hKR hY
