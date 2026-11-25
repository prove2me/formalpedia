-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.lu_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:43:23.671714+00:00
-- url     : https://prove2.me/submissions/62698fc9-0f8c-4787-9e2d-737984b99efb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
import Definitions.Def_Lemmata_GeneralBFactForm_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_inv_blockTriangular
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_det_lowerUni
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_lminor_last__5f96f668a500

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution {M : Matrix (Fin n) (Fin n) ℂ} (hM : ∀ i : Fin (n + 1), lminor M i ≠ 0) :
    ∃ N U : Matrix (Fin n) (Fin n) ℂ, N.BlockTriangular OrderDual.toDual ∧ (∀ a, N a a = 1) ∧
      U.BlockTriangular id ∧ U.det ≠ 0 ∧ N * U = M := by
  classical
  let A : ∀ r : Fin n, Matrix (Fin r) (Fin r) ℂ := fun r =>
    M.submatrix (Fin.castLE r.isLt.le) (Fin.castLE r.isLt.le)
  have hA : ∀ r : Fin n, IsUnit (A r).det := fun r => isUnit_iff_ne_zero.mpr (hM r.castSucc)
  let x : ∀ r : Fin n, Fin r → ℂ := fun r =>
    -((fun j => M r (Fin.castLE r.isLt.le j)) ᵥ* (A r)⁻¹)
  have hx : ∀ r : Fin n, ∀ j : Fin r,
      ∑ i : Fin r, x r i * M (Fin.castLE r.isLt.le i) (Fin.castLE r.isLt.le j) =
        -M r (Fin.castLE r.isLt.le j) := by
    intro r j
    have hv : x r ᵥ* A r = -(fun j => M r (Fin.castLE r.isLt.le j)) := by
      simp only [x, Matrix.neg_vecMul, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (hA r),
        Matrix.vecMul_one]
    have h := congrFun hv j
    simpa [Matrix.vecMul, dotProduct, A] using h

  let L : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun r c =>
    if h : c < r then x r ⟨c, h⟩ else if c = r then 1 else 0
  have hLlow : L.BlockTriangular OrderDual.toDual := by
    intro r c hrc
    have hrc' : r < c := OrderDual.toDual_lt_toDual.mp hrc
    simp [L, not_lt.mpr hrc'.le, hrc'.ne']
  have hL1 : ∀ a, L a a = 1 := fun a => by simp [L]
  have hLdet : L.det = 1 := det_lowerUni hLlow hL1
  have hLu : IsUnit L.det := by rw [hLdet]; exact isUnit_one
  have hrow : ∀ r c : Fin n, c < r → (L * M) r c = 0 := by
    intro r c hcr
    have e1 : ∀ k, L r k * M k c =
        (if h : k < r then x r ⟨k, h⟩ * M k c else 0) + (if k = r then M k c else 0) := by
      intro k
      by_cases h : k < r
      · simp [L, h, h.ne]
      · by_cases h' : k = r
        · subst h'
          simp [L]
        · simp [L, h, h']
    have hsub : ∑ k : Fin n, (if h : k < r then x r ⟨k, h⟩ * M k c else 0) =
        ∑ j : Fin r, x r j * M (Fin.castLE r.isLt.le j) c := by
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map (Fin.castLEEmb r.isLt.le)))]
      · rw [Finset.sum_map]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hj : (Fin.castLEEmb r.isLt.le j) < r := by
          show (j : ℕ) < r
          exact j.isLt
        rw [dif_pos hj]
        rfl
      · intro k _ hk
        have hk' : ¬ k < r := by
          intro h
          apply hk
          exact Finset.mem_map.mpr ⟨⟨k, h⟩, Finset.mem_univ _, Fin.ext rfl⟩
        rw [dif_neg hk']
    rw [Matrix.mul_apply, Finset.sum_congr rfl fun k _ => e1 k, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ r (fun k => M k c), if_pos (Finset.mem_univ _), hsub]
    have h := hx r ⟨c, hcr⟩
    have hc : Fin.castLE r.isLt.le (⟨c, hcr⟩ : Fin r) = c := Fin.ext rfl
    rw [hc] at h
    rw [h]
    ring
  refine ⟨L⁻¹, L * M, inv_blockTriangular hLlow (by rw [hLdet]; exact one_ne_zero), ?_, ?_, ?_, ?_⟩
  · intro a
    have h1 : (L * L⁻¹) a a = 1 := by
      rw [Matrix.mul_nonsing_inv L hLu]
      simp
    rw [Matrix.mul_apply, Finset.sum_eq_single a] at h1
    · rwa [hL1, one_mul] at h1
    · intro k _ hka
      rcases lt_or_gt_of_ne hka with h | h
      · have h0 : L⁻¹ k a = 0 := inv_blockTriangular hLlow (by rw [hLdet]; exact one_ne_zero)
          (OrderDual.toDual_lt_toDual.mpr h)
        rw [h0, mul_zero]
      · have h0 : L a k = 0 := hLlow (OrderDual.toDual_lt_toDual.mpr h)
        rw [h0, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  · intro r c hcr
    exact hrow r c hcr
  · rw [Matrix.det_mul, hLdet, one_mul, ← lminor_last']
    exact hM _
  · rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul L hLu, Matrix.one_mul]
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
