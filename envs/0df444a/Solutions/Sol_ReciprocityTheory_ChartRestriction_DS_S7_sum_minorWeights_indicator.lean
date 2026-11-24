-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.sum_minorWeights_indicator
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:18.786362+00:00
-- url     : https://prove2.me/submissions/a62be618-2d99-431e-b8bb-fd8a24387bbb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CBinet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMomentsA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_sum_castLE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_entry
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_one_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_mass
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_lead_unitary_diag


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) {i : ℕ} (hi : i ≤ n)
    (k : Fin n) :
    ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * dmInd J.1 k = dmK U i k k := by
  have h := lead_unitary_diag (U := U) (fun j => if j = k then (2 : ℂ) else 1) i hi
  have hprod : ∀ J : Finset (Fin n), ∏ j ∈ J, (if j = k then (2 : ℂ) else 1) = 1 + dmInd J k := by
    intro J; rw [Finset.prod_ite_eq']; unfold dmInd; split_ifs <;> norm_num
  simp only [hprod, mul_add, mul_one, Finset.sum_add_distrib] at h
  have hm := dm_mass hU hi
  simp only [dmW] at hm ⊢
  rw [hm] at h
  let v : Fin i → ℂ := fun a => U (Fin.castLE hi a) k
  have hsub : (U * Matrix.diagonal (fun j => if j = k then (2 : ℂ) else 1) * Uᴴ).submatrix
      (Fin.castLE hi) (Fin.castLE hi) = 1 + Matrix.replicateCol Unit v * Matrix.replicateRow Unit (star v) := by
    ext a b
    rw [Matrix.submatrix_apply, dm_entry]
    have hj : ∀ j, U (Fin.castLE hi a) j * (if j = k then (2 : ℂ) else 1) * star (U (Fin.castLE hi b) j)
        = U (Fin.castLE hi a) j * star (U (Fin.castLE hi b) j) +
          if k = j then U (Fin.castLE hi a) k * star (U (Fin.castLE hi b) k) else 0 := by
      intro j
      by_cases hjk : j = k
      · subst hjk; simp; ring
      · rw [if_neg hjk, if_neg (Ne.symm hjk)]; ring
    simp only [hj, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, dm_unit hU, dm_one_sub]
    simp [Matrix.mul_apply, v]
  rw [lead, dif_pos hi, hsub, Matrix.det_one_add_replicateCol_mul_replicateRow] at h
  have hdot : star v ⬝ᵥ v = dmK U i k k := by
    rw [dotProduct, dmK, ← dm_sum_castLE hi (fun a => star (U a k) * U a k)]
    rfl
  rw [hdot] at h
  linear_combination -h
end ReciprocityTheory.ChartRestriction.DS.S7
