-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.dm_mass
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:07.332843+00:00
-- url     : https://prove2.me/submissions/3e8fd2f5-77de-49a7-9975-b8bb94b32a53

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CBinet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMomentsA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_UUh
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_one_sub
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
theorem _root_.solution {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) {i : ℕ} (hi : i ≤ n) :
    ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) = 1 := by
  have h := lead_unitary_diag (U := U) (fun _ => (1 : ℂ)) i hi
  simp only [Finset.prod_const_one, mul_one] at h
  simp only [dmW]
  rw [← h, lead, dif_pos hi, Matrix.diagonal_one, Matrix.mul_one, dm_UUh hU]
  have h2 : (1 : Matrix (Fin n) (Fin n) ℂ).submatrix (Fin.castLE hi) (Fin.castLE hi) = 1 := by
    ext a b; rw [Matrix.submatrix_apply, dm_one_sub]
  rw [h2, Matrix.det_one]
end ReciprocityTheory.ChartRestriction.DS.S7
