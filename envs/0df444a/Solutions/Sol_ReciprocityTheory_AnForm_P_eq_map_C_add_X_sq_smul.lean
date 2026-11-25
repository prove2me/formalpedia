-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.eq_map_C_add_X_sq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:35.313963+00:00
-- url     : https://prove2.me/submissions/0609175d-f38b-44ff-9091-ecd94b1c211f

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Theorems.Thm_ReciprocityTheory_AnForm_P_eq_X_sq_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open Filter Topology Polynomial Matrix
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution {n : Type*} (P : Matrix n n ℂ[X]) (h1 : cf 1 P = 0) :
    P = (cf 0 P).map C + (X ^ 2 : ℂ[X]) • (P - (cf 0 P).map C).map (fun q => q.divX.divX) := by
  ext i j
  have h1' : (P i j).coeff 1 = 0 := by
    have := congrFun (congrFun h1 i) j
    simpa [cf] using this
  have hq0 : (P i j - C ((P i j).coeff 0)).coeff 0 = 0 := by simp
  have hq1 : (P i j - C ((P i j).coeff 0)).coeff 1 = 0 := by simp [h1', Polynomial.coeff_C]
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, cf]
  rw [← eq_X_sq_mul _ hq0 hq1]
  ring
end ReciprocityTheory.AnForm.P
