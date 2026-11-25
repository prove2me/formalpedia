-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.det_coeff_zero_one_of_coeffMatrix_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:28:07.815901+00:00
-- url     : https://prove2.me/submissions/86cd938d-105d-46d0-9ac6-6a3e35ebcfc4

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_IsRegFamilyInhabitStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Theorems.Thm_ReciprocityTheory_AnForm_P_det_map_C_add_X_sq_smul
import Theorems.Thm_ReciprocityTheory_AnForm_P_eq_map_C_add_X_sq_smul

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
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ[X])
    (h1 : cf 1 P = 0) : P.det.coeff 0 = (cf 0 P).det ∧ P.det.coeff 1 = 0 := by
  obtain ⟨r, hr⟩ := det_map_C_add_X_sq_smul (cf 0 P) ((P - (cf 0 P).map C).map fun q => q.divX.divX)
  rw [← eq_map_C_add_X_sq_smul P h1] at hr
  rw [hr]
  constructor
  · simp [Polynomial.coeff_X_pow_mul']
  · simp [Polynomial.coeff_X_pow_mul', Polynomial.coeff_C]
end ReciprocityTheory.AnForm.P
