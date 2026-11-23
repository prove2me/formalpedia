-- Prove2me | solution 1 for PI.ProdFormulaE.modF_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:10.896635+00:00
-- url     : https://prove2.me/submissions/69d288ae-6d23-4fd2-a41d-b4c12b664254

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormMod
import Theorems.Thm_PI_ProdFormulaE_modF_zero
import Theorems.Thm_PI_ProdFormulaE_modF_of_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel
open PI PI.ProdFormulaE
variable {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
namespace PI.ProdFormulaE
theorem _root_.solution (a b : K) : modF K (a * b) = modF K a * modF K b := by
  by_cases ha : a = 0
  · subst ha; simp [modF_zero]
  by_cases hb : b = 0
  · subst hb; simp [modF_zero]
  rw [modF_of_ne (mul_ne_zero ha hb), modF_of_ne ha, modF_of_ne hb]
  have hu : Units.mk0 (a * b) (mul_ne_zero ha hb) = Units.mk0 a ha * Units.mk0 b hb := by
    ext; simp
  rw [hu, map_mul, NNReal.coe_mul]
end PI.ProdFormulaE
