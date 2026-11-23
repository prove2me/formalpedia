-- Prove2me | solution 1 for PI.ProdFormulaE.modF_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:27:52.540388+00:00
-- url     : https://prove2.me/submissions/55678b2d-b27a-4809-ac33-9f2845755c5c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormMod
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
theorem _root_.solution {a : K} (h : a ≠ 0) : 0 < modF K a := by
  rw [modF_of_ne h]
  have hu : IsUnit (distribHaarChar K (Units.mk0 a h)) := (Group.isUnit (Units.mk0 a h)).map (distribHaarChar K)
  exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hu.ne_zero)
end PI.ProdFormulaE
