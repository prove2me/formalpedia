-- Prove2me | solution 1 for PI.ProdFormulaE.modF_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:06:18.991388+00:00
-- url     : https://prove2.me/submissions/2015caef-5486-498c-b20b-985be042decb

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
theorem _root_.solution : modF K 1 = 1 := by
  rw [modF_of_ne one_ne_zero]
  have hu : Units.mk0 (1 : K) one_ne_zero = 1 := by
    ext; simp
  rw [hu, map_one, NNReal.coe_one]
end PI.ProdFormulaE
