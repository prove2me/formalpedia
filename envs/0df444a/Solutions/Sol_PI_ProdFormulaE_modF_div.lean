-- Prove2me | solution 1 for PI.ProdFormulaE.modF_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:06:15.158149+00:00
-- url     : https://prove2.me/submissions/532489da-0852-45cc-bdc5-8506f50c0af3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormMod
import Theorems.Thm_PI_ProdFormulaE_modF_zero
import Theorems.Thm_PI_ProdFormulaE_modF_pos
import Theorems.Thm_PI_ProdFormulaE_modF_mul

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
theorem _root_.solution (a b : K) : modF K (a / b) = modF K a / modF K b := by
  by_cases hb : b = 0
  · subst hb; simp [modF_zero]
  have hm : modF K (a / b) * modF K b = modF K a := by
    rw [← modF_mul, div_mul_cancel₀ a hb]
  rw [eq_div_iff (modF_pos hb).ne']
  exact hm
end PI.ProdFormulaE
