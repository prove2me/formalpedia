-- Prove2me | solution 1 for PI.NcVal.OmVc1.gramMulTup_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:34:25.024682+00:00
-- url     : https://prove2.me/submissions/85a434b6-e767-4f95-a198-53a523213c2e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_AddEquivAddHaarCharEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_GramMulTupHolds
import Theorems.Thm_PI_NcVal_OmVc1_gram_entry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.NcVal PI.NcVal.OmVc1
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.DegenerateSiegelWeil.Scale
open scoped TensorProduct
namespace PI.NcVal.OmVc1
theorem _root_.solution : GramMulTup := by
  intro F E _ _ _ R _ _ σ n M J D X
  ext a b
  exact gram_entry R σ n M J D X a b
end PI.NcVal.OmVc1
