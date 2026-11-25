-- Prove2me | solution 1 for PI.AlgValsFin.W.algValsFin_of_tors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:22:34.991803+00:00
-- url     : https://prove2.me/submissions/44376c94-0f31-496a-bccf-f8acd5cde44f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_OrdFEqOfClassOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_FinprodNormEmbedding
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_EvFLocalIdeleSelf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_FactorOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_IsIntegralOfMemCompo
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_AlgValsFinOfTors
import Theorems.Thm_PI_AlgValsFin_W_assemble
import Theorems.Thm_PI_AlgValsFin_W_classPow
import Theorems.Thm_PI_AlgValsFin_W_classSame
import Theorems.Thm_PI_AlgValsFin_W_decomp
import Theorems.Thm_PI_AlgValsFin_W_keyIdOf
import Theorems.Thm_PI_AlgValsFin_W_locVal
import Theorems.Thm_PI_AlgValsFin_W_prodNorm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AlgValsFin PI.AlgValsFin.W
namespace PI.AlgValsFin.W
theorem _root_.solution (L : Type) [Field L] [NumberField L] (hT : TorsUnits L) : AlgValsFin L :=
  assemble hT (keyIdOf decomp locVal prodNorm) classPow classSame
end PI.AlgValsFin.W
