-- Prove2me | solution 1 for PI.HookSteps.mulXAdj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:43:10.439643+00:00
-- url     : https://prove2.me/submissions/3dec0a7a-01da-4680-a347-2f44d478df30

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DeterminantAdjugate
import Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_cast
import Theorems.Thm_Formalism_REAL_fischerInner_X_mul_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.HookSteps
namespace PI.HookSteps
theorem _root_.solution : MulXAdj := by
  intro σ v f g
  classical
  apply (Rat.castHom ℂ).injective
  show ((fockQ (X v * f) g : ℚ) : ℂ) = ((fockQ f (pderiv v g) : ℚ) : ℂ)
  rw [lfockq_cast, lfockq_cast, map_mul, map_X, Formalism.REAL.fischerInner_X_mul_left, pderiv_map]
end PI.HookSteps
