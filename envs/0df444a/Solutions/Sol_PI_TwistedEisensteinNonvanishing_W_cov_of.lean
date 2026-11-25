-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.cov_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:53:11.566299+00:00
-- url     : https://prove2.me/submissions/1b00a205-c810-4683-9272-10aacac08909

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumToGaussSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_ChangeVariablesDeterminantOne
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qt_aff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE Function Matrix
variable {E K : Type} [Field E] [NumberField E] [Field K]
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution (hN : NTAll) : CoVP := by
  intro E K _ _ _ P hp hq hK ι _ _ L τ
  exact ⟨(qOf P : K) ^ vq P (LinearMap.det (L : (ι → E) →ₗ[E] (ι → E))), zpow_ne_zero _ hK,
    qt_aff hN hp hq hK L τ⟩
end PI.TwistedEisensteinNonvanishing.W
