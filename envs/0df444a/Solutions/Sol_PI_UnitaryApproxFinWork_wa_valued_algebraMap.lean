-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.wa_valued_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:44:09.027383+00:00
-- url     : https://prove2.me/submissions/fe9bb272-b54d-45f2-ba15-8b3553f03702

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproxF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproximationFiniteUnitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open PI PI.UnitaryApproxFinWork
variable {F : Type} [Field F] [NumberField F]
namespace PI.UnitaryApproxFinWork
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (k : F) :
    Valued.v (algebraMap F (v.adicCompletion F) k) = v.valuation F k := by
  first
    | exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
    | simpa using IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
    | rfl
end PI.UnitaryApproxFinWork
