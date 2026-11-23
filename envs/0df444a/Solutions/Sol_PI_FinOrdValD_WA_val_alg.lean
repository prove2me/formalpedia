-- Prove2me | solution 1 for PI.FinOrdValD.WA.val_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:59:27.996705+00:00
-- url     : https://prove2.me/submissions/9f0e91aa-dda1-470c-b316-d733f1a2a15c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderValuation_WeakApprox

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open PI PI.FinOrdValD PI.FinOrdValD.WA
variable {L : Type*} [Field L] [NumberField L]
namespace PI.FinOrdValD.WA
theorem _root_.solution (v : HeightOneSpectrum (𝓞 L)) (a : L) :
    Valued.v (algebraMap L (v.adicCompletion L) a) = v.valuation L a := by
  first
  | exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a
  | exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation v a
  | simp
end PI.FinOrdValD.WA
