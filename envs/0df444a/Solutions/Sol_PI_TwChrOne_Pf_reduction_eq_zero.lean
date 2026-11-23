-- Prove2me | solution 1 for PI.TwChrOne.Pf.reduction_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:30.027206+00:00
-- url     : https://prove2.me/submissions/15dec77f-0c7f-4898-a212-051713d0e5d0

import Definitions.Def_Formalism_PeriodIntegrals_TwChrOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedCharacterOne_IsIntegralAtSuperdiagonalSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwChrOne PI.TwChrOne.Pf
variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))
namespace PI.TwChrOne.Pf
theorem _root_.solution {a : E} {p r s : 𝓞 E} (hp : p ∈ P.asIdeal) (hs : s ∉ P.asIdeal)
    (h : algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E p * algebraMap (𝓞 E) E r) : redP P a = 0 :=
  redP_eq P (r := p * r) hs (by rw [map_mul]; exact h)
    (by rw [mul_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.mul_mem_right _ _ hp)
end PI.TwChrOne.Pf
