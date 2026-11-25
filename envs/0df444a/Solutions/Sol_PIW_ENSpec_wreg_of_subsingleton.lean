-- Prove2me | solution 1 for PIW.ENSpec.wreg_of_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:25:50.761546+00:00
-- url     : https://prove2.me/submissions/73316555-7a83-4625-a3cf-5dbad8953e8e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_StSpecOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_WregOfSubsingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open PIW PIW.ENSpec
open MvPolynomial RingTheory.Sequence
open scoped Pointwise
variable {S : Type u} [CommRing S]
namespace PIW.ENSpec
theorem _root_.solution {M : Type v} [AddCommGroup M] [Module S M] [Subsingleton M] (rs : List S) :
    IsWeaklyRegular M rs := by
  refine (isWeaklyRegular_iff M rs).2 fun i _ => ?_
  intro a b _
  induction a using Submodule.Quotient.induction_on
  induction b using Submodule.Quotient.induction_on
  exact congrArg _ (Subsingleton.elim _ _)
end PIW.ENSpec
