-- Prove2me | solution 1 for PIW.ENSpec.gmap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:21:26.683162+00:00
-- url     : https://prove2.me/submissions/b2143755-1cf8-4f1c-9e94-1eac7b845465

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
variable {R : Type u} [CommRing R] {D : ℕ}
local notation "𝔛" => Ideal.span (Set.range (MvPolynomial.X : Fin D → MvPolynomial (Fin D) R))
namespace PIW.ENSpec
theorem _root_.solution (a : ℕ) : Function.Surjective (gmap (R := R) (D := D) a) :=
  Submodule.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ a))
end PIW.ENSpec
