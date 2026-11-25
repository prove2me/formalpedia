-- Prove2me | solution 1 for PIW.ENSpec.emb_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:35:15.062202+00:00
-- url     : https://prove2.me/submissions/162248fd-f723-4820-add3-1c2527f40196

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_StSpecOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_WregOfSubsingleton
import Theorems.Thm_PIW_ENSpec_homog_mem_pow_succ

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
theorem _root_.solution (a : ℕ) : Function.Injective (emb (R := R) (D := D) a) := by
  refine (injective_iff_map_eq_zero _).2 fun h hh => ?_
  have h1 : (Submodule.Quotient.mk h.1 : MvPolynomial (Fin D) R ⧸ 𝔛 ^ (a + 1)) = 0 :=
    congrArg Subtype.val hh
  rw [Submodule.Quotient.mk_eq_zero] at h1
  exact Subtype.ext (homog_mem_pow_succ h.2 h1)
end PIW.ENSpec
