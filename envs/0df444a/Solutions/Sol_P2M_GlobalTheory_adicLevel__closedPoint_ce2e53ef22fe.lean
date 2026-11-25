-- Prove2me | solution 1 for P2M_GlobalTheory_adicLevel__closedPoint_ce2e53ef22fe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:06:12.496798+00:00
-- url     : https://prove2.me/submissions/62ec321f-ad15-462d-92d0-69e82bcc76b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {R : Type u} [CommRing R] (I : Ideal R)
variable {I}
variable [IsLocalRing R]
namespace GlobalTheory
theorem _root_.solution (hI : I ≠ ⊤) (n : ℕ) :
    haveI := isLocalRing_quotient_pow hI n
    adicLevelι I (n + 1) (closedPoint (R ⧸ I ^ (n + 1))) = closedPoint R := by
  have := isLocalRing_quotient_pow hI n
  have : IsLocalHom (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))).hom :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  exact Spec_closedPoint
end GlobalTheory
