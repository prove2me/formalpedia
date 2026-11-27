-- Prove2me | solution 1 for P2M_GlobalTheory_SpecialConn_thickTr___82a49f0dd690
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:52:10.016389+00:00
-- url     : https://prove2.me/submissions/bcbe702e-2880-47e3-ba06-a9cfba8481f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ThickFibIsPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.SpecialConn
variable {O : Type} [CommRing O] [IsLocalRing O] {Y : Scheme.{0}} (f : Y ⟶ Spec (.of O))
namespace GlobalTheory.SpecialConn
theorem _root_.solution (n : ℕ) : thickTr f n ≫ thickι f (n + 1) = thickι f n :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)
end GlobalTheory.SpecialConn
