-- Prove2me | solution 1 for P2M_GroundTheory_Arith_SchemeCoh_eqLocusLift___492cd423a1bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:52:24.486394+00:00
-- url     : https://prove2.me/submissions/68a63458-7cfb-4dd7-8ba9-0079275d0b79

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_SchemeImage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry CategoryTheory Limits
universe u
noncomputable section
variable {T S B : Scheme.{u}} (p : S ⟶ B) [IsSeparated p] (g h : T ⟶ S) (hgh : g ≫ p = h ≫ p)
omit [IsSeparated p]
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {V : Scheme.{u}} (t : V ⟶ T) (ht : t ≫ g = t ≫ h) :
    eqLocusLift p g h hgh t ht ≫ eqLocusι p g h hgh = t :=
  pullback.lift_snd _ _ _
end GroundTheory.Arith.SchemeCoh
