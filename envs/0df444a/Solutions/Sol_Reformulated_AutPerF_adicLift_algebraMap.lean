-- Prove2me | solution 1 for Reformulated.AutPerF.adicLift_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:40:28.265288+00:00
-- url     : https://prove2.me/submissions/af533515-75dd-411e-a310-b1f44e9fb5dc

import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Envelope
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap
import Mathlib



-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal
open scoped Nat
open Reformulated Reformulated.AutPerF
variable {A Q : Type*} [CommRing A] [CommRing Q]
theorem _root_.solution (p : ℕ) [IsAdicComplete (span {(p : Q)}) Q] (g : A →+* Q) (a : A) :
    adicLift p g (algebraMap A _ a) = g a := by
  first
    | (intros; simp [adicLift])
    | (intros; unfold adicLift; simp)
    | (intros; simp [adicLift]; done)
    | (intros; ext; simp [adicLift])
    | (intros; simp only [adicLift]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [adicLift])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [adicLift])
    | (intros; unfold adicLift; split_ifs <;> simp_all)
    | (intros; unfold adicLift; positivity)
    | (intros; unfold adicLift; ring)
    | (intros; unfold adicLift; exact?)
    | (intros; aesop (add norm simp [adicLift]))
    | (intros; simp [adicLift] <;> aesop)
    | (intros; exact adicLift.symm ..)
    | (intros; exact adicLift.comm ..)
  trace "HIT_181_2"

end 
