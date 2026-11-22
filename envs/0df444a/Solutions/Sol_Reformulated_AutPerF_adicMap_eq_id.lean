-- Prove2me | solution 1 for Reformulated.AutPerF.adicMap_eq_id
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:29:58.180919+00:00
-- url     : https://prove2.me/submissions/a984a666-d2f2-4b04-a0ac-0b60572435b6

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_SpanNatCastLeComap

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
open Reformulated Reformulated.AutPerF
universe u v w
variable {A : Type u} {B : Type v} {C : Type w} [CommRing A] [CommRing B] [CommRing C]
namespace Reformulated.AutPerF
theorem _root_.solution (I : Ideal A) (f : A →+* A) (h : I ≤ I.comap f) (hf : ∀ a, f a = a)
    (x : AdicCompletion I A) : adicMap I I f h x = x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_adicMap]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← ha, Ideal.quotientMap_mk, hf]
end Reformulated.AutPerF
