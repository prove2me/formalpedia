-- Prove2me | solution 1 for Reformulated.AutPerF.adicMap_adicMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:29:58.257697+00:00
-- url     : https://prove2.me/submissions/c5e98146-9b52-42e6-9795-cf5308d69f71

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
theorem _root_.solution (I : Ideal A) (J : Ideal B) (K : Ideal C) (f : A →+* B) (g : B →+* C)
    (e : A →+* C) (h : I ≤ J.comap f) (h' : J ≤ K.comap g) (h'' : I ≤ K.comap e)
    (he : ∀ a, g (f a) = e a) (x : AdicCompletion I A) :
    adicMap J K g h' (adicMap I J f h x) = adicMap I K e h'' x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_adicMap, evalₐ_adicMap, evalₐ_adicMap]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← ha, Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.quotientMap_mk, he]
end Reformulated.AutPerF
