-- Prove2me | solution 1 for ProximityPrize.SubmissionUpper.HalfRadiusCollision.dot_zero_fiber_card_mul
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-27T04:35:30.657383+00:00
-- url     : https://prove2.me/submissions/d6fa8e3f-e61c-4744-a6f0-60c3956c92c2

import Mathlib
import Init
import Definitions.Def_ProximityPrize_SubmissionUpper_HalfRadiusCollision_dot
import Theorems.Thm_ProximityPrize_SubmissionUpper_HalfRadiusCollision_dot_surjective
namespace ProximityPrize.SubmissionUpper.HalfRadiusCollision

open scoped BigOperators

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]







lemma _root_.solution {k : ℕ} {d : Fin k → F} (hd : d ≠ 0) :
    ((Finset.univ.filter fun v : Fin k → F => dot d v = 0).card) * Fintype.card F =
      Fintype.card (Fin k → F) := (by
  classical
  let φ : (Fin k → F) →+ F :=
    { toFun := dot d
      map_zero' := by simp [dot]
      map_add' := by
        intro x y
        simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib] }
  have hsurj : Function.Surjective φ := dot_surjective hd
  let K := (Finset.univ.filter fun v : Fin k → F => φ v = 0).card
  have hfiber (y : F) :
      (Finset.univ.filter fun v : Fin k → F => φ v = y).card = K := by
    exact AddMonoidHom.card_fiber_eq_of_mem_range φ (hsurj y) (hsurj 0)
  have hsum : Fintype.card (Fin k → F) =
      ∑ y : F, (Finset.univ.filter fun v : Fin k → F => φ v = y).card := by
    rw [← Finset.card_univ]
    simpa using (Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin k → F)))
      (t := (Finset.univ : Finset F)) (f := φ)
      (fun _ _ => Finset.mem_univ _))
  rw [hsum]
  simp_rw [hfiber]
  simp [K, φ, Nat.mul_comm]
  rfl
)
end HalfRadiusCollision
end SubmissionUpper
end ProximityPrize
