-- Prove2me | solution 1 for ProximityPrize.SubmissionUpper.HalfRadiusCollision.dot_surjective
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-27T04:31:53.950877+00:00
-- url     : https://prove2.me/submissions/a30cd055-7cbe-4b34-b786-2451166854d4

import Mathlib
import Init
import Definitions.Def_ProximityPrize_SubmissionUpper_HalfRadiusCollision_dot
namespace ProximityPrize.SubmissionUpper.HalfRadiusCollision

open scoped BigOperators

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]




omit [Fintype F] [DecidableEq F] in
lemma _root_.solution {k : ℕ} {d : Fin k → F} (hd : d ≠ 0) :
    Function.Surjective (dot d) := by
  obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by
    simpa only [ne_eq, Pi.zero_apply, Function.ne_iff] using hd
  intro y
  let v : Fin k → F := fun i => if i = j then (d j)⁻¹ * y else 0
  refine ⟨v, ?_⟩
  simp only [dot, v]
  rw [Finset.sum_eq_single j]
  · simp [hj]
  · intro b _ hbj
    simp [hbj]
  · simp
end HalfRadiusCollision
end SubmissionUpper
end ProximityPrize
