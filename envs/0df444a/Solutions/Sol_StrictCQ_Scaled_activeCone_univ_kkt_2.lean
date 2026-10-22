-- Prove2me | solution 2 for StrictCQ.Scaled.activeCone_univ_kkt
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:21:08.773062+00:00
-- url     : https://prove2.me/submissions/00df82b2-02b5-4bc5-b82e-c48596adf3f1

import Mathlib
import Definitions.Def_StrictCQ_Scaled_Setting
import Definitions.Def_StrictCQ_Scaled_Conditions

set_option autoImplicit false
open Filter Topology
open scoped InnerProductSpace
open StrictCQ.Scaled

theorem solution {n m p : ℕ} (C : Constraints n m p)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ C.feasible)
    (hcone : C.activeCone xs = Set.univ) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    C.IsKKT f xs := by
  have : -gradient f xs ∈ C.activeCone xs := by rw [hcone]; exact Set.mem_univ _
  obtain ⟨lam, mu, hmu, hcomp, hw⟩ := this
  refine ⟨lam, mu, hmu, hcomp, ?_⟩
  have : gradient f xs + (∑ i, lam i • gradient (C.h i) xs + ∑ j, mu j • gradient (C.g j) xs) = 0 := by
    rw [← hw]; abel
  rw [← add_assoc] at this
  exact this
