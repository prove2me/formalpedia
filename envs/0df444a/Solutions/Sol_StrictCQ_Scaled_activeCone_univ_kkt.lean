-- Prove2me | solution 1 for StrictCQ.Scaled.activeCone_univ_kkt
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:19:11.629415+00:00
-- url     : https://prove2.me/submissions/6b8ec54b-a0c8-47ec-a1b6-73df3e7d3e78

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
  have : -gradient f xs ∈ C.activeCone xs := by rw [hcone]; trivial
  obtain ⟨lam, mu, hmu, hact, heq⟩ := this
  refine ⟨lam, mu, hmu, hact, ?_⟩
  rw [add_assoc, ← heq]
  abel
