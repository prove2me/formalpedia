-- Prove2me | solution 1 for ThreeSum.TernaryProjectionCells.collision_classification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:35:56.591058+00:00
-- url     : https://prove2.me/submissions/c9d45a7c-c35b-4bf4-aff7-4cf3fa18a146

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryProjectionCells
import Theorems.Thm_ThreeSum_TernaryProjectionCells_generic_projection_injective

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
open ThreeSum ThreeSum.TernaryProjectionCells
variable {K : Type*} [Field K]
namespace ThreeSum.TernaryProjectionCells
theorem _root_.solution {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    {i j : Fin 6} (hij : i ≠ j) (h : projectedCell a b i = projectedCell a b j) :
    a+b = 0 ∨ a = b ∨ 2*a = b ∨ a = 2*b := by
  by_contra hn
  push_neg at hn
  exact hij (generic_projection_injective ha hb h2 hn.1 hn.2.1 hn.2.2.1 hn.2.2.2 h)
end ThreeSum.TernaryProjectionCells
