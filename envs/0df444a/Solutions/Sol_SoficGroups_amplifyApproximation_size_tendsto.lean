-- Prove2me | solution 1 for SoficGroups.amplifyApproximation_size_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/76670788-32ed-4d16-bd69-36704bf303c1

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {G : Type*} [Group G] (A : SoficApproximation G) :
    Tendsto (fun n => (amplifyApproximation A).model n |>.size)
      atTop atTop := by
  apply tendsto_atTop_mono (f := fun n : ℕ => n + 1)
    (g := fun n => (amplifyApproximation A).model n |>.size)
  · intro n
    change n + 1 ≤ (n + 1) * (A.model n).size
    exact Nat.le_mul_of_pos_right _ (A.model n).size_pos
  · exact tendsto_add_atTop_nat 1
end SoficGroups
