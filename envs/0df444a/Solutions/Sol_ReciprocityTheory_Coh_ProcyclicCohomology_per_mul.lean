-- Prove2me | solution 1 for ReciprocityTheory.Coh.ProcyclicCohomology.per_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:43.89589+00:00
-- url     : https://prove2.me/submissions/5227af51-d50a-4a7e-bf27-757c17ae7fb6

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_MemZpowersQuot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Coh.ProcyclicCohomology
open Topology
open scoped Pointwise
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {s : G}
variable {X : Type*} (n : ℕ) (T : ℕ → X)
namespace ReciprocityTheory.Coh.ProcyclicCohomology
theorem _root_.solution (hper : ∀ j, T (j + n) = T j) (a t : ℕ) : T (a + n * t) = T a := by
  induction t with
  | zero => simp
  | succ t ih => rw [Nat.mul_succ, ← Nat.add_assoc, hper, ih]
end ReciprocityTheory.Coh.ProcyclicCohomology
