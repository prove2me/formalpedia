-- Prove2me | solution 1 for ReciprocityTheory.Coh.ProcyclicCohomology.per_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:47:57.14521+00:00
-- url     : https://prove2.me/submissions/b81b6557-6703-4186-9a0b-d45ef9efd753

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_MemZpowersQuot
import Theorems.Thm_ReciprocityTheory_Coh_ProcyclicCohomology_per_mul

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
theorem _root_.solution (hper : ∀ j, T (j + n) = T j) (a b : ℕ) (h : (n : ℤ) ∣ (b : ℤ) - a) :
    T a = T b := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg c
  · have h1 : ((b : ℕ) : ℤ) = ((a + n * m : ℕ) : ℤ) := by push_cast; linarith
    have h2 : b = a + n * m := by exact_mod_cast h1
    rw [h2, per_mul n T hper]
  · rw [mul_neg] at hc
    have h1 : ((a : ℕ) : ℤ) = ((b + n * m : ℕ) : ℤ) := by push_cast; linarith
    have h2 : a = b + n * m := by exact_mod_cast h1
    rw [h2, per_mul n T hper]
end ReciprocityTheory.Coh.ProcyclicCohomology
