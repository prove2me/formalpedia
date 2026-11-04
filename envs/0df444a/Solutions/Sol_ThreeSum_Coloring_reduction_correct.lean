-- Prove2me | solution 1 for ThreeSum.Coloring.reduction_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:22:54.630742+00:00
-- url     : https://prove2.me/submissions/4d699147-48ae-4be3-a385-09e7b7964c8c

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Image
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Coloring
import Theorems.Thm_ThreeSum_Coloring_family_separates
import Theorems.Thm_ThreeSum_Coloring_mem_values
import Theorems.Thm_ThreeSum_Coloring_mem_negValues

set_option autoImplicit false
open ThreeSum ThreeSum.Coloring
variable {α : Type*}
namespace ThreeSum.Coloring
theorem _root_.solution {n : ℕ} (x : Fin n → ℤ) :
    DistinctZeroSum x ↔ ∃ c ∈ family n,
      ThreeSetWitness (values x c 0) (values x c 1) (negValues x c) := by
  constructor
  · rintro ⟨i, j, k, hij, hik, hjk, hsum⟩
    obtain ⟨c, hc, hi, hj, hk⟩ := family_separates hij hik hjk
    refine ⟨c, hc, x i, (mem_values x c 0 _).mpr ⟨i, hi, rfl⟩,
      x j, (mem_values x c 1 _).mpr ⟨j, hj, rfl⟩,
      -x k, (mem_negValues x c _).mpr ⟨k, hk, rfl⟩, ?_⟩
    omega
  · rintro ⟨c, _, a, ha, b, hb, z, hz, he⟩
    obtain ⟨i, hi, rfl⟩ := (mem_values x c 0 a).mp ha
    obtain ⟨j, hj, rfl⟩ := (mem_values x c 1 b).mp hb
    obtain ⟨k, hk, rfl⟩ := (mem_negValues x c z).mp hz
    refine ⟨i, j, k, ?_, ?_, ?_, by omega⟩
    · intro heq
      subst j
      simp_all
    · intro heq
      subst k
      simp_all
    · intro heq
      subst k
      simp_all
end ThreeSum.Coloring
