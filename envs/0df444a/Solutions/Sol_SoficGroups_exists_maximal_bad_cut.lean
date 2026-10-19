-- Prove2me | solution 1 for SoficGroups.exists_maximal_bad_cut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/2e897eea-512d-4767-9c01-23f9c3893bc9

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {V ι : Type*}
    [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (ell : ℝ) :
    ∃ B : Finset V,
      2 * B.card ≤ Fintype.card V ∧
      (boundary σ B : ℝ) ≤ ell * (B.card : ℝ) ∧
      ∀ A : Finset V,
        2 * A.card ≤ Fintype.card V →
        (boundary σ A : ℝ) < ell * (A.card : ℝ) → A.card ≤ B.card := by
  classical
  let candidates : Finset (Finset V) :=
    Finset.univ.powerset.filter fun A =>
      2 * A.card ≤ Fintype.card V ∧
        (boundary σ A : ℝ) < ell * (A.card : ℝ)
  by_cases hnonempty : candidates.Nonempty
  · obtain ⟨B, hBmem, hmax⟩ :=
      Finset.exists_max_image candidates Finset.card hnonempty
    have hprops :
        2 * B.card ≤ Fintype.card V ∧
          (boundary σ B : ℝ) < ell * (B.card : ℝ) := by
      have hmem : B ∈ Finset.univ.powerset.filter fun A =>
          2 * A.card ≤ Fintype.card V ∧
            (boundary σ A : ℝ) < ell * (A.card : ℝ) := by
        simpa only [candidates] using hBmem
      exact (Finset.mem_filter.mp hmem).2
    refine ⟨B, hprops.1, hprops.2.le, ?_⟩
    intro A hhalf hbad
    apply hmax A
    simp [candidates, hhalf, hbad]
  · refine ⟨∅, by simp, by simp [boundary], ?_⟩
    intro A hhalf hbad
    exfalso
    apply hnonempty
    refine ⟨A, ?_⟩
    simp [candidates, hhalf, hbad]
end SoficGroups
