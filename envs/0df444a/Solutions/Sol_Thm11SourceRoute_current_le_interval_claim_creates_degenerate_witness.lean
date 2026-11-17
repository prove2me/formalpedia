-- Prove2me | solution 1 for Thm11SourceRoute.current_le_interval_claim_creates_degenerate_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:21:35.140494+00:00
-- url     : https://prove2.me/submissions/797e8103-b1d8-4458-9d24-e0689900e66a

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_basic_F000
import Mathlib.Tactic


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset BigOperators
open Set Topology

noncomputable section

namespace Thm11SourceRoute
end Thm11SourceRoute
section Thm11SourceRoute
open Thm11SourceRoute


theorem solution
    (hclaim :
      ∀ {f α : ℝ → ℝ} {a b : ℝ},
        a ≤ b →
        Monotone α →
        BddAbove (f '' Icc a b) →
        BddBelow (f '' Icc a b) →
        (discontinuitySetOn f a b).Finite →
        (∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x) →
        RSIntegrable f α a b) :
    RSIntegrable (fun _ : ℝ => 0) (fun _ : ℝ => 0) 0 0 := by
  refine hclaim (f := fun _ : ℝ => 0) (α := fun _ : ℝ => 0)
    (a := 0) (b := 0) le_rfl ?_ ?_ ?_ ?_ ?_
  · intro x y hxy
    simp
  · refine ⟨0, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    simp
  · refine ⟨0, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    simp
  · rw [discontinuitySetOn_const_refl_empty]
    exact Set.finite_empty
  · intro x hx
    simpa using (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) x)
end Thm11SourceRoute
