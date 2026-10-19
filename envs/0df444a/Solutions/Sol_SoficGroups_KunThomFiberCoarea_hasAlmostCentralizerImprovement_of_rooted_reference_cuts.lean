-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.hasAlmostCentralizerImprovement_of_rooted_reference_cuts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/58bca080-66c8-4b03-b799-90375aed233d

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_hasAlmostCentralizerImprovement_of_expanding_diagonal_cuts
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_first_singleton_half_of_reference_difference
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_second_singleton_half_of_reference_difference

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ)
    (h : ℝ) (hpositive : 0 < h)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (SoficGroups.boundary σ A : ℝ))
    (hcut : ∀ p : Equiv.Perm V,
      SoficGroups.permutationCommutationDefect σ p ≤ 2 * tolerance →
        ∃ U : Finset (V × V),
          2 * ((U \ SoficGroups.permutationGraph p).card +
            (SoficGroups.permutationGraph p \ U).card) ≤
              Fintype.card V ∧
          (h + 8 * (Fintype.card ι : ℝ)) *
              (SoficGroups.boundary
                (fun i => (σ i).prodCongr (σ i)) U : ℝ) ≤
            h * (tolerance : ℝ) ∧
          (5 : ℝ) *
              (4 * (SoficGroups.boundary
                (fun i => (σ i).prodCongr (σ i)) U : ℝ) +
                h * ((U \ SoficGroups.permutationGraph p).card : ℝ)) ≤
            h * (Fintype.card V : ℝ)) :
    SoficGroups.HasAlmostCentralizerImprovement σ tolerance := by
  apply hasAlmostCentralizerImprovement_of_expanding_diagonal_cuts
    σ tolerance h hpositive hexp
  intro p hp
  obtain ⟨U, hnear, hdefect, hdistance⟩ := hcut p hp
  exact ⟨U,
    first_singleton_half_of_reference_difference U p hnear,
    second_singleton_half_of_reference_difference U p hnear,
    hdefect, hdistance⟩
end SoficGroups.KunThomFiberCoarea
