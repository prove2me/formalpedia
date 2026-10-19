-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.hasAlmostCentralizerImprovement_of_expanding_diagonal_cuts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/c64cb47e-2842-4364-87cc-ff3e73f24b83

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_exists_boundary_controlled_permutation_repair_close_to_reference

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
          Fintype.card V ≤
            2 * (singletonSupport (firstMultiplicity U)).card ∧
          Fintype.card V ≤
            2 * (singletonSupport (secondMultiplicity U)).card ∧
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
  refine ⟨?_⟩
  intro p hp
  obtain ⟨U, hfirst, hsecond, hcutdefect, hcutdistance⟩ := hcut p hp
  obtain ⟨q, hqdistance, hqdefect⟩ :=
    exists_boundary_controlled_permutation_repair_close_to_reference
      σ U p h hpositive hexp hfirst hsecond
  have hdefect_real :
      (SoficGroups.permutationCommutationDefect σ q : ℝ) ≤
        (tolerance : ℝ) := by
    nlinarith
  have hdefect :
      SoficGroups.permutationCommutationDefect σ q ≤ tolerance := by
    exact_mod_cast hdefect_real
  have hscaled := mul_le_mul_of_nonneg_left hqdistance
    (show (0 : ℝ) ≤ 5 by norm_num)
  have hdistance_real :
      (5 : ℝ) * (SoficGroups.permutationDistance q p : ℝ) ≤
        (Fintype.card V : ℝ) := by
    nlinarith
  have hdistance :
      5 * SoficGroups.permutationDistance q p ≤ Fintype.card V := by
    exact_mod_cast hdistance_real
  exact ⟨q, hdefect, hdistance⟩
end SoficGroups.KunThomFiberCoarea
