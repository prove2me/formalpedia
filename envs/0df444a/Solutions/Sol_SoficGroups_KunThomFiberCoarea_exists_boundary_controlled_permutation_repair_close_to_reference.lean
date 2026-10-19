-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.exists_boundary_controlled_permutation_repair_close_to_reference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/97263d44-1b95-4180-aadb-b68d1d85bb1b

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_matchedFiberEdges_vertex_loss_bound
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_exists_boundary_controlled_permutation_repair
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_permutationDistance_le_matching_loss_add_reference

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (U : Finset (V × V))
    (p : Equiv.Perm V) (h : ℝ) (hpositive : 0 < h)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (SoficGroups.boundary σ A : ℝ))
    (hfirst : Fintype.card V ≤
      2 * (singletonSupport (firstMultiplicity U)).card)
    (hsecond : Fintype.card V ≤
      2 * (singletonSupport (secondMultiplicity U)).card) :
    ∃ q : Equiv.Perm V,
      h * (SoficGroups.permutationDistance q p : ℝ) ≤
          4 * (SoficGroups.boundary
            (fun i => (σ i).prodCongr (σ i)) U : ℝ) +
            h * ((U \ SoficGroups.permutationGraph p).card : ℝ) ∧
        h * (SoficGroups.permutationCommutationDefect σ q : ℝ) ≤
          (h + 8 * (Fintype.card ι : ℝ)) *
            (SoficGroups.boundary
              (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by
  obtain ⟨q, hq, hdefect⟩ :=
    exists_boundary_controlled_permutation_repair
      σ U h hpositive hexp hfirst hsecond
  have hdistance :=
    permutationDistance_le_matching_loss_add_reference U q p hq
  have hdistance_real :
      (SoficGroups.permutationDistance q p : ℝ) ≤
        ((Fintype.card V - (matchedFiberEdges U).card : ℕ) : ℝ) +
          ((U \ SoficGroups.permutationGraph p).card : ℝ) := by
    exact_mod_cast hdistance
  have hvertex := matchedFiberEdges_vertex_loss_bound
    σ U h hpositive hexp hfirst hsecond
  refine ⟨q, ?_, hdefect⟩
  have hscaled := mul_le_mul_of_nonneg_left hdistance_real hpositive.le
  nlinarith
end SoficGroups.KunThomFiberCoarea
