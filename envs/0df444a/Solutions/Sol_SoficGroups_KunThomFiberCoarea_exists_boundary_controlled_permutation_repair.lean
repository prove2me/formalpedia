-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.exists_boundary_controlled_permutation_repair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/b37eec43-e5d1-4acd-8b4c-603601799680

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_boundary_permutationGraph_eq_commutationDefect
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_matchedFiberEdges_relation_loss_bound
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_matchedFiberEdges_vertex_loss_bound
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_exists_permutationGraph_containing_matchedFiberEdges
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_permutationGraph_sdiff_bounds_of_matchedFiberEdges
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_boundary_le_boundary_add_sdiff

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (U : Finset (V × V))
    (h : ℝ) (hpositive : 0 < h)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (SoficGroups.boundary σ A : ℝ))
    (hfirst : Fintype.card V ≤
      2 * (singletonSupport (firstMultiplicity U)).card)
    (hsecond : Fintype.card V ≤
      2 * (singletonSupport (secondMultiplicity U)).card) :
    ∃ q : Equiv.Perm V,
      matchedFiberEdges U ⊆ SoficGroups.permutationGraph q ∧
        h * (SoficGroups.permutationCommutationDefect σ q : ℝ) ≤
          (h + 8 * (Fintype.card ι : ℝ)) *
            (SoficGroups.boundary
              (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by
  classical
  obtain ⟨q, hq⟩ :=
    exists_permutationGraph_containing_matchedFiberEdges U
  obtain ⟨hgraphleft, hgraphright⟩ :=
    permutationGraph_sdiff_bounds_of_matchedFiberEdges U q hq
  have hboundary := boundary_le_boundary_add_sdiff
    (fun i => (σ i).prodCongr (σ i))
      (SoficGroups.permutationGraph q) U
  have hdefect :
      SoficGroups.permutationCommutationDefect σ q ≤
        SoficGroups.boundary
            (fun i => (σ i).prodCongr (σ i)) U +
          Fintype.card ι *
            ((Fintype.card V - (matchedFiberEdges U).card) +
              (U \ matchedFiberEdges U).card) := by
    rw [← SoficGroups.boundary_permutationGraph_eq_commutationDefect]
    apply hboundary.trans
    exact Nat.add_le_add_left
      (Nat.mul_le_mul_left (Fintype.card ι)
        (Nat.add_le_add hgraphleft hgraphright)) _
  have hdefect_real :
      (SoficGroups.permutationCommutationDefect σ q : ℝ) ≤
        (SoficGroups.boundary
          (fun i => (σ i).prodCongr (σ i)) U : ℝ) +
          (Fintype.card ι : ℝ) *
            (((Fintype.card V - (matchedFiberEdges U).card : ℕ) : ℝ) +
              ((U \ matchedFiberEdges U).card : ℝ)) := by
    exact_mod_cast hdefect
  have hvertex := matchedFiberEdges_vertex_loss_bound
    σ U h hpositive hexp hfirst hsecond
  have hrelation := matchedFiberEdges_relation_loss_bound
    σ U h hpositive hexp hfirst hsecond
  have hsum :
      h *
          (((Fintype.card V - (matchedFiberEdges U).card : ℕ) : ℝ) +
            ((U \ matchedFiberEdges U).card : ℝ)) ≤
        8 * (SoficGroups.boundary
          (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by
    nlinarith
  have hdnonneg : (0 : ℝ) ≤ Fintype.card ι := by
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hsum hdnonneg
  refine ⟨q, hq, ?_⟩
  calc
    h * (SoficGroups.permutationCommutationDefect σ q : ℝ) ≤
        h *
          ((SoficGroups.boundary
            (fun i => (σ i).prodCongr (σ i)) U : ℝ) +
            (Fintype.card ι : ℝ) *
              (((Fintype.card V - (matchedFiberEdges U).card : ℕ) : ℝ) +
                ((U \ matchedFiberEdges U).card : ℝ))) :=
      mul_le_mul_of_nonneg_left hdefect_real hpositive.le
    _ ≤ (h + 8 * (Fintype.card ι : ℝ)) *
          (SoficGroups.boundary
            (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by
      nlinarith
end SoficGroups.KunThomFiberCoarea
