-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.matchedFiberEdges_vertex_loss_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/bc4fdf03-62ff-474c-8232-73a135c8d0c2

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_first_excess_mass_le_diagonalBoundary
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_second_excess_mass_le_diagonalBoundary
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_first_zero_mass_le_diagonalBoundary
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_unmatched_vertices_le_zero_and_excess

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
    h * ((Fintype.card V - (matchedFiberEdges U).card : ℕ) : ℝ) ≤
      4 * (SoficGroups.boundary
        (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by
  have hcount := unmatched_vertices_le_zero_and_excess U
  have hcount_real :
      ((Fintype.card V - (matchedFiberEdges U).card : ℕ) : ℝ) ≤
        ((Finset.univ.filter fun x : V =>
          firstMultiplicity U x = 0).card : ℝ) +
          ((∑ x : V, (firstMultiplicity U x - 1 : ℕ)) : ℝ) +
          2 * ((∑ x : V, (secondMultiplicity U x - 1 : ℕ)) : ℝ) := by
    exact_mod_cast hcount
  have hzero := first_zero_mass_le_diagonalBoundary
    σ U h hexp hfirst
  have hrow := first_excess_mass_le_diagonalBoundary
    σ U h hexp hfirst
  have hcol := second_excess_mass_le_diagonalBoundary
    σ U h hexp hsecond
  have hrow' :
      h * (∑ x : V, ((firstMultiplicity U x - 1 : ℕ) : ℝ)) ≤
        (SoficGroups.boundary
          (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by
    simpa only [Nat.cast_sum] using hrow
  have hcol' :
      h * (∑ x : V, ((secondMultiplicity U x - 1 : ℕ) : ℝ)) ≤
        (SoficGroups.boundary
          (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by
    simpa only [Nat.cast_sum] using hcol
  calc
    h * ((Fintype.card V - (matchedFiberEdges U).card : ℕ) : ℝ) ≤
        h *
          (((Finset.univ.filter fun x : V =>
            firstMultiplicity U x = 0).card : ℝ) +
            ((∑ x : V, (firstMultiplicity U x - 1 : ℕ)) : ℝ) +
            2 * ((∑ x : V, (secondMultiplicity U x - 1 : ℕ)) : ℝ)) :=
      mul_le_mul_of_nonneg_left hcount_real hpositive.le
    _ = h * ((Finset.univ.filter fun x : V =>
          firstMultiplicity U x = 0).card : ℝ) +
          h * (∑ x : V, ((firstMultiplicity U x - 1 : ℕ) : ℝ)) +
          2 *
            (h * (∑ x : V, ((secondMultiplicity U x - 1 : ℕ) : ℝ))) := by
      ring
    _ ≤ 4 * (SoficGroups.boundary
          (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by
      linarith
end SoficGroups.KunThomFiberCoarea
