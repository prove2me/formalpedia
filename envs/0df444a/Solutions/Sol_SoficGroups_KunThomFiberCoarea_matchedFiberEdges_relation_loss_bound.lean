-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.matchedFiberEdges_relation_loss_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/63ed9e76-8a34-459f-872d-937fb0ad5c9c

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_first_excess_mass_le_diagonalBoundary
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_second_excess_mass_le_diagonalBoundary
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_card_nonmatchedFiberEdges_le_twice_excess

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
    h * ((U \ matchedFiberEdges U).card : ℝ) ≤
      4 * (SoficGroups.boundary
        (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by
  have hcount := card_nonmatchedFiberEdges_le_twice_excess U
  have hcount_real :
      ((U \ matchedFiberEdges U).card : ℝ) ≤
        2 * ((∑ x : V, (firstMultiplicity U x - 1 : ℕ)) : ℝ) +
          2 * ((∑ x : V, (secondMultiplicity U x - 1 : ℕ)) : ℝ) := by
    exact_mod_cast hcount
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
    h * ((U \ matchedFiberEdges U).card : ℝ) ≤
        h *
          (2 * ((∑ x : V, (firstMultiplicity U x - 1 : ℕ)) : ℝ) +
            2 * ((∑ x : V, (secondMultiplicity U x - 1 : ℕ)) : ℝ)) :=
      mul_le_mul_of_nonneg_left hcount_real hpositive.le
    _ = 2 *
          (h * (∑ x : V, ((firstMultiplicity U x - 1 : ℕ) : ℝ))) +
          2 *
          (h * (∑ x : V, ((secondMultiplicity U x - 1 : ℕ) : ℝ))) := by
      ring
    _ ≤ 4 * (SoficGroups.boundary
          (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by
      linarith
end SoficGroups.KunThomFiberCoarea
