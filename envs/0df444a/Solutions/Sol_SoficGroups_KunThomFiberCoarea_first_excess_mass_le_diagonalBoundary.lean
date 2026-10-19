-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.first_excess_mass_le_diagonalBoundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/2b881963-6081-48ba-9cbc-bc08322fea75

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_firstMultiplicity_totalVariation_le_twice_diagonalBoundary
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_excess_mass_le_of_diagonal_variation

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (U : Finset (V × V)) (h : ℝ)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (SoficGroups.boundary σ A : ℝ))
    (hsingle : Fintype.card V ≤
      2 * (singletonSupport (firstMultiplicity U)).card) :
    h * (∑ x : V, (firstMultiplicity U x - 1 : ℕ)) ≤
      (SoficGroups.boundary
        (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by
  apply excess_mass_le_of_diagonal_variation
    σ h hexp (firstMultiplicity U)
      (SoficGroups.boundary
        (fun i => (σ i).prodCongr (σ i)) U) hsingle
  exact firstMultiplicity_totalVariation_le_twice_diagonalBoundary
    σ U
end SoficGroups.KunThomFiberCoarea
