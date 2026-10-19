-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.first_zero_mass_le_diagonalBoundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/5b34b515-91a9-40d0-9358-4c4d8a61e950

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_firstMultiplicity_totalVariation_le_twice_diagonalBoundary
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_zero_mass_le_of_diagonal_variation

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
    h * (Finset.univ.filter fun x : V =>
      firstMultiplicity U x = 0).card ≤
        (SoficGroups.boundary
          (fun i => (σ i).prodCongr (σ i)) U : ℝ) := by
  apply zero_mass_le_of_diagonal_variation
    σ h hexp (firstMultiplicity U)
      (SoficGroups.boundary
        (fun i => (σ i).prodCongr (σ i)) U) hsingle
  exact firstMultiplicity_totalVariation_le_twice_diagonalBoundary
    σ U
end SoficGroups.KunThomFiberCoarea
