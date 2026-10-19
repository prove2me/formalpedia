-- Prove2me | solution 1 for SoficGroups.ChosenCayleyMatchedComponentRealization.sourceFirstFactor_injective_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/79090d84-ee0a-46ba-bf13-eb44f4da05f8

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_chosenCayleyRadiusBad_injective_ball

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ChosenCayleyMatchedComponentRealization
open Filter Topology
open SoficGroups.KunActualSoficRootRadius
open SoficGroups.KunResidualRetainedSelection
open scoped BigOperators Pointwise symmDiff
namespace SoficGroups.ChosenCayleyMatchedComponentRealization
theorem _root_.solution
    {K J : Type*} [Group K] [Group J] [DecidableEq K]
    (A : SoficGroups.SoficApproximation (K × J))
    (S : Finset K)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (n k : ℕ)
    {x : Fin (A.model n).size}
    (hx : x ∉ sourceFirstFactorCayleyRadiusBad
      A S hsymmetric hgenerates n k) :
    Set.InjOn
      (fun g : K => (A.model n).action (g, 1) x)
      (↑(S ^ k) : Set K) := by
  exact chosenCayleyRadiusBad_injective_ball
    (sourceFirstFactorApproximation A)
    S (symmetricGeneratorWord S hsymmetric hgenerates)
    n k hx
end SoficGroups.ChosenCayleyMatchedComponentRealization
