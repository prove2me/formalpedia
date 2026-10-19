-- Prove2me | solution 1 for SoficGroups.ChosenCayleyMatchedComponentRealization.sourceFirstFactorCayleyRadiusBad_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/08d6ab3f-8c02-49a0-8df4-688bddb34b3e

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_symmetricGeneratorWord_prod
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_chosenCayleyRadiusBad_density_tendsto_zero

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
    (k : ℕ) :
    Tendsto
      (fun n =>
        ((sourceFirstFactorCayleyRadiusBad
          A S hsymmetric hgenerates n k).card : ℝ) /
            (A.model n).size)
      atTop (nhds 0) := by
  exact chosenCayleyRadiusBad_density_tendsto_zero
    (sourceFirstFactorApproximation A)
    S (symmetricGeneratorWord S hsymmetric hgenerates)
    (symmetricGeneratorWord_prod S hsymmetric hgenerates) k
end SoficGroups.ChosenCayleyMatchedComponentRealization
