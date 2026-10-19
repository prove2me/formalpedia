-- Prove2me | solution 1 for SoficGroups.CanonicalProductRadiusBadMatchedCapture.canonicalProductRadiusBad_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/c143bd67-3bfd-4eee-aa13-38d16c8ee643

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_finiteRootBad_density_tendsto_zero
import Theorems.Thm_SoficGroups_ChosenCayleyMatchedComponentRealization_sourceFirstFactorCayleyRadiusBad_density_tendsto_zero

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
open Filter Topology
open SoficGroups.KunActualSoficRootRadius
open SoficGroups.ChosenCayleyMatchedComponentRealization
open SoficGroups.MatchedComponentCompletion
open SoficGroups.MatchedComponentExitBudget
open scoped BigOperators Pointwise symmDiff
namespace SoficGroups.CanonicalProductRadiusBadMatchedCapture
theorem _root_.solution
    {K J : Type*} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (A : SoficGroups.SoficApproximation (K × J))
    (S : Finset K)
    (hsymmetric : ∀ a ∈ S, a⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (F : Finset J) (k : ℕ) :
    Tendsto
      (fun n =>
        ((canonicalProductRadiusBad
          A S hsymmetric hgenerates F n k).card : ℝ) /
            (A.model n).size)
      atTop (nhds 0) := by
  have hfactor :=
    sourceFirstFactorCayleyRadiusBad_density_tendsto_zero
      A S hsymmetric hgenerates k
  have hproduct :=
    finiteRootBad_density_tendsto_zero
      A (sourceProductRadiusLabels S F k)
  have hsum : Tendsto
      (fun n =>
        ((sourceFirstFactorCayleyRadiusBad
          A S hsymmetric hgenerates n k).card : ℝ) /
            (A.model n).size +
        ((finiteRootBad (A.model n)
          (sourceProductRadiusLabels S F k)).card : ℝ) /
            (A.model n).size)
      atTop (nhds 0) := by
    simpa using hfactor.add hproduct
  refine squeeze_zero (fun n => by positivity) ?_ hsum
  intro n
  have hcard :
      ((canonicalProductRadiusBad
        A S hsymmetric hgenerates F n k).card : ℝ) ≤
        (sourceFirstFactorCayleyRadiusBad
          A S hsymmetric hgenerates n k).card +
        (finiteRootBad (A.model n)
          (sourceProductRadiusLabels S F k)).card := by
    exact_mod_cast Finset.card_union_le
      (sourceFirstFactorCayleyRadiusBad
        A S hsymmetric hgenerates n k)
      (finiteRootBad (A.model n)
        (sourceProductRadiusLabels S F k))
  calc
    ((canonicalProductRadiusBad
      A S hsymmetric hgenerates F n k).card : ℝ) /
        (A.model n).size ≤
      (((sourceFirstFactorCayleyRadiusBad
        A S hsymmetric hgenerates n k).card : ℝ) +
        ((finiteRootBad (A.model n)
          (sourceProductRadiusLabels S F k)).card : ℝ)) /
          (A.model n).size :=
        div_le_div_of_nonneg_right hcard (by positivity)
    _ = ((sourceFirstFactorCayleyRadiusBad
          A S hsymmetric hgenerates n k).card : ℝ) /
            (A.model n).size +
        ((finiteRootBad (A.model n)
          (sourceProductRadiusLabels S F k)).card : ℝ) /
            (A.model n).size := by
      rw [add_div]
end SoficGroups.CanonicalProductRadiusBadMatchedCapture
