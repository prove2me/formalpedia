-- Prove2me | solution 1 for SoficGroups.KunActualSoficRootRadius.chosenWordMultiplicationBad_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/921a3775-587e-4cb7-8450-c116f6213c64

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_chosenWordEvaluation_multiplicative_tendsto

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSoficRootRadius
open Filter Topology
open scoped BigOperators Pointwise
namespace SoficGroups.KunActualSoficRootRadius
theorem _root_.solution
    {G ι : Type*} [Group G]
    (A : SoficGroups.SoficApproximation G)
    (s : ι → G) (w : G → List ι)
    (hw : ∀ g, ((w g).map s).prod = g) (g h : G) :
    Tendsto
      (fun n =>
        ((chosenWordMultiplicationBad A s w n g h).card : ℝ) /
          (A.model n).size)
      atTop (𝓝 0) := by
  simpa [chosenWordMultiplicationBad,
    SoficGroups.normalizedHamming, hammingDist] using
      chosenWordEvaluation_multiplicative_tendsto A s w hw g h
end SoficGroups.KunActualSoficRootRadius
