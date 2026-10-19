-- Prove2me | solution 1 for SoficGroups.KunActualSoficRootRadius.modelSeparationBad_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/45458147-d5aa-47b5-9a84-2444c97d6066

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_agreementSet_card_add_hammingDist
import Theorems.Thm_SoficGroups_CompressionCriterion_normalizedHamming_distinct_tendsto

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSoficRootRadius
open Filter Topology
open scoped BigOperators Pointwise
namespace SoficGroups.KunActualSoficRootRadius
theorem _root_.solution
    {G : Type*} [Group G]
    (A : SoficGroups.SoficApproximation G)
    {g h : G} (hne : g ≠ h) :
    Tendsto
      (fun n =>
        ((modelSeparationBad (A.model n) g h).card : ℝ) /
          (A.model n).size)
      atTop (𝓝 0) := by
  have hdist :=
    SoficGroups.CompressionCriterion.normalizedHamming_distinct_tendsto
      A hne
  have hlimit :
      Tendsto
        (fun n =>
          (1 : ℝ) - SoficGroups.normalizedHamming
            ((A.model n).action g) ((A.model n).action h))
        atTop (𝓝 0) := by
    have hone :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    simpa using hone.sub hdist
  convert hlimit using 1
  funext n
  have hcard :
      (SoficGroups.agreementSet
        ((A.model n).action g) ((A.model n).action h)).card +
        hammingDist
          (fun x => (A.model n).action g x)
          (fun x => (A.model n).action h x) =
        (A.model n).size := by
    simpa using SoficGroups.agreementSet_card_add_hammingDist
      ((A.model n).action g) ((A.model n).action h)
  have hreal :
      ((SoficGroups.agreementSet
          ((A.model n).action g) ((A.model n).action h)).card : ℝ) +
        (hammingDist
          (fun x => (A.model n).action g x)
          (fun x => (A.model n).action h x) : ℝ) =
          (A.model n).size := by
    exact_mod_cast hcard
  have hden : ((A.model n).size : ℝ) ≠ 0 := by
    exact_mod_cast (A.model n).size_pos.ne'
  simp only [modelSeparationBad, SoficGroups.normalizedHamming,
    Fintype.card_fin]
  field_simp
  linarith
end SoficGroups.KunActualSoficRootRadius
