-- Prove2me | solution 1 for SoficGroups.KunActualSoficRootRadius.chosenWordEvaluation_multiplicative_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:57.599909+00:00
-- url     : https://prove2.me/submissions/8cc2293e-78e7-4201-b604-e2626796f5c1

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_normalizedHamming_comm
import Theorems.Thm_SoficGroups_normalizedHamming_nonneg
import Theorems.Thm_SoficGroups_normalizedHamming_triangle
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_normalizedHamming_mul_le
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_chosenWordEvaluation_tendsto_action

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
        SoficGroups.normalizedHamming
          (chosenWordEvaluation A s w n (g * h))
          (chosenWordEvaluation A s w n g *
            chosenWordEvaluation A s w n h))
      atTop (𝓝 0) := by
  have hgh := chosenWordEvaluation_tendsto_action A s w hw (g * h)
  have hgh' :
      Tendsto
        (fun n =>
          SoficGroups.normalizedHamming
            (chosenWordEvaluation A s w n (g * h))
            ((A.model n).action (g * h)))
        atTop (𝓝 0) := by
    convert hgh using 1
    funext n
    exact SoficGroups.normalizedHamming_comm _ _
  have hg := chosenWordEvaluation_tendsto_action A s w hw g
  have hh := chosenWordEvaluation_tendsto_action A s w hw h
  have hmul := A.multiplicative g h
  have hupper :
      Tendsto
        (fun n =>
          SoficGroups.normalizedHamming
              (chosenWordEvaluation A s w n (g * h))
              ((A.model n).action (g * h)) +
            SoficGroups.normalizedHamming
              ((A.model n).action (g * h))
              ((A.model n).action g * (A.model n).action h) +
            (SoficGroups.normalizedHamming
                ((A.model n).action g)
                (chosenWordEvaluation A s w n g) +
              SoficGroups.normalizedHamming
                ((A.model n).action h)
                (chosenWordEvaluation A s w n h)))
        atTop (𝓝 0) := by
    simpa using (hgh'.add hmul).add (hg.add hh)
  refine squeeze_zero
    (fun n => SoficGroups.normalizedHamming_nonneg _ _) ?_ hupper
  intro n
  have hfirst := SoficGroups.normalizedHamming_triangle
    (chosenWordEvaluation A s w n (g * h))
    ((A.model n).action (g * h))
    (chosenWordEvaluation A s w n g *
      chosenWordEvaluation A s w n h)
  have hsecond := SoficGroups.normalizedHamming_triangle
    ((A.model n).action (g * h))
    ((A.model n).action g * (A.model n).action h)
    (chosenWordEvaluation A s w n g *
      chosenWordEvaluation A s w n h)
  have hproduct := normalizedHamming_mul_le
    ((A.model n).action g) (chosenWordEvaluation A s w n g)
    ((A.model n).action h) (chosenWordEvaluation A s w n h)
  linarith
end SoficGroups.KunActualSoficRootRadius
