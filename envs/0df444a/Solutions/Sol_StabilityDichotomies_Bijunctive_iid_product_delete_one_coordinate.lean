-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.iid_product_delete_one_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:43:15.817215+00:00
-- url     : https://prove2.me/submissions/21ef576e-b438-4bcc-a6c6-49ce827ebe63

import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Function StabilityDichotomies.Bijunctive

theorem solution {α β : Type} [Fintype α] [Fintype β]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (e : α ≃ Option β) :
    Measure.map (fun p : α → ℝ => fun i : β => p (e.symm (some i)))
      (Measure.pi (fun _ : α => ν)) = Measure.pi (fun _ : β => ν) := by
  classical
  let E := MeasurableEquiv.piOptionEquivProd (fun _ : Option β => ℝ)
  have hinv : MeasurePreserving E.symm
      ((Measure.pi (fun _ : β => ν)).prod ν) (Measure.pi (fun _ : Option β => ν)) := by
    refine ⟨E.symm.measurable, ?_⟩
    exact Measure.pi_map_piOptionEquivProd (fun _ => ν)
  have hopt := hinv.symm E.symm
  have hre := measurePreserving_piCongrLeft (fun _ : Option β => ν) e
  have hfinal := (measurePreserving_fst.comp (hopt.comp hre)).map_eq
  have hf : (fun p : α → ℝ => fun i : β => p (e.symm (some i))) =
      Prod.fst ∘ E ∘ MeasurableEquiv.piCongrLeft (fun _ : Option β => ℝ) e := by
    funext p i
    simp only [Function.comp_apply, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply,eq_rec_constant]
    simp [E, MeasurableEquiv.piOptionEquivProd, MeasurableEquiv.piCongrLeft,
      MeasurableEquiv.sumPiEquivProdPi, Equiv.piCongrLeft_apply]
    rfl
  rw [hf]
  exact hfinal
