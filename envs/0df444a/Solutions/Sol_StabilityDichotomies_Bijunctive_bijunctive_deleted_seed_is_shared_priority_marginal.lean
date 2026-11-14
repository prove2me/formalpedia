-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.bijunctive_deleted_seed_is_shared_priority_marginal
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:56:22.159961+00:00
-- url     : https://prove2.me/submissions/a1234938-3e33-4d9a-a6df-a57f37117268

import Theorems.Thm_StabilityDichotomies_Bijunctive_iid_product_delete_one_coordinate
import Definitions.Def_StabilityDichotomies_Approximability_BijunctiveLaw
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Function StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V) (c : Constraint Γ V)
    (ε : ℝ) (hε : 0 < ε)
    (e : Fin I.constraints.card ≃ Option (Fin (I.delete c).constraints.card)) :
    Measure.map (fun z : (Fin I.constraints.card → ℝ) × ℝ × (Literal V → ℝ) =>
      (fun i : Fin (I.delete c).constraints.card => z.1 (e.symm (some i)), z.2))
      (bijunctiveSeedMeasure rep I ε) = bijunctiveSeedMeasure rep (I.delete c) ε := by
  classical
  haveI : IsProbabilityMeasure unitPriorityMeasure := by
    unfold unitPriorityMeasure
    apply cond_isProbabilityMeasure_of_finite
    · rw [Real.volume_Icc]; exact ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num))
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  haveI : IsProbabilityMeasure (cutoffMeasure ε) := by
    unfold cutoffMeasure
    apply cond_isProbabilityMeasure_of_finite
    · rw [Real.volume_Icc]; exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hβ : 0 < bijunctiveRate rep ε := by
    unfold bijunctiveRate
    apply div_pos hε
    have hb : (0 : ℝ) < rep.clauseBound := by exact_mod_cast rep.clauseBound_pos
    positivity
  haveI : IsProbabilityMeasure (shiftMeasure (bijunctiveRate rep ε)) := by
    unfold shiftMeasure
    exact isProbabilityMeasure_expMeasure hβ
  let f : (Fin I.constraints.card → ℝ) → (Fin (I.delete c).constraints.card → ℝ) :=
    fun p i => p (e.symm (some i))
  have hf : Measurable f := measurable_pi_lambda _ fun i => measurable_pi_apply (e.symm (some i))
  have hmap : Measure.map f (Measure.pi (fun _ : Fin I.constraints.card => unitPriorityMeasure)) =
      Measure.pi (fun _ : Fin (I.delete c).constraints.card => unitPriorityMeasure) :=
    iid_product_delete_one_coordinate unitPriorityMeasure e
  have hmp : MeasurePreserving f (Measure.pi (fun _ : Fin I.constraints.card => unitPriorityMeasure))
      (Measure.pi (fun _ : Fin (I.delete c).constraints.card => unitPriorityMeasure)) := ⟨hf,hmap⟩
  let ν := (cutoffMeasure ε).prod (Measure.pi (fun _ : Literal V => shiftMeasure (bijunctiveRate rep ε)))
  have hid : MeasurePreserving (id : ℝ × (Literal V → ℝ) → ℝ × (Literal V → ℝ)) ν ν := MeasurePreserving.id ν
  have hprod := (hmp.prod hid).map_eq
  change Measure.map _ ((Measure.pi (fun _ : Fin I.constraints.card => unitPriorityMeasure)).prod ν) = _
  change Measure.map (Prod.map f id) _ = _
  exact hprod
