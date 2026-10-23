-- Prove2me | solution 1 for SubsetShrink.Events.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T05:49:10.911449+00:00
-- url     : https://prove2.me/submissions/953381e6-0f97-45ce-83e0-45dcf66a0d9f

import Mathlib
import Definitions.Def_SubsetShrink_Events_Model
import Theorems.Thm_SubsetShrink_Events_prob_F
import Theorems.Thm_SubsetShrink_Events_F_subset_E
import Theorems.Thm_SubsetShrink_Events_prob_G_corrected
import Theorems.Thm_SubsetShrink_Events_prob_H

open MeasureTheory ProbabilityTheory

open SubsetShrink.Events in
theorem solution {n p s : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (hX : UnitCols X)
    (σ : ℝ) (hσ : 0 < σ) (hs : 1 ≤ s) (hsp : s ≤ p) (δ0 : ℝ) (hδ0 : 0 < δ0) (hδ1 : δ0 ≤ 1) :
    (MeasurableSet (E X σ s) ∧
        1 - (s : ℝ) / (4 * Real.exp 1 * p) ≤ (noiseLaw n σ (E X σ s)).toReal) ∧
      (MeasurableSet (F X σ δ0) ∧ 1 - δ0 / 2 ≤ (noiseLaw n σ (F X σ δ0)).toReal) ∧
      (MeasurableSet (Gc X σ δ0 s) ∧ 1 - δ0 ≤ (noiseLaw n σ (Gc X σ δ0 s)).toReal) ∧
      (MeasurableSet (H X σ δ0) ∧ 1 - δ0 ≤ (noiseLaw n σ (H X σ δ0)).toReal) := by
  have hp : 1 ≤ p := le_trans hs hsp
  have hprob : IsProbabilityMeasure (noiseLaw n σ) := by
    unfold noiseLaw
    have hv : ∀ v : NNReal,
        IsProbabilityMeasure (Measure.pi (fun _ : Fin n => gaussianReal 0 v)) :=
      fun v => inferInstance
    exact hv ⟨σ ^ 2, sq_nonneg σ⟩
  -- measurability of `E`: an intersection of closed half-spaces
  have hEm : MeasurableSet (E X σ s) := by
    have : E X σ s = ⋂ u : Fin p → ℝ, ⋂ (_ : l0 u ≤ s), {ε : Fin n → ℝ |
        dot ε (X.mulVec u) ≤ (4 + Real.sqrt 2) * σ *
          Real.sqrt ((s : ℝ) * Real.log (2 * Real.exp 1 * p / s)) * l2 u} := by
      ext ε; simp [E]
    rw [this]
    refine IsClosed.measurableSet (isClosed_iInter fun u => isClosed_iInter fun _ => ?_)
    exact isClosed_le (by unfold dot; fun_prop) continuous_const
  -- `δ' = s/(2ep) ∈ (0, 1]`
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hspR : (s : ℝ) ≤ p := by exact_mod_cast hsp
  have he : (1 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  set δ' : ℝ := (s : ℝ) / (2 * Real.exp 1 * p) with hδ'
  have hδ'0 : 0 < δ' := by positivity
  have hδ'1 : δ' ≤ 1 := by
    rw [hδ', div_le_one (by positivity)]; nlinarith
  have hF' := prob_F X hX σ hσ δ' hδ'0 hδ'1
  have hsub := (F_subset_E X hX σ hσ hs hsp).2
  have hmono : (noiseLaw n σ (F X σ δ')).toReal ≤ (noiseLaw n σ (E X σ s)).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have hval : δ' / 2 = (s : ℝ) / (4 * Real.exp 1 * p) := by
    rw [hδ']; field_simp; ring
  refine ⟨⟨hEm, ?_⟩, prob_F X hX σ hσ δ0 hδ0 hδ1,
    prob_G_corrected X hX σ hσ hs hsp δ0 hδ0 hδ1, prob_H hp X hX σ hσ δ0 hδ0 hδ1⟩
  have := hF'.2
  rw [hval] at this
  linarith
