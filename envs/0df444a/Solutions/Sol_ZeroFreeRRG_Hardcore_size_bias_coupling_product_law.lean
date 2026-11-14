-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.size_bias_coupling_product_law
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:53:48.767702+00:00
-- url     : https://prove2.me/submissions/a309d83d-962a-47cb-b483-0e2d83ab9976

import Theorems.Thm_ZeroFreeRRG_Hardcore_finite_product_density
import Mathlib
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators ENNReal

theorem solution (d : ℕ) (S : Finset (Fin d)) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x : ℝ => x) μ) (hpos : ∀ᵐ x ∂μ, 0 ≤ x)
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π]
    (hfst : Measure.map Prod.fst π = μ)
    (hsnd : Measure.map Prod.snd π = μ.withDensity (fun x => ENNReal.ofReal x)) :
    Measure.map (fun xs : Fin d → ℝ × ℝ => fun i => if i ∈ S then (xs i).2 else (xs i).1)
      (Measure.pi fun _ : Fin d => π) =
    (Measure.pi fun _ : Fin d => μ).withDensity
      (fun xs => ENNReal.ofReal (∏ i, if i ∈ S then max (xs i) 0 else 1)) := by
  let f : Fin d → (ℝ × ℝ) → ℝ := fun i p => if i ∈ S then p.2 else p.1
  let ρ : Fin d → ℝ → ℝ := fun i x => if i ∈ S then max x 0 else 1
  have hf (i : Fin d) : Measurable (f i) := by
    dsimp [f]
    split_ifs <;> fun_prop
  letI : ∀ i, IsProbabilityMeasure (Measure.map (f i) π) :=
    fun i => Measure.isProbabilityMeasure_map (hf i).aemeasurable
  have hρint (i : Fin d) : Integrable (ρ i) μ := by
    dsimp [ρ]
    split_ifs
    · change Integrable ((fun x : ℝ => x) ⊔ (fun _ => 0)) μ
      exact hint.sup (integrable_const 0)
    · exact integrable_const 1
  have hρpos (i : Fin d) (x : ℝ) : 0 ≤ ρ i x := by
    dsimp [ρ]
    split_ifs
    · exact le_max_right _ _
    · norm_num
  have hm (i : Fin d) : Measure.map (f i) π = μ.withDensity (fun x => ENNReal.ofReal (ρ i x)) := by
    dsimp [f,ρ]
    split_ifs with hi
    · rw [hsnd]
      apply withDensity_congr_ae
      filter_upwards [hpos] with x hx
      rw [max_eq_left hx]
    · rw [hfst]
      simpa using (withDensity_one (μ := μ)).symm
  calc
    _ = Measure.pi (fun i => Measure.map (f i) π) := by
      exact Measure.pi_map_pi (fun i => (hf i).aemeasurable)
    _ = Measure.pi (fun i => μ.withDensity (fun x => ENNReal.ofReal (ρ i x))) := by
      congr 1
      funext i
      exact hm i
    _ = _ := finite_product_density (fun _ : Fin d => μ) ρ hρpos hρint
