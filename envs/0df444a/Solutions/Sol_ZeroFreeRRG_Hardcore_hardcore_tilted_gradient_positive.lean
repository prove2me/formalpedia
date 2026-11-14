-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_tilted_gradient_positive
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:03:12.738173+00:00
-- url     : https://prove2.me/submissions/c5350e00-7467-4d6b-b5dc-6a4add9d7c65

import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_tilted_weight_law
import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_tilted_nontrivial
import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_positive_weighted_log
import Theorems.Thm_ZeroFreeRRG_Hardcore_tilted_product_expectation
import Mathlib
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators ENNReal

theorem solution (d : ℕ) (hd : 2 ≤ d) (η : Measure ℝ) [IsProbabilityMeasure η]
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hb : ∀ᵐ h ∂η, -1 ≤ h ∧ h ≤ 1)
    (hint : Integrable (fun h : ℝ => h) η)
    (hmean : (∫ h : ℝ, h ∂η) = 0)
    (hn : ¬(∀ᵐ h ∂η, h = 0)) :
    let W := fun h : ℝ => (1-h)/(1+θ*h)
    0 < ∫ hs : Fin d → ℝ, (∏ i, (1+θ*hs i)) *
      (((∏ i, W (hs i)) - ∑ i, W (hs i) + d - 1) *
        Real.log (1+θ*∏ i, W (hs i))) ∂(Measure.pi fun _ : Fin d => η) := by
  dsimp only
  let W := fun h : ℝ => (1-h)/(1+θ*h)
  let f := fun h : ℝ => max (1+θ*h) 0
  let τ := η.withDensity (fun h => ENNReal.ofReal (1+θ*h))
  let ν := Measure.map W τ
  have hW : Measurable W := by dsimp [W]; fun_prop
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hf0 (h : ℝ) : 0 ≤ f h := le_max_right _ _
  have hfi : Integrable f η := by
    change Integrable ((fun h : ℝ => 1+θ*h) ⊔ (fun _ => 0)) η
    exact ((integrable_const 1).add (hint.const_mul θ)).sup (integrable_const 0)
  have heq : η.withDensity (fun h => ENNReal.ofReal (f h)) = τ := by
    dsimp [τ]
    apply withDensity_congr_ae
    filter_upwards [hb] with h hh
    have hp : 0 ≤ 1+θ*h := by
      nlinarith [mul_nonneg hθ.le (show 1+h ≥ 0 by linarith)]
    dsimp [f]
    rw [max_eq_left hp]
  have hwlaw := hardcore_tilted_weight_law η θ hθ.le hθ1 hb hint hmean
  letI : IsProbabilityMeasure ν := hwlaw.1
  have htprob : IsProbabilityMeasure τ := by
    apply isProbabilityMeasure_iff.mpr
    have hν : ν univ = 1 := measure_univ
    have hmap : Measure.map W τ univ = τ univ := by
      rw [Measure.map_apply hW MeasurableSet.univ]
      rfl
    exact hmap.symm.trans hν
  letI : IsProbabilityMeasure (η.withDensity (fun h => ENNReal.ofReal (f h))) := by rw [heq]; exact htprob
  have hne : ν ≠ Measure.dirac 1 := hardcore_tilted_nontrivial η θ hθ.le hθ1 hb hn
  have hC : 0 ≤ 2/(1-θ) := div_nonneg (by norm_num) (by linarith)
  have hstrict := hardcore_positive_weighted_log d hd θ (2/(1-θ)) hθ hC ν hwlaw.2.1 hwlaw.2.2.1 hwlaw.2.2.2 hne
  let K := fun xs : Fin d → ℝ => ((∏ i, xs i)-∑ i, xs i+d-1)*Real.log (1+θ*∏ i, xs i)
  have hK : Measurable K := by dsimp [K]; fun_prop
  have hid := tilted_product_expectation d η f W hf hW hf0 hfi K hK
  rw [heq] at hid
  have hgood : ∀ᵐ xs ∂(Measure.pi fun _ : Fin d => η), ∀ i, -1 ≤ xs i ∧ xs i ≤ 1 := by
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi (fun _ : Fin d => hb)
  have hfinal : (∫ xs : Fin d → ℝ, (∏ i, f (xs i)) * K (fun i => W (xs i))
      ∂(Measure.pi fun _ : Fin d => η)) =
      ∫ xs : Fin d → ℝ, (∏ i, (1+θ*xs i)) * K (fun i => W (xs i))
        ∂(Measure.pi fun _ : Fin d => η) := by
    apply integral_congr_ae
    filter_upwards [hgood] with xs hx
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    have hp : 0 ≤ 1+θ*xs i := by
      nlinarith [mul_nonneg hθ.le (show 1+xs i ≥ 0 by linarith [(hx i).1])]
    exact max_eq_left hp
  rw [hfinal] at hid
  change 0 < (∫ xs : Fin d → ℝ, K xs ∂(Measure.pi fun _ : Fin d => ν)) at hstrict
  rw [hid] at hstrict
  exact hstrict
