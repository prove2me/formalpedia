-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_entropy_integral_derivative
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:51:56.584026+00:00
-- url     : https://prove2.me/submissions/1d8231c9-eccc-426f-b34e-deb21fbb8a16

import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_vertex_entropy_derivative
import Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_entropy_uniform_bound
import Mathlib
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators Topology

theorem solution (d : ℕ) (η : Measure ℝ) [IsProbabilityMeasure η]
    (hb : ∀ᵐ h ∂η, -1 ≤ h ∧ h ≤ 1) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) :
    let μ := Measure.pi (fun _ : Fin d => η)
    let V := fun (t : ℝ) (h : Fin d → ℝ) =>
      ((∏ i, (1+t*h i)) + t*(∏ i, (1-h i)))/(1+t)
    let D := fun (t : ℝ) (h : Fin d → ℝ) =>
      ((1+t)*(∑ i, (∏ j ∈ Finset.univ.erase i, (1+t*h j))*h i) +
        (∏ i, (1-h i)) - ∏ i, (1+t*h i)) / (1+t)^2
    HasDerivAt (fun t => ∫ h, V t h * Real.log (V t h) ∂μ)
      (∫ h, D θ h * (Real.log (V θ h) + 1) ∂μ) θ := by
  dsimp only
  let μ := Measure.pi (fun _ : Fin d => η)
  let V := fun (t : ℝ) (h : Fin d → ℝ) =>
    ((∏ i, (1+t*h i)) + t*(∏ i, (1-h i)))/(1+t)
  let D := fun (t : ℝ) (h : Fin d → ℝ) =>
    ((1+t)*(∑ i, (∏ j ∈ Finset.univ.erase i, (1+t*h j))*h i) +
      (∏ i, (1-h i)) - ∏ i, (1+t*h i)) / (1+t)^2
  let F := fun t h => V t h * Real.log (V t h)
  let F' := fun t h => D t h * (Real.log (V t h)+1)
  let T := (1+θ)/2
  let s := Ioo (θ/2) T
  have hT : T < 1 := by dsimp [T]; linarith
  have hTs : θ ∈ s := by dsimp [s,T]; constructor <;> linarith
  have hs : s ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hTs
  have hrange : ∀ t ∈ s, 0 ≤ t ∧ t ≤ T := by
    intro t ht
    dsimp [s] at ht
    constructor <;> linarith [ht.1,ht.2]
  have hgood : ∀ᵐ h ∂μ, ∀ i, -1 ≤ h i ∧ h i ≤ 1 := by
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi (fun _ : Fin d => hb)
  obtain ⟨B,hB,hbound⟩ := hardcore_entropy_uniform_bound d T hT
  have hFmeas (t : ℝ) : Measurable (F t) := by
    dsimp [F,V]
    fun_prop
  have hF'meas (t : ℝ) : Measurable (F' t) := by
    dsimp [F',D,V]
    fun_prop
  have hFint : Integrable (F θ) μ := by
    apply Integrable.of_bound (hFmeas θ).aestronglyMeasurable B
    filter_upwards [hgood] with h hh
    exact (hbound θ h (hrange θ hTs).1 (hrange θ hTs).2 hh).1
  have hFdif : ∀ᵐ h ∂μ, ∀ t ∈ s, HasDerivAt (fun t => F t h) (F' t h) t := by
    filter_upwards [hgood] with h hh
    intro t ht
    have ht0 := (hrange t ht).1
    have ht1 : t < 1 := lt_of_le_of_lt (hrange t ht).2 hT
    have hd : 1+t ≠ 0 := by linarith
    have hp (i : Fin d) : 0 < 1+t*h i := by
      nlinarith [mul_nonneg ht0 (show 1+h i ≥ 0 by linarith [(hh i).1])]
    have hp' : 0 < ∏ i, (1+t*h i) := Finset.prod_pos (fun i _ => hp i)
    have hq : 0 ≤ ∏ i, (1-h i) := Finset.prod_nonneg (fun i _ => by linarith [(hh i).2])
    have hv : V t h ≠ 0 := by
      dsimp [V]
      apply ne_of_gt
      exact div_pos (add_pos_of_pos_of_nonneg hp' (mul_nonneg ht0 hq)) (by linarith)
    exact hardcore_vertex_entropy_derivative h t hd hv
  have hFbound : ∀ᵐ h ∂μ, ∀ t ∈ s, ‖F' t h‖ ≤ B := by
    filter_upwards [hgood] with h hh
    intro t ht
    exact (hbound t h (hrange t ht).1 (hrange t ht).2 hh).2
  have hfin : Integrable (fun _ : Fin d → ℝ => B) μ := integrable_const B
  have result := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := F') (bound := fun _ => B) hs
    (Filter.Eventually.of_forall (fun t => (hFmeas t).aestronglyMeasurable)) hFint
    (hF'meas θ).aestronglyMeasurable hFbound hfin hFdif
  exact result.2
