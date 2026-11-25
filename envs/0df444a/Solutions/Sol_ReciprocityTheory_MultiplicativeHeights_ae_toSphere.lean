-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.ae_toSphere
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:37:54.19628+00:00
-- url     : https://prove2.me/submissions/c224c480-a5d9-447f-bfb7-551abf47cea1

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ae_eval_ne_zero_linear
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_eval_blockScale_eq_prod_pow_mul
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_blockCoordEquiv_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (B n : ℕ) (a : Fin B → ℕ) (F : MvPolynomial (Fin B × Fin n) ℂ)
    (hF0 : F ≠ 0) (hF : IsMultiHomogeneous a F) :
    ∀ᵐ z ∂(Measure.pi fun _ : Fin B => (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere),
      MvPolynomial.eval (blockPoint z) F ≠ 0 := by
  set E := EuclideanSpace ℂ (Fin n)
  set νS := (volume : Measure E).toSphere
  set ρ := Measure.volumeIoiPow (Module.finrank ℝ E - 1)
  set Z : Set (Fin B → sphere (0 : E) 1) := {z | MvPolynomial.eval (blockPoint z) F = 0}
  have hZ : MeasurableSet Z := by
    have : Continuous fun z : Fin B → sphere (0 : E) 1 => MvPolynomial.eval (blockPoint z) F := by
      refine (MvPolynomial.continuous_eval F).comp ?_
      refine continuous_pi fun p => ?_
      unfold blockPoint spherePoint
      fun_prop
    exact this.measurable (measurableSet_singleton 0)
  have : (Measure.pi fun _ : Fin B => (volume : Measure E)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have : IsFiniteMeasure νS := by show IsFiniteMeasure ((volume : Measure E).toSphere); infer_instance
  have : SigmaFinite ρ := by show SigmaFinite (Measure.volumeIoiPow (Module.finrank ℝ E - 1)); infer_instance
  have hlin : ∀ᵐ y ∂(Measure.pi fun _ : Fin B => (volume : Measure E)),
      MvPolynomial.eval (blockCoordEquiv B n y) F ≠ 0 :=
    ae_eval_ne_zero_linear _ (blockCoordEquiv B n) F hF0
  set S : Set (Fin B → E) := {y | MvPolynomial.eval (blockCoordEquiv B n y) F = 0}
  have hS0 : (Measure.pi fun _ : Fin B => (volume : Measure E)) S = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hlin] with y hy
    exact hy
  have hSm : MeasurableSet S := by
    have : Continuous fun y : Fin B → E => MvPolynomial.eval (blockCoordEquiv B n y) F := by
      refine (MvPolynomial.continuous_eval F).comp ?_
      exact (blockCoordEquiv B n).toContinuousLinearEquiv.continuous
    exact this.measurable (measurableSet_singleton 0)
  have h1 := Measure.measurePreserving_homeomorphUnitSphereProd (volume : Measure E)
  have hprodSF : SigmaFinite (νS.prod ρ) := inferInstance
  have hT := measurePreserving_pi (hν := fun _ => hprodSF)
    (fun _ : Fin B => (volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E))
    (fun _ => νS.prod ρ) (fun _ => h1)
  have hA := measurePreserving_arrowProdEquivProdArrow (sphere (0 : E) 1) (Set.Ioi (0 : ℝ)) (Fin B)
    (fun _ => νS) (fun _ => ρ)
  set A := MeasurableEquiv.arrowProdEquivProdArrow (sphere (0 : E) 1) (Set.Ioi (0 : ℝ)) (Fin B)
  set T : (Fin B → ({0}ᶜ : Set E)) → (Fin B → sphere (0 : E) 1 × Set.Ioi (0 : ℝ)) :=
    fun x b => homeomorphUnitSphereProd E (x b)
  have hW : MeasurableSet (Z ×ˢ (Set.univ : Set (Fin B → Set.Ioi (0 : ℝ)))) :=
    hZ.prod MeasurableSet.univ
  have hAW : MeasurableSet (A ⁻¹' (Z ×ˢ Set.univ)) := A.measurable hW
  have e1 := Measure.prod_prod (μ := Measure.pi fun _ : Fin B => νS)
    (ν := Measure.pi fun _ : Fin B => ρ) Z Set.univ
  rw [← hA.measure_preimage hW.nullMeasurableSet, ← hT.measure_preimage hAW.nullMeasurableSet] at e1
  set G : (Fin B → ({0}ᶜ : Set E)) → (Fin B → E) := fun x b => (x b : E)
  have hsub : T ⁻¹' (A ⁻¹' (Z ×ˢ Set.univ)) ⊆ G ⁻¹' S := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true] at hx
    have hx' : MvPolynomial.eval (blockPoint fun b => (homeomorphUnitSphereProd E (x b)).1) F = 0 := by
      simpa [A, T, Z, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow] using hx
    have hcoord : blockCoordEquiv B n (G x) = fun p => ((‖(x p.1 : E)‖ : ℝ) : ℂ) *
        blockPoint (fun b => (homeomorphUnitSphereProd E (x b)).1) p := by
      funext p
      have hne : ‖(x p.1 : E)‖ ≠ 0 := norm_ne_zero_iff.2 (x p.1).2
      simp only [blockCoordEquiv_apply, G, blockPoint, spherePoint, homeomorphUnitSphereProd_apply_fst_coe]
      rw [← Complex.coe_smul, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc,
        ← Complex.ofReal_mul, mul_inv_cancel₀ hne, Complex.ofReal_one, one_mul]
    show MvPolynomial.eval (blockCoordEquiv B n (G x)) F = 0
    have hsc := eval_blockScale_eq_prod_pow_mul a F hF (fun b => ((‖(x b : E)‖ : ℝ) : ℂ))
      (blockPoint (fun b => (homeomorphUnitSphereProd E (x b)).1))
    rw [hcoord, hsc, hx', mul_zero]
  have hmap : ∀ _ : Fin B, ((volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E)).map
      Subtype.val = (volume : Measure E).restrict {0}ᶜ :=
    fun _ => map_comap_subtype_coe (measurableSet_singleton 0).compl _
  have hmSF : ∀ i : Fin B, SigmaFinite
      (((volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E)).map Subtype.val) := by
    intro i; rw [hmap i]; infer_instance
  have hG : (Measure.pi fun _ : Fin B =>
      (volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E)).map G =
      Measure.pi fun _ : Fin B => (volume : Measure E).restrict {0}ᶜ := by
    rw [Measure.pi_map_pi (hμ := hmSF) (fun _ => measurable_subtype_coe.aemeasurable)]
    exact congrArg _ (funext hmap)
  have hGm : Measurable G := measurable_pi_lambda _ fun b => measurable_subtype_coe.comp
    (measurable_pi_apply b)
  have hzero : (Measure.pi fun _ : Fin B =>
      (volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E))
      (T ⁻¹' (A ⁻¹' (Z ×ˢ Set.univ))) = 0 := by
    refine measure_mono_null hsub ?_
    rw [← Measure.map_apply hGm hSm, hG, ← Measure.restrict_pi_pi]
    exact nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans hS0.le)
  have hρ : ρ Set.univ ≠ 0 := by
    intro h
    have h2 := measure_mono_null (Set.subset_univ (Set.Iio (⟨1, by norm_num⟩ : Set.Ioi (0 : ℝ)))) h
    have h3 := Measure.volumeIoiPow_apply_Iio (Module.finrank ℝ E - 1) ⟨1, by norm_num⟩
    rw [show ρ (Set.Iio ⟨1, by norm_num⟩) = _ from h3] at h2
    rw [ENNReal.ofReal_eq_zero] at h2
    have h4 : (0 : ℝ) < (1 : ℝ) ^ (Module.finrank ℝ E - 1 + 1) / ((Module.finrank ℝ E - 1 : ℕ) + 1) := by
      positivity
    exact absurd h2 (not_le.2 h4)
  have hpiρ : (Measure.pi fun _ : Fin B => ρ) Set.univ ≠ 0 := by
    rw [Measure.pi_univ]
    exact Finset.prod_ne_zero_iff.2 fun _ _ => hρ
  rw [hzero] at e1
  have hZ0 : (Measure.pi fun _ : Fin B => νS) Z = 0 := by
    rcases mul_eq_zero.1 e1.symm with h | h
    · exact h
    · exact absurd h hpiρ
  rw [measure_eq_zero_iff_ae_notMem] at hZ0
  filter_upwards [hZ0] with z hz
  exact hz
end ReciprocityTheory.MultiplicativeHeights
