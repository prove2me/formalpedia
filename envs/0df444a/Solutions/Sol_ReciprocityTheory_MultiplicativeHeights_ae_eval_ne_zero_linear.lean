-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.ae_eval_ne_zero_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:30:45.429781+00:00
-- url     : https://prove2.me/submissions/4d7621de-8baa-4ee0-b45f-eb377a0775b1

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_ae_eval_ne_zero_of_ne_zero_fin

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
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] {ι : Type*} [Fintype ι] (L : V ≃ₗ[ℂ] (ι → ℂ))
    (f : MvPolynomial ι ℂ) (hf : f ≠ 0) :
    ∀ᵐ x ∂μ, MvPolynomial.eval (L x) f ≠ 0 := by
  set e := Fintype.equivFin ι
  set g := MvPolynomial.rename e f
  have hg : g ≠ 0 := by
    intro h
    apply hf
    exact MvPolynomial.rename_injective _ e.injective (by rw [map_zero]; exact h)
  set L' : V ≃ₗ[ℂ] (Fin (Fintype.card ι) → ℂ) := L.trans (LinearEquiv.funCongrLeft ℂ ℂ e.symm)
  have hL' : ∀ x, MvPolynomial.eval (L' x) g = MvPolynomial.eval (L x) f := by
    intro x
    have hc : (L' x : Fin (Fintype.card ι) → ℂ) ∘ e = L x := by
      funext i
      simp [L', LinearEquiv.funCongrLeft_apply]
    simp only [g, MvPolynomial.eval_rename, hc]
  have hac : μ.map L' ≪ volume := Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have h1 : ∀ᵐ y ∂(μ.map L'), MvPolynomial.eval y g ≠ 0 :=
    hac.ae_le (ae_eval_ne_zero_of_ne_zero_fin _ g hg)
  have hmeasL : Measurable L' := L'.toContinuousLinearEquiv.continuous.measurable
  have hmeasS : MeasurableSet {y : Fin (Fintype.card ι) → ℂ | MvPolynomial.eval y g ≠ 0} :=
    (MvPolynomial.continuous_eval g).measurable (measurableSet_singleton 0).compl
  rw [ae_map_iff hmeasL.aemeasurable hmeasS] at h1
  filter_upwards [h1] with x hx
  rwa [← hL']
end ReciprocityTheory.MultiplicativeHeights
