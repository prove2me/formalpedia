-- Prove2me | solution 1 for PI.VolStabW.SdTestInfW.testEx_of_homeo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:13:53.08674+00:00
-- url     : https://prove2.me/submissions/356b0bfd-6696-4758-85a7-b6dd67f1f745

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensInfAll
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_RealCharacter
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdTestInf
import Theorems.Thm_PI_VolStabW_SdTestInfW_testEx_bichar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.SdTestInfW
open MeasureTheory Complex Filter Topology
open scoped RealInnerProductSpace FourierTransform SchwartzMap ContDiff
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
namespace PI.VolStabW.SdTestInfW
theorem _root_.solution {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → V → ℂ)
    (e : V ≃ₜ W) (he : ∀ x y, e (x + y) = e x + e y)
    (hL : ∀ x x' y, χ (x + x') y = χ x y * χ x' y) (hR : ∀ x y y', χ x (y + y') = χ x y * χ x y')
    (hn : ∀ x y, ‖χ x y‖ = 1) (hcL : ∀ y, Continuous fun x => χ x y)
    (hcR : ∀ x, Continuous (χ x)) : SdUniqW.TestEx μ χ := by
  let ea : V ≃+ W := AddEquiv.mk' e.toEquiv he
  have hs : ∀ u v : W, e.symm (u + v) = e.symm u + e.symm v := fun u v => ea.symm.map_add u v
  let ce : V ≃ₜ+ W :=
    { ea with continuous_toFun := e.continuous, continuous_invFun := e.symm.continuous }
  let em : V ≃ᵐ W := e.toMeasurableEquiv
  let μ' : Measure W := Measure.map em μ
  have : μ'.IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ ce
  let χ' : W → W → ℂ := fun x y => χ (e.symm x) (e.symm y)
  have hb : IsBichar χ' :=
    { addL := fun x x' y => by simp only [χ', hs, hL]
      addR := fun x y y' => by simp only [χ', hs, hR]
      norm1 := fun x y => hn _ _
      contL := fun y => (hcL _).comp e.symm.continuous
      contR := fun x => (hcR _).comp e.symm.continuous }
  obtain ⟨φ, hφc, hφs, hI, z, hz⟩ := testEx_bichar μ' hb
  have hT : ∀ y, ∫ x, φ (e x) * χ x y ∂μ = ∫ x, φ x * χ' x (e y) ∂μ' := by
    intro y
    rw [integral_map_equiv em]
    simp [χ', em]
  refine ⟨fun x => φ (e x), hφc.comp e.continuous, hφs.comp_homeomorph e, ?_, e.symm z, ?_⟩
  · show Integrable (fun y => ∫ x, φ (e x) * χ x y ∂μ) μ
    have e1 : (fun y => ∫ x, φ (e x) * χ x y ∂μ) = (fun y => ∫ x, φ x * χ' x y ∂μ') ∘ em :=
      funext hT
    rw [e1]
    exact (integrable_map_equiv em _).1 hI
  · show φ (e (-e.symm z)) ≠ 0
    have h1 : e (-e.symm z) = -z := by
      have := ea.map_neg (e.symm z)
      change e (-e.symm z) = -e (e.symm z) at this
      rw [this, e.apply_symm_apply]
    rw [h1]; exact hz
end PI.VolStabW.SdTestInfW
