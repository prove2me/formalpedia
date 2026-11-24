-- Prove2me | solution 1 for PositivityTheory.RgUd.T.Desc.SLF.isUnimod_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:10:25.142539+00:00
-- url     : https://prove2.me/submissions/b06c1e13-23cc-4b9f-98d9-9fa8276a8888

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_Descent_SliceVanishing_IsUnimodOfEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MeasureTheory.Measure
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc PositivityTheory.RgUd.T.Desc.SLF
namespace PositivityTheory.RgUd.T.Desc.SLF
theorem _root_.solution {G₁ G₂ : Type*} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
    [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂] (φ : G₁ ≃ₜ* G₂)
    (h : PositivityTheory.PfBern.Frob.IsUnimod G₂) : PositivityTheory.PfBern.Frob.IsUnimod G₁ := by
  intro g
  have hg : modularCharacterFun (φ g) = 1 := h (φ g)
  show modularCharacterFun g = 1
  borelize G₁ G₂
  let μ₂ : Measure G₂ := haar
  have hme : MeasurableEmbedding (φ.symm : G₂ → G₁) := φ.symm.toHomeomorph.measurableEmbedding
  let μ₁ : Measure G₁ := map (φ.symm : G₂ → G₁) μ₂
  haveI : IsHaarMeasure μ₁ := ContinuousMulEquiv.isHaarMeasure_map μ₂ φ.symm
  rw [modularCharacterFun_eq_haarScalarFactor μ₁ g]
  rw [modularCharacterFun_eq_haarScalarFactor μ₂ (φ g)] at hg
  obtain ⟨f, hfc, hf0, hf1⟩ := exists_continuous_nonneg_pos (1 : G₁)
  let f₂ : G₂ → ℝ := fun y => f (φ.symm y)
  have hf₂c : Continuous f₂ := f.continuous.comp φ.symm.continuous
  have hf₂s : HasCompactSupport f₂ := hfc.comp_homeomorph φ.symm.toHomeomorph
  have I1 : ∫ x, f x ∂μ₁ = ∫ y, f₂ y ∂μ₂ := hme.integral_map _
  have I2 : ∫ x, f x ∂(map (· * g) μ₁) = ∫ y, f₂ y ∂(map (· * φ g) μ₂) := by
    rw [integral_map (measurable_mul_const g).aemeasurable f.continuous.aestronglyMeasurable,
      show μ₁ = map (φ.symm : G₂ → G₁) μ₂ from rfl, hme.integral_map,
      integral_map (measurable_mul_const (φ g)).aemeasurable hf₂c.aestronglyMeasurable]
    congr 1
    funext y
    simp only [f₂, map_mul, ContinuousMulEquiv.symm_apply_apply]
  have hpos : ∫ x, f x ∂μ₁ ≠ 0 :=
    (f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc hf0 hf1).ne'
  have hpos₂ : ∫ y, f₂ y ∂μ₂ ≠ 0 := by
    rw [← I1]
    exact hpos
  have hg' : ((haarScalarFactor (map (· * φ g) μ₂) μ₂ : NNReal) : ℝ) = 1 := by
    rw [hg]
    rfl
  rw [haarScalarFactor_eq_integral_div _ _ hf₂c hf₂s hpos₂] at hg'
  apply NNReal.coe_injective
  rw [haarScalarFactor_eq_integral_div _ _ f.continuous hfc hpos, I2, I1, hg', NNReal.coe_one]
end PositivityTheory.RgUd.T.Desc.SLF
