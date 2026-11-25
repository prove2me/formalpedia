-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.stepP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:25:07.650857+00:00
-- url     : https://prove2.me/submissions/128c80a8-c457-41d1-b244-4791e206465b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanBn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_TileIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_mem_P
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_L_le_P
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_fdP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_tile_average
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory MeasureTheory.Measure Complex Module Set Submodule
noncomputable section
variable {E : Type} [Field E] [NumberField E]
section PiR
end PiR
private theorem setAverage_preimage_linearEquiv_comp (X : PT E) (f : Vsp X.dim ≃ₗ[ℝ] Vsp X.dim) (g : Vsp X.dim → ℝ)
    (hg : Continuous g) (S : Set (Vsp X.dim)) (hS : MeasurableSet S) :
    ⨍ x in f ⁻¹' S, g (f x) ∂(volume : Measure (Vsp X.dim)) = ⨍ x in S, g x ∂volume := by
  have hdet : LinearMap.det (f : Vsp X.dim →ₗ[ℝ] Vsp X.dim) ≠ 0 := (LinearEquiv.isUnit_det' f).ne_zero
  have hmap : Measure.map f volume = ENNReal.ofReal |(LinearMap.det (f : Vsp X.dim →ₗ[ℝ] Vsp X.dim))⁻¹| •
      (volume : Measure (Vsp X.dim)) :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet
  have hfm : Measurable f := (LinearMap.continuous_of_finiteDimensional (f : Vsp X.dim →ₗ[ℝ] Vsp X.dim)).measurable
  have h1 : ∫ x in f ⁻¹' S, g (f x) ∂volume = ∫ x in S, g x ∂(Measure.map f volume) :=
    (setIntegral_map hS hg.aestronglyMeasurable hfm.aemeasurable).symm
  have h2 : volume (f ⁻¹' S) = (Measure.map f volume) S := (Measure.map_apply hfm hS).symm
  have hc0 : (ENNReal.ofReal |(LinearMap.det (f : Vsp X.dim →ₗ[ℝ] Vsp X.dim))⁻¹|).toReal ≠ 0 := by
    rw [ENNReal.toReal_ofReal (abs_nonneg _)]
    exact abs_ne_zero.mpr (inv_ne_zero hdet)
  rw [setAverage_eq, setAverage_eq, h1, measureReal_def, h2, hmap, Measure.restrict_smul, integral_smul_measure,
    Measure.smul_apply, smul_eq_mul (α := ENNReal), ENNReal.toReal_mul, ← measureReal_def]
  simp only [smul_eq_mul, mul_inv]
  linear_combination ((volume.real S)⁻¹ * ∫ x in S, g x) * inv_mul_cancel₀ hc0
section Q
end Q
end
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory MeasureTheory.Measure Complex Module Set Submodule
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
theorem _root_.solution : StepP := by
  intro E _ _ X q π hq hπ g hg hper
  have hgp : Continuous fun w => g (π w) := hg.comp (LinearMap.continuous_of_finiteDimensional π)
  rw [tile_average (μ := volume) X.b (bP X hq hπ) (L_le_P X hq hπ) (fun w => g (π w)) hgp ?_]
  · rw [fdP]
    exact setAverage_preimage_linearEquiv_comp X (piR X hq hπ) g hg _ (ZSpan.fundamentalDomain_measurableSet X.b)
  · intro β hβ x
    have h1 := (mem_P X hq hπ β).mp hβ
    simp only [map_add]
    exact hper _ h1 _
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
