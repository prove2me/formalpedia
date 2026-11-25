-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.Base0.mp_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:17:47.602864+00:00
-- url     : https://prove2.me/submissions/6e6d541d-260e-4808-b62a-306ea882b754

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_IntegrableUnitIndicator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.Base0
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (h : Matrix ι ι ℂ) (hu : h.conjTranspose * h = 1) :
    MeasurePreserving (fun y : ι → ℂ => h.mulVec y) volume volume := by
  let L : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) := (Matrix.toLin' h).restrictScalars ℝ
  have hfun : (fun y : ι → ℂ => h.mulVec y) = ⇑L := by
    funext y
    first
    | rfl
    | simp [L, Matrix.toLin'_apply]
  have hdetC : Complex.normSq h.det = 1 := by
    have h1 := congrArg Matrix.det hu
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h1
    have h2 : ((Complex.normSq h.det : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      first
      | exact h1
      | (rw [starRingEnd_apply]; exact h1)
      | simpa using h1
    exact_mod_cast h2
  have hdet : LinearMap.det L = 1 := by
    first
    | (rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, hdetC])
    | (show LinearMap.det ((Matrix.toLin' h).restrictScalars ℝ) = 1
       rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, hdetC])
  have hmeas : Measurable (fun y : ι → ℂ => h.mulVec y) := by
    rw [hfun]
    exact L.continuous_of_finiteDimensional.measurable
  refine ⟨hmeas, ?_⟩
  rw [hfun]
  first
  | (rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; norm_num), hdet]; simp)
  | (rw [Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := volume) (by rw [hdet]; norm_num), hdet]; simp)
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0
