-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.mp_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:15:24.148467+00:00
-- url     : https://prove2.me/submissions/2a504cf3-a561-43b8-8b25-b7ba5e9ae46a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermExpand
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MpUnitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.BL
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1) :
    MeasurePreserving (fun y : Fin N → ℂ => U *ᵥ y) volume volume := by
  set f : (Fin N → ℂ) →ₗ[ℝ] (Fin N → ℂ) := (Matrix.toLin' U).restrictScalars ℝ with hf
  have hfU : (fun y : Fin N → ℂ => U *ᵥ y) = ⇑f := by funext y; simp [hf, Matrix.toLin'_apply]
  have hn : ((Complex.normSq U.det : ℝ) : ℂ) = 1 := by
    have h := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
    rw [Complex.normSq_eq_conj_mul_self]; exact h
  have hdet : LinearMap.det f = 1 := by
    rw [hf, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]; exact_mod_cast hn
  rw [hfU]
  refine ⟨f.continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; norm_num), hdet]
  simp
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
