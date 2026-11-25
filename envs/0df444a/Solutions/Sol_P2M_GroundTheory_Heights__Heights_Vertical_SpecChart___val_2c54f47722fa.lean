-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___val_2c54f47722fa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:31:38.048062+00:00
-- url     : https://prove2.me/submissions/b070ff2a-1b8b-4b72-8376-1341ac103d65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartIso
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_solve_inl_544ff5ad2773
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_solve_inr_ae6d804b71ce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_secB_secForm_18ac93789522
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_secB_chartForm_dbede3e2003d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___X_04365f072597
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___cx_89ebc424d343
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___cinv_mul_adb95d831303

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Vertical.SpecChart
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
  (j : Fin n)
variable (W : Ideal (MvPolynomial (Fin n) (𝓞 K)))
variable {I W}
variable {v : HeightOneSpectrum (𝓞 K)}
variable (𝔫 : Ideal (SecB e I v)) [𝔫.IsPrime]
variable {e j 𝔫}
namespace GroundTheory.Heights₂.Heights.Vertical.SpecChart
theorem _root_.solution (hj : toSecB e I v (X j) ∉ 𝔫) (p : Par e n) : Φ hj (val e I j p) = parB e 𝔫 p := by
  have hc := Φ_cinv_mul hj
  rcases p with ⟨i, l⟩ | l
  · by_cases hl : l = j
    · subst hl
      have h := congrArg (algebraMap (SecB e I v) (Localization.AtPrime 𝔫)) (secB_secForm e (I := I) (v := v) i)
      rw [map_sum, map_zero, Fintype.sum_eq_add_sum_subtype_ne _ l] at h
      simp only [map_mul] at h
      simp only [val, dite_true, map_neg, map_mul, map_sum, Φ_X, Φ_cx, FreePar.val, parB]
      exact solve_inl (L := Localization.AtPrime 𝔫) h hc
    · simp only [val, hl, dite_false, Φ_X, FreePar.val]
  · by_cases hl : l = j
    · subst hl
      have h := congrArg (algebraMap (SecB e I v) (Localization.AtPrime 𝔫)) (secB_chartForm e (I := I) (v := v))
      rw [map_sum, map_one, Fintype.sum_eq_add_sum_subtype_ne _ l] at h
      simp only [map_mul] at h
      simp only [val, dite_true, map_sub, map_one, map_mul, map_sum, Φ_X, Φ_cx, FreePar.val, parB]
      exact solve_inr (L := Localization.AtPrime 𝔫) h hc
    · simp only [val, hl, dite_false, Φ_X, FreePar.val]
end GroundTheory.Heights₂.Heights.Vertical.SpecChart
