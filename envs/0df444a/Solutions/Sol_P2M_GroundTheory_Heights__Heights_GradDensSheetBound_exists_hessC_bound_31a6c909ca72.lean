-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GradDensSheetBound_exists_hessC_bound_31a6c909ca72
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:27:57.215684+00:00
-- url     : https://prove2.me/submissions/d2fafd4e-5291-42bf-85d9-226af50aa4f1

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGradDensSheetBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradDensSheetBound_hessC_pm_posSemidef_6dd07111738d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.GradDensSheetBound
namespace GroundTheory.Heights₂.Heights.GradDensSheetBound
theorem _root_.solution {n d : ℕ} (φ : Fin d → (Fin n → ℂ) → ℝ) (U K : Set (Fin n → ℂ))
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (hφ : ∀ i, ContDiffOn ℝ 2 (φ i) U) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ i,
      ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - hessC (φ i) x).PosSemidef ∧
        (hessC (φ i) x + (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
  have hcont : ContinuousOn (fun x => ∑ i, ‖fderiv ℝ (fderiv ℝ (φ i)) x‖) U :=
    continuousOn_finsetSum _ fun i _ =>
      (((hφ i).fderiv_of_isOpen hU (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hU
        le_rfl).norm
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hcont.mono hKU)
  refine ⟨max M 0 / 2 + 1, by positivity, fun x hx i => ?_⟩
  have h2 : ContDiffAt ℝ 2 (φ i) x := (hφ i).contDiffAt (hU.mem_nhds (hKU hx))
  have hMi : ‖fderiv ℝ (fderiv ℝ (φ i)) x‖ ≤ max M 0 :=
    (((Finset.single_le_sum (f := fun i => ‖fderiv ℝ (fderiv ℝ (φ i)) x‖)
      (fun i _ => ContinuousLinearMap.opNorm_nonneg _) (Finset.mem_univ i)).trans
        ((le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hM x hx))))).trans
      (le_max_left _ _)
  exact hessC_pm_posSemidef (φ i) x h2 _ _ hMi (by linarith)
end GroundTheory.Heights₂.Heights.GradDensSheetBound
