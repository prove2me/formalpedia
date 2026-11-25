-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TubeFormComparison_exists_hessC_bound_adf0c8df653f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:56:50.747519+00:00
-- url     : https://prove2.me/submissions/7b099e95-a24e-4a72-935a-c2b291202c49

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeFormCompare
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_levi_neg_eba6193b69bd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_hessC_neg_f4567154ff3b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeFormComparison_posSemidef_hessC_add_73f8e49e0713
import Theorems.Thm_ReciprocityTheory_AnForm_continuousOn_levi
import Theorems.Thm_ReciprocityTheory_AnForm_levi_smul_dir
import Theorems.Thm_ReciprocityTheory_AnForm_levi_zero


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
open MvPolynomial Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.TubeFormComparison
namespace GroundTheory.Heights₂.Heights.TubeFormComparison
theorem _root_.solution {N m : ℕ} (φ : Fin m → (Fin N → ℂ) → ℝ) (K : Set (Fin N → ℂ))
    (hK : IsCompact K) (U : Fin m → Set (Fin N → ℂ)) (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K ⊆ U i)
    (hφ : ∀ i, ContDiffOn ℝ 2 (φ i) (U i)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ i, ∀ x ∈ K, (hessC (φ i) x + (c : ℂ) • 1).PosSemidef ∧
      (-hessC (φ i) x + (c : ℂ) • 1).PosSemidef := by
  have hb : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ w, |levi (φ i) x w| ≤ C * ‖w‖ ^ 2 := by
    intro i
    have hS : IsCompact (K ×ˢ Metric.sphere (0 : Fin N → ℂ) 1) := hK.prod (isCompact_sphere 0 1)
    obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn
      ((continuousOn_levi (hU i) (hφ i)).mono (Set.prod_mono (hKU i) (Set.subset_univ _)))
    refine ⟨max C 0, le_max_right _ _, fun x hx w => ?_⟩
    rcases eq_or_ne w 0 with rfl | hw
    · simp [levi_zero]
    have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
    have hw' : w = ‖w‖ • (‖w‖⁻¹ • w) := by rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have hu : ‖‖w‖⁻¹ • w‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn.ne']
    have hb := hC (x, ‖w‖⁻¹ • w) ⟨hx, mem_sphere_zero_iff_norm.2 hu⟩
    rw [Real.norm_eq_abs] at hb
    calc |levi (φ i) x w| = |levi (φ i) x (‖w‖ • (‖w‖⁻¹ • w))| := by rw [← hw']
      _ = ‖w‖ ^ 2 * |levi (φ i) x (‖w‖⁻¹ • w)| := by
        rw [levi_smul_dir, abs_mul, abs_of_nonneg (sq_nonneg _)]
      _ ≤ ‖w‖ ^ 2 * max C 0 := by gcongr; exact hb.trans (le_max_left _ _)
      _ = _ := by ring
  choose C hC0 hC using hb
  refine ⟨∑ i, C i, Finset.sum_nonneg fun i _ => hC0 i, fun i x hx => ?_⟩
  have hCi : C i ≤ ∑ i, C i := Finset.single_le_sum (fun i _ => hC0 i) (Finset.mem_univ i)
  have hx2 : ContDiffAt ℝ 2 (φ i) x := (hφ i).contDiffAt ((hU i).mem_nhds (hKU i hx))
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => hC0 i
  refine ⟨posSemidef_hessC_add hx2 hsum fun w => ?_, ?_⟩
  · have h1 := (abs_le.1 (hC i x hx w)).1
    have h2 : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
    nlinarith
  · rw [← hessC_neg]
    refine posSemidef_hessC_add hx2.neg hsum fun w => ?_
    rw [levi_neg]
    have h1 := (abs_le.1 (hC i x hx w)).2
    have h2 : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
    nlinarith
end GroundTheory.Heights₂.Heights.TubeFormComparison
