-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_proof_12c2b424ae99
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:08:39.14351+00:00
-- url     : https://prove2.me/submissions/5ab65372-9da8-4ea2-9112-fa49953143e8

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLeibniz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepRankOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeDeepRankOne
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_mdisc_vecMulVec_be2ffc9f6b9b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_mdisc_cons_sum_a97f8b68dabd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_hessC_euclPot_comp_54803d612c25
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_hessC_logAbsSq_sq_half_b80bf96c7606
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_det_rows_eq_deepJacDet_32c0a8f69f5c
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_hessC_congr__aa19fc468bd1
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood


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
open MvPolynomial Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.TubeDeepRankOne
namespace GroundTheory.Heights₂.Heights.TubeDeepRankOne
theorem _root_.solution : TubeDeepRankOne.Statement := by
  intro n d A P U s y hU hy hsd hAs hP
  have hsa : AnalyticAt ℂ s y := analyticAt_pi_iff.2 fun j =>
    ReciprocityTheory.AnForm.Osgood.osgood (d + 1) U (fun y => s y j) hU (differentiableOn_pi.1 hsd j) y hy
  set a : Fin (d + 1) → ℂ := fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P with ha
  set b : Fin n → Fin (d + 1) → ℂ := fun m j => jacC s y m j with hb
  have h0 : hessC ((fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) ∘ s) y = vecMulVec a (star a) := by
    have hev : ((fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) ∘ s) =ᶠ[𝓝 y] fun z => logAbsSq P z ^ 2 / 2 := by
      filter_upwards [hU.mem_nhds hy] with z hz
      simp only [Function.comp_apply, hAs z hz]
    rw [hessC_congr' hev, hessC_logAbsSq_sq_half P y hP]
  have h1 : hessC (euclPot ∘ s) y = ∑ m, vecMulVec (b m) (star (b m)) := hessC_euclPot_comp s y hsa
  have hH : (fun k => hessC (vecCons (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) (fun _ => euclPot) k ∘ s) y) =
      (Fin.cons (vecMulVec a (star a)) (fun _ => ∑ m, vecMulVec (b m) (star (b m))) :
        Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simpa using h0
    · simpa using h1
  have hI : ∀ I : Fin d → Fin n,
      (Fin.cons (vecMulVec a (star a)) (fun i => vecMulVec (b (I i)) (star (b (I i)))) :
        Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) =
      fun k => vecMulVec ((Fin.cons a (fun i => b (I i)) : Fin (d + 1) → Fin (d + 1) → ℂ) k)
        (star ((Fin.cons a (fun i => b (I i)) : Fin (d + 1) → Fin (d + 1) → ℂ) k)) := by
    intro I
    funext k
    refine Fin.cases ?_ (fun i => ?_) k <;> simp
  have hdet : ∀ I : Fin d → Fin n,
      (Matrix.of (Fin.cons a (fun i => b (I i)) : Fin (d + 1) → Fin (d + 1) → ℂ)).det =
        (eval y P)⁻¹ * deepJacDet P s I y := fun I =>
    det_rows_eq_deepJacDet P s y (hsd.differentiableAt (hU.mem_nhds hy)) I
  unfold ReciprocityTheory.AnForm.maDens
  rw [hH, mdisc_cons_sum]
  simp_rw [hI, mdisc_vecMulVec, hdet]
  rw [Complex.re_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  have hf : ((d + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast (d + 1).factorial_ne_zero
  have hre : ((1 / ((d + 1).factorial : ℂ)) *
      (Complex.normSq ((eval y P)⁻¹ * deepJacDet P s I y) : ℂ)).re =
      Complex.normSq ((eval y P)⁻¹ * deepJacDet P s I y) / ((d + 1).factorial : ℝ) := by
    rw [show (1 / ((d + 1).factorial : ℂ)) = (((1 / ((d + 1).factorial : ℝ)) : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  rw [hre, map_mul, map_inv₀, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have hp : ‖eval y P‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hP)
  field_simp
end GroundTheory.Heights₂.Heights.TubeDeepRankOne
