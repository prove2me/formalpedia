-- Prove2me | solution 1 for ReciprocityTheory.PTheta.thetaMTest_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:29:04.76123+00:00
-- url     : https://prove2.me/submissions/3d72487e-a00e-48cd-b1b9-5f48bdbc1bcf

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere
import Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_quad_lower
import Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_summable_pi_prod
import Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_summable_gauss
import Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_term_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
open ReciprocityTheory ReciprocityTheory.PTheta
open sphereQuadraticPositivity
namespace ReciprocityTheory.PTheta
theorem _root_.solution : ThetaMTestStatement := by
  intro ι _ a K hK hKd
  classical
  let Mf : (ι → ℂ) × (ι → ι → ℂ) → Matrix ι ι ℝ :=
    fun p => (of p.2).map Complex.im + ((of p.2).map Complex.im)ᵀ
  have hc : Continuous Mf := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (Complex.continuous_im.comp ((continuous_apply j).comp
      ((continuous_apply i).comp continuous_snd))).add
      (Complex.continuous_im.comp ((continuous_apply i).comp
        ((continuous_apply j).comp continuous_snd)))
  obtain ⟨c, hc0, hcK⟩ := quad_lower Mf hc K hK (fun p hp => hKd p hp)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := fun p => p.1) continuous_fst.continuousOn
  refine ⟨fun l => ∏ i, Real.exp (-((Real.pi * c / 2) / 4) * (l i : ℝ) ^ 2 +
      ((2 * Real.pi * max C 0) ^ 2 / (2 * (Real.pi * c / 2)) + (Real.pi * c / 2) / 2 * a i ^ 2)),
    ?_, ?_⟩
  · exact summable_pi_prod (g := fun i k => Real.exp (-((Real.pi * c / 2) / 4) * (k : ℝ) ^ 2 +
      ((2 * Real.pi * max C 0) ^ 2 / (2 * (Real.pi * c / 2)) + (Real.pi * c / 2) / 2 * a i ^ 2)))
      (fun i k => (Real.exp_pos _).le) (fun i => summable_gauss _ _ (by positivity))
  · intro b p hp l
    refine term_bound a b p.1 (of p.2) l c (max C 0) hc0 (le_max_right _ _) (fun i => ?_)
      (fun x => hcK p hp x)
    have h1 : ‖p.1‖ ≤ C := hC p hp
    calc |(p.1 i).im| ≤ ‖p.1 i‖ := Complex.abs_im_le_norm _
      _ ≤ ‖p.1‖ := norm_le_pi_norm p.1 i
      _ ≤ C := h1
      _ ≤ max C 0 := le_max_left _ _
end ReciprocityTheory.PTheta
