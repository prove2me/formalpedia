-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_step_9cbe12202740
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:40:51.14706+00:00
-- url     : https://prove2.me/submissions/949d7ca6-3848-4723-9837-5d617b3ad875

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_JetOfMonomialSumStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PJetOfMonomialSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_analyticAt_fderiv_apply_9b7cdfb9e7f9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_top_mul_e04b522ebe3c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_iteratedFDeriv_fderiv_diag_af2eaa2d2298

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.EffectiveHS
open GroundTheory.Heights₂.Heights.EffectiveHS.JetOfMonomialSum
open Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {x : E}
namespace GroundTheory.Heights₂.Heights.EffectiveHS.JetOfMonomialSum
theorem _root_.solution {g v : E → ℂ} (hg : AnalyticAt ℂ g x) (hv : AnalyticAt ℂ v x) {a : ℕ}
    (hga : ∀ k < a, iteratedFDeriv ℂ k g x = 0) (w : E) :
    iteratedFDeriv ℂ (a + 1) (fun y => g y * v y) x (fun _ => w) =
      fderiv ℂ v x w * iteratedFDeriv ℂ a g x (fun _ => w) +
        iteratedFDeriv ℂ a (fun y => v y * fderiv ℂ g y w) x (fun _ => w) := by
  have hgv : AnalyticAt ℂ (fun y => g y * v y) x := hg.fun_mul hv
  rw [← iteratedFDeriv_fderiv_diag hgv]
  have heq : (fun y => fderiv ℂ (fun y => g y * v y) y w) =ᶠ[𝓝 x]
      fun y => g y * fderiv ℂ v y w + v y * fderiv ℂ g y w := by
    filter_upwards [hg.eventually_analyticAt, hv.eventually_analyticAt] with y hgy hvy
    rw [fderiv_fun_mul hgy.differentiableAt hvy.differentiableAt]
    simp [smul_eq_mul]
  have h1 := analyticAt_fderiv_apply hv w
  have h2 := analyticAt_fderiv_apply hg w
  rw [(heq.iteratedFDeriv ℂ a).eq_of_nhds,
    fun_iteratedFDeriv_add_apply (hg.fun_mul h1).contDiffAt (hv.fun_mul h2).contDiffAt,
    top_mul hg h1 hga]
  simp [smul_eq_mul]
end GroundTheory.Heights₂.Heights.EffectiveHS.JetOfMonomialSum
