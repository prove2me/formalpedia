-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_order_one_7eb3e896cbbb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:25:20.154927+00:00
-- url     : https://prove2.me/submissions/0c4b770e-c969-48ff-9159-922c997c7b81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_JetOfMonomialSumStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PJetOfMonomialSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_analyticAt_fderiv_apply_9b7cdfb9e7f9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_iteratedFDeriv_fderiv_apply_db1f68c7338c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_iteratedFDeriv_fderiv_diag_af2eaa2d2298
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_step_9cbe12202740

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
theorem _root_.solution {v : E → ℂ} (hv : AnalyticAt ℂ v x) (hv0 : v x = 0) (w : E) :
    ∀ (a : ℕ) (g : E → ℂ), AnalyticAt ℂ g x → (∀ k < a, iteratedFDeriv ℂ k g x = 0) →
      iteratedFDeriv ℂ (a + 1) (fun y => g y * v y) x (fun _ => w) =
        ((a : ℂ) + 1) * iteratedFDeriv ℂ a g x (fun _ => w) * fderiv ℂ v x w := by
  intro a
  induction a with
  | zero =>
    intro g hg _
    rw [step hg hv (fun k hk => absurd hk (Nat.not_lt_zero k)) w]
    simp [iteratedFDeriv_zero_apply, hv0]
    ring
  | succ a ih =>
    intro g hg hga
    have hdg := analyticAt_fderiv_apply hg w
    have hdga : ∀ k < a, iteratedFDeriv ℂ k (fun y => fderiv ℂ g y w) x = 0 := by
      intro k hk
      ext m
      rw [iteratedFDeriv_fderiv_apply hg, hga (k + 1) (by omega)]
      simp
    have e : (fun y => v y * fderiv ℂ g y w) = fun y => fderiv ℂ g y w * v y := by
      funext y
      ring
    rw [step hg hv hga w, e, ih _ hdg hdga, iteratedFDeriv_fderiv_diag hg]
    push_cast
    ring
end GroundTheory.Heights₂.Heights.EffectiveHS.JetOfMonomialSum
