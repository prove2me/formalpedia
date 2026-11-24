-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_top_mul_e04b522ebe3c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:07:23.572821+00:00
-- url     : https://prove2.me/submissions/6eb25eea-50e1-43bb-84b8-7730238941c9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_JetOfMonomialSumStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PJetOfMonomialSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_vanish_one_4f1d6effb138
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_vanish_mul_2c201f8ce5c5

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
theorem _root_.solution {f g : E → ℂ} (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x) {a : ℕ}
    (hfa : ∀ k < a, iteratedFDeriv ℂ k f x = 0) :
    iteratedFDeriv ℂ a (fun y => f y * g y) x = g x • iteratedFDeriv ℂ a f x := by
  have hg' : AnalyticAt ℂ (fun y => g y - g x) x := hg.sub analyticAt_const
  have e : (fun y => f y * g y) = (fun y => f y * (g y - g x)) + (fun y => g x • f y) := by
    funext y
    simp only [Pi.add_apply, smul_eq_mul]
    ring
  rw [e, iteratedFDeriv_add_apply (hf.fun_mul hg').contDiffAt
      (analyticAt_const.fun_smul hf).contDiffAt,
    vanish_mul hf hg' hfa (vanish_one (by simp)) a (by omega), zero_add]
  exact iteratedFDeriv_const_smul_apply' hf.contDiffAt
end GroundTheory.Heights₂.Heights.EffectiveHS.JetOfMonomialSum
