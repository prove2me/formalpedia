-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_iteratedFDeriv_fderiv_diag_af2eaa2d2298
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:04:59.8958+00:00
-- url     : https://prove2.me/submissions/8ce0e28e-5b04-425d-a242-f29ba0547688

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_JetOfMonomialSumStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PJetOfMonomialSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_iteratedFDeriv_fderiv_apply_db1f68c7338c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_snoc_const_55250f806c20

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
theorem _root_.solution {f : E → ℂ} (hf : AnalyticAt ℂ f x) (w : E) (k : ℕ) :
    iteratedFDeriv ℂ k (fun y => fderiv ℂ f y w) x (fun _ => w) =
      iteratedFDeriv ℂ (k + 1) f x (fun _ => w) := by
  rw [iteratedFDeriv_fderiv_apply hf, snoc_const]
end GroundTheory.Heights₂.Heights.EffectiveHS.JetOfMonomialSum
