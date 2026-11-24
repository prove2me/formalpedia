-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_iteratedFDeriv_fderiv_apply_db1f68c7338c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:31.577459+00:00
-- url     : https://prove2.me/submissions/618cf704-96cf-4f9b-9bc3-85b9ce5e92ef

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_JetOfMonomialSumStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PJetOfMonomialSum

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
theorem _root_.solution {f : E → ℂ} (hf : AnalyticAt ℂ f x) (w : E) (k : ℕ)
    (m : Fin k → E) :
    iteratedFDeriv ℂ k (fun y => fderiv ℂ f y w) x m =
      iteratedFDeriv ℂ (k + 1) f x (Fin.snoc m w : Fin (k + 1) → E) := by
  rw [iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last]
  have := (ContinuousLinearMap.apply ℂ ℂ w).iteratedFDeriv_comp_left
    (hf.fderiv.contDiffAt (n := ⊤)) (i := k) le_top
  exact congrArg (fun L => L m) this
end GroundTheory.Heights₂.Heights.EffectiveHS.JetOfMonomialSum
