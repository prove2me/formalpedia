-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_mul_pow_jet_934851d1e926
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:44.212787+00:00
-- url     : https://prove2.me/submissions/92d9c5aa-389a-42f9-ae34-f6b03b206dc6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_JetOfMonomialSumStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PJetOfMonomialSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_vanish_one_4f1d6effb138
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_vanish_mul_2c201f8ce5c5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_order_one_7eb3e896cbbb

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
theorem _root_.solution {v : E → ℂ} (hv : AnalyticAt ℂ v x) (hv0 : v x = 0) (w : E)
    {g : E → ℂ} (hg : AnalyticAt ℂ g x) {c : ℕ} (hgc : ∀ k < c, iteratedFDeriv ℂ k g x = 0)
    {G : ℂ} (hG : iteratedFDeriv ℂ c g x (fun _ => w) = c.factorial * G) (m : ℕ) :
    (∀ k < c + m, iteratedFDeriv ℂ k (fun y => g y * v y ^ m) x = 0) ∧
      iteratedFDeriv ℂ (c + m) (fun y => g y * v y ^ m) x (fun _ => w) =
        (c + m).factorial * G * fderiv ℂ v x w ^ m := by
  induction m with
  | zero => simpa using ⟨hgc, hG⟩
  | succ m ih =>
    have hgm : AnalyticAt ℂ (fun y => g y * v y ^ m) x := hg.fun_mul (hv.fun_pow m)
    have e : (fun y => g y * v y ^ (m + 1)) = fun y => (g y * v y ^ m) * v y := by
      funext y
      ring
    rw [e, ← add_assoc]
    refine ⟨vanish_mul hgm hv ih.1 (vanish_one hv0), ?_⟩
    rw [order_one hv hv0 w (c + m) _ hgm ih.1, ih.2, Nat.factorial_succ]
    push_cast
    ring
end GroundTheory.Heights₂.Heights.EffectiveHS.JetOfMonomialSum
