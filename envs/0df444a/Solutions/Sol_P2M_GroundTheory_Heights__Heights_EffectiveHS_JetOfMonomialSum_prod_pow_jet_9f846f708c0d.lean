-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_prod_pow_jet_9f846f708c0d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:13:54.806331+00:00
-- url     : https://prove2.me/submissions/9904128e-2c48-44bf-9ffe-a5136edae56a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_JetOfMonomialSumStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PJetOfMonomialSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_mul_pow_jet_934851d1e926

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
theorem _root_.solution {p : ℕ} (u : Fin p → E → ℂ) (hu : ∀ i, AnalyticAt ℂ (u i) x)
    (hu0 : ∀ i, u i x = 0) (α : Fin p → ℕ) (w : E) (s : Finset (Fin p)) :
    AnalyticAt ℂ (fun y => ∏ i ∈ s, u i y ^ α i) x ∧
    (∀ k < ∑ i ∈ s, α i, iteratedFDeriv ℂ k (fun y => ∏ i ∈ s, u i y ^ α i) x = 0) ∧
    iteratedFDeriv ℂ (∑ i ∈ s, α i) (fun y => ∏ i ∈ s, u i y ^ α i) x (fun _ => w) =
      (∑ i ∈ s, α i).factorial * ∏ i ∈ s, fderiv ℂ (u i) x w ^ α i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, fun k hk => by simp at hk, ?_⟩
    · simp only [Finset.prod_empty]
      exact analyticAt_const
    · simp only [Finset.sum_empty, Finset.prod_empty, Nat.factorial_zero, Nat.cast_one, mul_one]
      exact iteratedFDeriv_zero_apply _
  | insert j s hj ih =>
    obtain ⟨ha, hv, hd⟩ := ih
    have e : (fun y => ∏ i ∈ insert j s, u i y ^ α i) =
        fun y => (∏ i ∈ s, u i y ^ α i) * u j y ^ α j := by
      funext y
      rw [Finset.prod_insert hj, mul_comm]
    have := mul_pow_jet (hu j) (hu0 j) w ha hv (G := ∏ i ∈ s, fderiv ℂ (u i) x w ^ α i) hd (α j)
    rw [e, Finset.sum_insert hj, Finset.prod_insert hj, add_comm (α j)]
    refine ⟨ha.fun_mul ((hu j).fun_pow _), this.1, ?_⟩
    rw [this.2]
    ring
end GroundTheory.Heights₂.Heights.EffectiveHS.JetOfMonomialSum
