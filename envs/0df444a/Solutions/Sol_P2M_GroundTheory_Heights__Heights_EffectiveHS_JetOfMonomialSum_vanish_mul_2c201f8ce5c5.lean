-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_vanish_mul_2c201f8ce5c5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:02.569563+00:00
-- url     : https://prove2.me/submissions/28187313-359b-43da-b861-06ef6bb9f47c

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
theorem _root_.solution {f g : E → ℂ} (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x) {a b : ℕ}
    (hfa : ∀ k < a, iteratedFDeriv ℂ k f x = 0) (hgb : ∀ k < b, iteratedFDeriv ℂ k g x = 0) :
    ∀ k < a + b, iteratedFDeriv ℂ k (fun y => f y * g y) x = 0 := by
  intro k hk
  obtain ⟨s, hs, hso, hxs⟩ :=
    eventually_nhds_iff.1 (hf.eventually_analyticAt.and hg.eventually_analyticAt)
  have hfs : ContDiffOn ℂ ⊤ f s := fun y hy => (hs y hy).1.contDiffAt.contDiffWithinAt
  have hgs : ContDiffOn ℂ ⊤ g s := fun y hy => (hs y hy).2.contDiffAt.contDiffWithinAt
  have key := norm_iteratedFDerivWithin_mul_le hfs hgs hso.uniqueDiffOn hxs (n := k) le_top
  rw [iteratedFDerivWithin_of_isOpen k hso hxs] at key
  have hsum : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDerivWithin ℂ i f s x‖ *
      ‖iteratedFDerivWithin ℂ (k - i) g s x‖ = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hik := Finset.mem_range.1 hi
    rw [iteratedFDerivWithin_of_isOpen i hso hxs, iteratedFDerivWithin_of_isOpen (k - i) hso hxs]
    rcases lt_or_ge i a with h | h
    · simp [hfa i h]
    · simp [hgb (k - i) (by omega)]
  rw [hsum] at key
  exact norm_le_zero_iff.1 key
end GroundTheory.Heights₂.Heights.EffectiveHS.JetOfMonomialSum
