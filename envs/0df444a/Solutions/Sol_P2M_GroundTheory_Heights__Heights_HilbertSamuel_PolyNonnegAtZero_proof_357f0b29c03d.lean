-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_PolyNonnegAtZero_proof_357f0b29c03d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:56:16.982986+00:00
-- url     : https://prove2.me/submissions/b6efb7f1-00a7-41c2-b06a-e11d1ddcb42b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPolyNonnegAtZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PPolyNonnegAtZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Filter Topology
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace PolyNonnegAtZero
theorem _root_.solution : PolyNonnegAtZero.Statement := by
  intro d p c hc hdom hev
  by_contra h0
  push Not at h0
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  let S : Set ℝ := {t | 0 ≤ t ∧ p.eval t ≤ 0}
  have h0S : (0 : ℝ) ∈ S := ⟨le_rfl, h0.le⟩
  have hbdd : BddAbove S := ⟨N, fun t ht => by
    by_contra hlt
    push Not at hlt
    exact absurd ht.2 (not_le.2 (hN t hlt.le))⟩
  have hclosed : IsClosed S :=
    (isClosed_le continuous_const continuous_id).inter
      (isClosed_le p.continuous continuous_const)
  have ht0S : sSup S ∈ S := hclosed.csSup_mem ⟨0, h0S⟩ hbdd
  obtain ⟨ht0nn, hpt0⟩ := ht0S
  have hpos : ∀ t, sSup S < t → 0 < p.eval t := by
    intro t ht
    by_contra hle
    push Not at hle
    exact absurd (le_csSup hbdd ⟨ht0nn.trans ht.le, hle⟩) (not_le.2 ht)
  have hlim : c * (sSup S) ^ d ≤ p.eval (sSup S) := by
    by_contra hlt
    push Not at hlt
    have hcont : Continuous fun t : ℝ => p.eval t - c * t ^ d :=
      p.continuous.sub (continuous_const.mul (continuous_pow d))
    have hev' : ∀ᶠ t in 𝓝 (sSup S), p.eval t - c * t ^ d < 0 :=
      hcont.continuousAt.eventually (gt_mem_nhds (by linarith))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev'
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show sSup S < sSup S + ε by linarith)
    have hqpos : (0 : ℝ) < q := lt_of_le_of_lt ht0nn hq1
    have hd : dist (q : ℝ) (sSup S) < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have h1 := hball hd
    have h2 := hdom q (by exact_mod_cast hqpos) (hpos q hq1)
    linarith
  rcases ht0nn.lt_or_eq with htpos | htz
  · have : 0 < c * (sSup S) ^ d := mul_pos hc (pow_pos htpos d)
    linarith
  · have hp0 : 0 ≤ p.eval (sSup S) := le_trans (mul_nonneg hc.le (pow_nonneg ht0nn d)) hlim
    rw [← htz] at hp0
    linarith
end PolyNonnegAtZero
end GroundTheory.Heights₂.Heights.HilbertSamuel
