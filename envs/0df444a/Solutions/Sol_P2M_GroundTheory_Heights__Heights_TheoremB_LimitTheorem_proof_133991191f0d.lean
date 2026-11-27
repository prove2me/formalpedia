-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_LimitTheorem_proof_133991191f0d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:08:53.274833+00:00
-- url     : https://prove2.me/submissions/260d540b-7316-43ad-82bf-c23c6ba147e7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_StatementsEnd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_ImportsAlt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Filter Topology
namespace GroundTheory.Heights₂.Heights.TheoremB
namespace LimitTheorem
theorem _root_.solution : LimitTheorem.Statement := by
  intro σ _ Pt u w M C3 s0 hs0 hM
  set g : ℚ → ℝ := fun s => eval (fun o : Option σ => o.elim (s : ℝ) (fun p => u p - s * w p)) Pt
    with hg
  have hgc : Continuous g := by
    refine (MvPolynomial.continuous_eval Pt).comp ?_
    refine continuous_pi fun o => ?_
    rcases o with _ | p
    · exact Rat.continuous_coe_real
    · exact continuous_const.sub (Rat.continuous_coe_real.mul continuous_const)
  have hg0 : g 0 = eval (fun o : Option σ => o.elim (0 : ℝ) u) Pt := by
    simp only [hg]
    congr 2
    funext o
    rcases o with _ | p <;> simp
  have h1 : Tendsto g (𝓝[>] (0 : ℚ)) (𝓝 (g 0)) :=
    (hgc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hC : Tendsto (fun s : ℚ => C3 * (s : ℝ)) (𝓝[>] (0 : ℚ)) (𝓝 0) := by
    have h : Tendsto (fun s : ℚ => C3 * (s : ℝ)) (𝓝 (0 : ℚ)) (𝓝 (C3 * ((0 : ℚ) : ℝ))) :=
      (continuous_const.mul Rat.continuous_coe_real).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hlt : ∀ᶠ s : ℚ in 𝓝 (0 : ℚ), (s : ℝ) < s0 := by
    have h : Tendsto (fun s : ℚ => (s : ℝ)) (𝓝 (0 : ℚ)) (𝓝 ((0 : ℚ) : ℝ)) :=
      Rat.continuous_coe_real.tendsto 0
    rw [Rat.cast_zero] at h
    exact h.eventually (gt_mem_nhds hs0)
  have hev : ∀ᶠ s : ℚ in 𝓝[>] (0 : ℚ), ‖M s - g s‖ ≤ C3 * (s : ℝ) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hlt] with s hs hs'
    rw [Real.norm_eq_abs]
    exact hM s hs hs'.le
  have h2 : Tendsto (fun s => M s - g s) (𝓝[>] (0 : ℚ)) (𝓝 0) := squeeze_zero_norm' hev hC
  rw [← hg0]
  simpa using h1.add h2
end LimitTheorem
end GroundTheory.Heights₂.Heights.TheoremB
