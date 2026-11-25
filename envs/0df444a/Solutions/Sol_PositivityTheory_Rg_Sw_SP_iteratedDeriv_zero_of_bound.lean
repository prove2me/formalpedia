-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.iteratedDeriv_zero_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:47:47.771294+00:00
-- url     : https://prove2.me/submissions/fc272f49-40d5-4e74-9aea-c2a0b6004887

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_IteratedDerivZeroOfBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution {f : ℂ → ℂ} {ε C : ℝ} {r : ℕ} (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (ball 0 ε)) (hb : ∀ z ∈ ball (0 : ℂ) ε, ‖f z‖ ≤ C * ‖z‖ ^ r) {j : ℕ} (hj : j < r) :
    iteratedDeriv j f 0 = 0 := by
  have key : ∀ R : ℝ, 0 < R → R < ε → ‖iteratedDeriv j f 0‖ ≤ j.factorial * (C * R ^ r) / R ^ j := by
    intro R hR hRε
    refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hR ?_ ?_
    · exact hf.diffContOnCl_ball (closedBall_subset_ball hRε)
    · intro z hz
      have hz' : z ∈ ball (0 : ℂ) ε := by
        rw [mem_sphere_zero_iff_norm] at hz
        rw [mem_ball_zero_iff, hz]; exact hRε
      have := hb z hz'
      rwa [mem_sphere_zero_iff_norm.1 hz] at this
  have hlim : Filter.Tendsto (fun R : ℝ => (j.factorial : ℝ) * (C * R ^ r) / R ^ j) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have e : ∀ R : ℝ, 0 < R → (j.factorial : ℝ) * (C * R ^ r) / R ^ j = j.factorial * C * R ^ (r - j) := by
      intro R hR
      have : R ^ r = R ^ (r - j) * R ^ j := by rw [← pow_add, Nat.sub_add_cancel hj.le]
      rw [this]; field_simp
    have h0 : Filter.Tendsto (fun R : ℝ => (j.factorial : ℝ) * C * R ^ (r - j)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have : Filter.Tendsto (fun R : ℝ => (j.factorial : ℝ) * C * R ^ (r - j)) (nhds 0) (nhds ((j.factorial : ℝ) * C * 0 ^ (r - j))) :=
        (continuous_const.mul (continuous_pow _)).tendsto 0
      rw [zero_pow (Nat.sub_ne_zero_of_lt hj), mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine h0.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with R hR using (e R hR).symm
  have hle : ‖iteratedDeriv j f 0‖ ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT hε] with R hR using key R hR.1 hR.2
  exact norm_le_zero_iff.1 hle
end PositivityTheory.Rg.Sw.SP
