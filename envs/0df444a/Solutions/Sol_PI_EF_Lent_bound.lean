-- Prove2me | solution 1 for PI.EF.Lent_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:43:19.985177+00:00
-- url     : https://prove2.me/submissions/bfcc1abd-4448-4efc-b8c8-16212e14d2e8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LStructC
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindowIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_HalfLeNormLentCtr
import Theorems.Thm_PI_EF_Lent_bound_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Metric Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]
namespace PI.EF
theorem _root_.solution {A C : ℝ} (hA : 0 < A) (hC : 0 < C) (hG : LGrowth A C)
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {t : ℝ} {z : ℂ} (h1 : -4 ≤ z.re)
    (h2 : z.re ≤ 8) (h3 : |z.im| ≤ |t| + 6) :
    ‖Lent χ z‖ ≤ C * (4 * (N * (|t| + 2))) ^ A := by
  by_cases hz : z = 1
  · subst hz
    have hcont : Continuous (Lent χ) := by
      unfold Lent
      split_ifs with h
      · exact (DirichletCharacter.differentiable_LFunctionTrivChar₁ N).continuous
      · exact (DirichletCharacter.differentiable_LFunction h).continuous
    have hc : Continuous (fun x : ℝ => ‖Lent χ (1 + (x : ℂ))‖) :=
      (hcont.comp (continuous_const.add Complex.continuous_ofReal)).norm
    have h0 : ‖Lent χ 1‖ = ‖Lent χ (1 + ((0 : ℝ) : ℂ))‖ := by simp
    have hT : Filter.Tendsto (fun x : ℝ => ‖Lent χ (1 + (x : ℂ))‖) (nhdsWithin (0 : ℝ) {0}ᶜ)
        (nhds ‖Lent χ 1‖) := by
      rw [h0]
      exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hT ?_
    have hmem : Set.Ioo (-1 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) {0}ᶜ :=
      nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
    filter_upwards [hmem, self_mem_nhdsWithin] with x hx hx0
    have hx1 : (1 + (x : ℂ)) ≠ 1 := by
      intro h
      apply hx0
      have h' := congrArg Complex.re h
      simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re] at h'
      show x = 0
      linarith
    refine Lent_bound_ne hA hC hG hχ ?_ ?_ ?_ hx1
    · simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
      linarith [hx.1]
    · simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
      linarith [hx.2]
    · simp only [Complex.add_im, Complex.one_im, Complex.ofReal_im, add_zero, abs_zero]
      positivity
  · exact Lent_bound_ne hA hC hG hχ h1 h2 h3 hz
end PI.EF
