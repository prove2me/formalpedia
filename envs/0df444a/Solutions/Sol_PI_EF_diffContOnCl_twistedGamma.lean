-- Prove2me | solution 1 for PI.EF.diffContOnCl_twistedGamma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:37:26.833299+00:00
-- url     : https://prove2.me/submissions/3501ca4c-aa5a-4c40-b1ed-20ced1f21a46

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthGamma

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
open Complex Filter Set
namespace PI.EF
theorem _root_.solution : DiffContOnCl ℂ frobeniusStickelbergerDetMulSigmaCube (re ⁻¹' Ioo (1 / 2 : ℝ) (11 / 2)) := by
  apply DifferentiableOn.diffContOnCl
  have hcl : closure (re ⁻¹' Ioo (1 / 2 : ℝ) (11 / 2)) ⊆ re ⁻¹' Icc (1 / 2 : ℝ) (11 / 2) :=
    closure_minimal (preimage_mono Ioo_subset_Icc_self) (isClosed_Icc.preimage Complex.continuous_re)
  intro w hw
  have hw' := hcl hw
  have hre : (1 / 2 : ℝ) ≤ w.re := hw'.1
  apply DifferentiableAt.differentiableWithinAt
  unfold frobeniusStickelbergerDetMulSigmaCube
  apply DifferentiableAt.div
  · apply DifferentiableAt.mul
    · apply Complex.differentiableAt_Gamma
      intro m h
      have := congrArg Complex.re h
      simp at this
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    · fun_prop
  · fun_prop
  · apply pow_ne_zero
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
end PI.EF
