-- Prove2me | solution 1 for P2M_GlobalTheory_HeckeTwoC_bound_G__e6ab55a3392d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:38:13.759242+00:00
-- url     : https://prove2.me/submissions/7d1c89f8-0de8-4965-95bf-7e0bad8b7524

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOn
import Theorems.Thm_GlobalTheory_HeckeTwoC_lg_nonneg
import Theorems.Thm_P2M_GlobalTheory_HeckeTwoC_norm_G__1a9e454f2caf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwoC
open MeasureTheory
namespace GlobalTheory.HeckeTwoC
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) {σ : ℂ} (hσ : -1 / 2 + ε ≤ σ.re) (t : ℝ) :
    ‖G' σ t‖ ≤ 2 / ε * Real.exp (-(1 + ε) * lg t) := by
  rw [norm_G']
  have hL := lg_nonneg t
  have h1 : Real.exp (-(2 + 2 * σ.re) * lg t) ≤ Real.exp (-(1 + ε) * lg t) * Real.exp (-(ε * lg t)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  have h2 : ε * lg t + 1 ≤ Real.exp (ε * lg t) := Real.add_one_le_exp _
  have h3 : Real.exp (-(ε * lg t)) * (2 * lg t) ≤ 2 / ε := by
    rw [Real.exp_neg, le_div_iff₀ hε]
    have hp := Real.exp_pos (ε * lg t)
    rw [show (Real.exp (ε * lg t))⁻¹ * (2 * lg t) * ε = 2 * (ε * lg t) / Real.exp (ε * lg t) by field_simp]
    rw [div_le_iff₀ hp]
    linarith
  calc Real.exp (-(2 + 2 * σ.re) * lg t) * (2 * lg t)
      ≤ Real.exp (-(1 + ε) * lg t) * Real.exp (-(ε * lg t)) * (2 * lg t) :=
        mul_le_mul_of_nonneg_right h1 (by linarith)
    _ = Real.exp (-(1 + ε) * lg t) * (Real.exp (-(ε * lg t)) * (2 * lg t)) := by ring
    _ ≤ Real.exp (-(1 + ε) * lg t) * (2 / ε) := mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = 2 / ε * Real.exp (-(1 + ε) * lg t) := by ring
end GlobalTheory.HeckeTwoC
