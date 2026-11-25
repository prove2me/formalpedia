-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesNorm_intSeriesEval_split_252472cd49a8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:26.773103+00:00
-- url     : https://prove2.me/submissions/b2755761-398c-40f2-91c6-06fa5a99e9cc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeries
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_IntSeriesNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowlaSelberg_PIntSeriesNorm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowlaSelberg_IntSeriesNorm_residuePart_conv_7c24ca73e8b7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ChowlaSelberg
open PowerSeries
open scoped Real
noncomputable section
open GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesNorm
namespace GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesNorm
theorem _root_.solution (hR : IntSeriesRing.Statement) {F : PowerSeries ℤ} {r : ℝ}
    (hr : 0 < r) (hF : IntSeriesConv F r) {p : ℕ} (hp : 0 < p) (s : ℂ) (hs : ‖s‖ ≤ r) :
    intSeriesEval F s = ∑ i : Fin p, s ^ (i : ℕ) * intSeriesEval (residuePart F p i) (s ^ p) := by
  have : NeZero p := ⟨hp.ne'⟩
  have hq : ‖s ^ p‖ ≤ r ^ p := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hs p
  have hsum := (hR r hr.le).2.2.1 F hF s hs
  have hparts : ∀ i : Fin p, HasSum (fun m : ℕ ↦ ((coeff (m * p + i) F : ℤ) : ℂ) * s ^ (m * p + i))
      (s ^ (i : ℕ) * intSeriesEval (residuePart F p i) (s ^ p)) := by
    intro i
    have h := ((hR (r ^ p) (pow_nonneg hr.le p)).2.2.1 _ (residuePart_conv hr hF hp i) _ hq).mul_left
      (s ^ (i : ℕ))
    have hf : (fun m : ℕ ↦ ((coeff (m * p + i) F : ℤ) : ℂ) * s ^ (m * p + i)) =
        fun m ↦ s ^ (i : ℕ) * (((coeff m (residuePart F p i) : ℤ) : ℂ) * (s ^ p) ^ m) := by
      funext m
      simp only [residuePart, coeff_mk]
      rw [pow_add, pow_mul']
      ring
    rw [hf]
    exact h
  let e : ℕ ≃ Fin p × ℕ := (Nat.divModEquiv p).trans (Equiv.prodComm _ _)
  have hfe : ∀ x : Fin p × ℕ, e.symm x = x.2 * p + x.1 := fun x ↦ rfl
  have htot := (e.symm.hasSum_iff).mpr hsum
  simp only [Function.comp_def, hfe] at htot
  exact (htot.prod_fiberwise hparts).unique (hasSum_fintype _)
end GroundTheory.Heights₂.Heights.ChowlaSelberg.IntSeriesNorm
