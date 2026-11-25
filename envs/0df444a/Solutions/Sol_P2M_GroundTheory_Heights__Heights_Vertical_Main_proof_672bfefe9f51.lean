-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_Main_proof_672bfefe9f51
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:02:23.875396+00:00
-- url     : https://prove2.me/submissions/28ca3d33-e626-47a8-bdd9-51772fa4c85a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IsChowFormCMul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_isChowForm_C_mul_6384c68c3124
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_specFirst_C_mul_fbe46aaee29f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNorm_C_mul_5c755ec4cf94
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNorm_nonneg_6ba4fe626cee


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
namespace Main
theorem _root_.solution (h1 : GaussEq.Statement) (h2 : PrimitiveScale.Statement)
    (h3 : VertTermEq.Statement) : ChowFormSectionVertical.Statement := by
  intro K _ _ n e I f u hI hf hu v
  obtain ⟨c, g, hc, hg, hprim⟩ := h2 K v _ f hf.1
  have hcf : IsChowForm I (e + 1) (g.map (algebraMap (𝓞 K) K)) := by
    rw [hg]
    exact isChowForm_C_mul hf hc
  obtain ⟨h1a, h1b⟩ := h1 K n e I g u v hI hcf hu hprim
  rw [hg, specFirst_C_mul, gaussNorm_C_mul] at h1a
  rw [hg, gaussNorm_C_mul] at h1b
  rw [h3]
  set a := NumberField.HeightOneSpectrum.adicAbv K v c
  set N : ℝ := (Ideal.absNorm v.asIdeal : ℝ)
  set D := vertDeg e I u v
  have hN : 0 < N := by
    have h := Ideal.absNorm_ne_zero_of_nonZeroDivisors
      (⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ : nonZeroDivisors (Ideal (𝓞 K)))
    have h' : 0 < Ideal.absNorm v.asIdeal := Nat.pos_of_ne_zero h
    exact Nat.cast_pos.mpr h'
  have ha : a ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1b
    exact zero_ne_one h1b
  have hfu : 0 < gaussNorm v (specFirst f fun j => (u j : K)) := by
    refine lt_of_le_of_ne (gaussNorm_nonneg v _) fun h0 => ?_
    rw [← h0, mul_zero, zero_mul] at h1a
    exact zero_ne_one h1a
  have hff : gaussNorm v f = gaussNorm v (specFirst f fun j => (u j : K)) * N ^ D := by
    have e1 : a * gaussNorm v f = a * (gaussNorm v (specFirst f fun j => (u j : K)) * N ^ D) := by
      rw [h1b, ← mul_assoc, h1a]
    exact mul_left_cancel₀ ha e1
  rw [hff, Real.log_mul hfu.ne' (pow_ne_zero _ hN.ne'), Real.log_pow]
  ring
end Main
end GroundTheory.Heights₂.Heights.Vertical
