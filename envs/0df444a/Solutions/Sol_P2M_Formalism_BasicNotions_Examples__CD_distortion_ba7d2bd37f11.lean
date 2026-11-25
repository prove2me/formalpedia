-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_distortion_ba7d2bd37f11
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:29:28.200835+00:00
-- url     : https://prove2.me/submissions/4c5bf52c-a14d-4930-9096-b7f8f87eef08

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HasStrictFDerivAtExpZero
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_logA_exp_60d72a73aded
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_exp_logA_34b3c58efbe1
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_logA_one_5d3ec8a2de84
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_exp_cont_6ec931771609
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_exp_neg_mul_b0802c46782f
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_hasStrictFDerivAt_translateLog_076c8ad24f60
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_hasStrictFDerivAt_productLog_156a7c321b75
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_eventually_pair_16eb6f15237a
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_strict_est_80947886f766

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open Filter Topology Metric NormedSpace Asymptotics
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
namespace Formalism.BasicNotions.Examples₂.CD
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ X Y : 𝔸, ‖X‖ < δ → ‖Y‖ < δ →
    (exp (F1 (X, Y)) = exp (-X) * exp (X + Y) ∧ ‖F1 (X, Y) - Y‖ ≤ ε * ‖Y‖) ∧
    (exp (F2 (X, Y)) = exp X * exp Y ∧ ‖F2 (X, Y) - X - Y‖ ≤ ε * ‖Y‖) := by
  have hc1 : Continuous (fun p : 𝔸 × 𝔸 => exp (-p.1) * exp (p.1 + p.2)) :=
    (exp_cont.comp continuous_fst.neg).mul (exp_cont.comp (continuous_fst.add continuous_snd))
  have hc2 : Continuous (fun p : 𝔸 × 𝔸 => exp p.1 * exp p.2) :=
    (exp_cont.comp continuous_fst).mul (exp_cont.comp continuous_snd)
  have e1 : ∀ᶠ p in 𝓝 (0 : 𝔸 × 𝔸),
      exp (logA 𝔸 (exp (-p.1) * exp (p.1 + p.2))) = exp (-p.1) * exp (p.1 + p.2) := by
    have ht := hc1.tendsto 0
    simp only [Prod.fst_zero, Prod.snd_zero, neg_zero, add_zero, exp_zero, mul_one] at ht
    exact ht.eventually exp_logA
  have e2 : ∀ᶠ p in 𝓝 (0 : 𝔸 × 𝔸), exp (logA 𝔸 (exp p.1 * exp p.2)) = exp p.1 * exp p.2 := by
    have ht := hc2.tendsto 0
    simp only [Prod.fst_zero, Prod.snd_zero, exp_zero, mul_one] at ht
    exact ht.eventually exp_logA
  have e3 : ∀ᶠ p in 𝓝 (0 : 𝔸 × 𝔸), logA 𝔸 (exp p.1) = p.1 := by
    have ht := (continuous_fst (X := 𝔸) (Y := 𝔸)).tendsto 0
    simp only [Prod.fst_zero] at ht
    exact ht.eventually logA_exp
  obtain ⟨δ1, hδ1, h1⟩ := eventually_pair (e1.and (e2.and e3))
  obtain ⟨δ2, hδ2, h2⟩ := strict_est (hasStrictFDerivAt_translateLog (𝔸 := 𝔸)) hε
  obtain ⟨δ3, hδ3, h3⟩ := strict_est (hasStrictFDerivAt_productLog (𝔸 := 𝔸)) hε
  refine ⟨min δ1 (min δ2 δ3), lt_min hδ1 (lt_min hδ2 hδ3), fun X Y hX hY => ?_⟩
  have hX1 : ‖X‖ < δ1 := lt_of_lt_of_le hX (min_le_left _ _)
  have hY1 : ‖Y‖ < δ1 := lt_of_lt_of_le hY (min_le_left _ _)
  have hX2 : ‖X‖ < δ2 := lt_of_lt_of_le hX ((min_le_right _ _).trans (min_le_left _ _))
  have hY2 : ‖Y‖ < δ2 := lt_of_lt_of_le hY ((min_le_right _ _).trans (min_le_left _ _))
  have hX3 : ‖X‖ < δ3 := lt_of_lt_of_le hX ((min_le_right _ _).trans (min_le_right _ _))
  have hY3 : ‖Y‖ < δ3 := lt_of_lt_of_le hY ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨k1, k2, k3⟩ := h1 X Y hX1 hY1
  refine ⟨⟨k1, ?_⟩, ⟨k2, ?_⟩⟩
  · have h := h2 X Y hX2 hY2
    have hz : F1 (X, (0 : 𝔸)) = 0 := by
      simp only [F1, add_zero, exp_neg_mul, logA_one]
    rw [hz, sub_zero] at h
    simpa using h
  · have h := h3 X Y hX3 hY3
    have hz : F2 (X, (0 : 𝔸)) = X := by
      simp only [F2, exp_zero, mul_one]
      exact k3
    rw [hz] at h
    simpa using h
end Formalism.BasicNotions.Examples₂.CD
