-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_exists_pos_of_eventually_lower_cf01f4457600
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:21:02.776976+00:00
-- url     : https://prove2.me/submissions/1b1bea55-6a56-42b0-94ab-497568075042

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmplePowSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LeadingCoeffPosSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open Filter
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {d : ℕ} {A : ℤ} (hA : 0 < A) {C : ℝ} {f : ℕ → ℝ}
    (h : ∀ᶠ n : ℕ in atTop,
      (A : ℝ) * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) - C * (n : ℝ) ^ d ≤ f n)
    (D : ℕ) (hD : 0 < D) : ∃ n₁ : ℕ, 0 < n₁ ∧ 0 < f (D * n₁) := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp h
  obtain ⟨K, hK⟩ := exists_nat_gt (C * ((d + 1).factorial : ℝ) / A)
  refine ⟨n₀ + K + 1, by omega, ?_⟩
  have hle : n₀ + K + 1 ≤ D * (n₀ + K + 1) := Nat.le_mul_of_pos_left _ hD
  refine lt_of_lt_of_le ?_ (hn₀ _ (le_trans (by omega) hle))
  have hnK : (K : ℝ) < ((D * (n₀ + K + 1) : ℕ) : ℝ) := by
    have : K < D * (n₀ + K + 1) := lt_of_lt_of_le (by omega) hle
    exact_mod_cast this
  generalize ((D * (n₀ + K + 1) : ℕ) : ℝ) = n at hnK ⊢
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  have hF : (0 : ℝ) < ((d + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (Nat.cast_nonneg K) hnK
  have h1 : C * ((d + 1).factorial : ℝ) < A * n := by
    have := lt_trans hK hnK
    rwa [div_lt_iff₀ hA', mul_comm n] at this
  have h2 : C < A * n / ((d + 1).factorial : ℝ) := by rw [lt_div_iff₀ hF]; exact h1
  have h3 : (A : ℝ) * n ^ (d + 1) / ((d + 1).factorial : ℝ) - C * n ^ d =
      n ^ d * (A * n / ((d + 1).factorial : ℝ) - C) := by ring
  rw [h3]
  exact mul_pos (pow_pos hnpos d) (by linarith)
end GroundTheory.Heights₂.Heights.Kleiman
