-- Prove2me | solution 1 for PI.OmLocU.Nrm.solve_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:07:54.964229+00:00
-- url     : https://prove2.me/submissions/0f1a4e1a-e463-4a5d-9a5a-49ad187a5bfb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LandherrUnitNorm_UnitNormLoc
import Definitions.Def_Lemmata_GeneralBFactLeft_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnitaryOrbits_NormLeOfNear
import Theorems.Thm_PI_OmLocU_Nrm_near_root
import Theorems.Thm_PI_OmLocU_Nrm_norm_le_of_near
import Theorems.Thm_P2M_PI_Landherr__unitNormLoc_add_le_19ca89b64b37
import Theorems.Thm_P2M_PI_Landherr__unitNormLoc_add_lt_ceb1586227f0
import Theorems.Thm_P2M_PI_Landherr__unitNormLoc_mul_le_3fe19474cadc
import Theorems.Thm_P2M_PI_Landherr__unitNormLoc_mul_lt_575669e40379
import Theorems.Thm_P2M_PI_Landherr__unitNormLoc_newton_b8b32645f676
import Theorems.Thm_P2M_PI_Landherr__unitNormLoc_norm_two_le_ac676a0a19a1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open PI.Landherr₃
open PI PI.OmLocU PI.OmLocU.Nrm
namespace PI.OmLocU.Nrm
theorem _root_.solution {K : Type} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (T M ε x₀ y₀ : K) (hT : ‖T‖ ≤ 1) (hM : ‖M‖ ≤ 1) (hD : ‖T ^ 2 - 4 * M‖ = 1) (hε : ‖ε‖ = 1)
    (hx : ‖x₀‖ ≤ 1) (hy : ‖y₀‖ ≤ 1) (h0 : ‖x₀ ^ 2 + T * x₀ * y₀ + M * y₀ ^ 2 - ε‖ < 1) :
    ∃ x y : K, ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 ∧ x ^ 2 + T * x * y + M * y ^ 2 = ε := by
  have h2 : ‖(2 : K)‖ ≤ 1 := unitNormLoc_norm_two_le
  have hgx : ‖2 * x₀ + T * y₀‖ ≤ 1 :=
    unitNormLoc_add_le (unitNormLoc_mul_le h2 hx) (unitNormLoc_mul_le hT hy)
  rcases hgx.lt_or_eq with hlt | heq
  · have hgy : ‖2 * M * y₀ + T * x₀‖ = 1 := by
      have hle : ‖2 * M * y₀ + T * x₀‖ ≤ 1 :=
        unitNormLoc_add_le (unitNormLoc_mul_le (unitNormLoc_mul_le h2 hM) hy) (unitNormLoc_mul_le hT hx)
      rcases hle.lt_or_eq with hlt' | h'
      · exfalso
        have ey : (T ^ 2 - 4 * M) * y₀ = T * (2 * x₀ + T * y₀) + (-2) * (2 * M * y₀ + T * x₀) := by ring
        have ex : (T ^ 2 - 4 * M) * x₀ = T * (2 * M * y₀ + T * x₀) + (-2 * M) * (2 * x₀ + T * y₀) := by ring
        have hn2 : ‖(-2 : K)‖ ≤ 1 := by rw [norm_neg]; exact h2
        have hy1 : ‖y₀‖ < 1 := by
          have := unitNormLoc_add_lt (unitNormLoc_mul_lt hT hlt) (unitNormLoc_mul_lt hn2 hlt')
          rwa [← ey, norm_mul, hD, one_mul] at this
        have hx1 : ‖x₀‖ < 1 := by
          have := unitNormLoc_add_lt (unitNormLoc_mul_lt hT hlt')
            (unitNormLoc_mul_lt (unitNormLoc_mul_le hn2 hM) hlt)
          rwa [← ex, norm_mul, hD, one_mul] at this
        have hq : ‖x₀ ^ 2 + T * x₀ * y₀ + M * y₀ ^ 2‖ < 1 := by
          refine unitNormLoc_add_lt (unitNormLoc_add_lt ?_ ?_) ?_
          · rw [pow_two]; exact unitNormLoc_mul_lt hx hx1
          · exact unitNormLoc_mul_lt (unitNormLoc_mul_le hT hx) hy1
          · rw [pow_two, ← mul_assoc]; exact unitNormLoc_mul_lt (unitNormLoc_mul_le hM hy) hy1
        have : ‖ε‖ < 1 := by
          have e : ε = (x₀ ^ 2 + T * x₀ * y₀ + M * y₀ ^ 2) + -(x₀ ^ 2 + T * x₀ * y₀ + M * y₀ ^ 2 - ε) := by ring
          rw [e]; exact unitNormLoc_add_lt hq (by rw [norm_neg]; exact h0)
        rw [hε] at this; exact lt_irrefl _ this
      · exact h'
    have hf : ‖M * y₀ ^ 2 + T * x₀ * y₀ + (x₀ ^ 2 - ε)‖ < 1 := by
      have e : M * y₀ ^ 2 + T * x₀ * y₀ + (x₀ ^ 2 - ε) = x₀ ^ 2 + T * x₀ * y₀ + M * y₀ ^ 2 - ε := by ring
      rw [e]; exact h0
    obtain ⟨y, hy'⟩ := unitNormLoc_newton M (T * x₀) (x₀ ^ 2 - ε) y₀ hM (by rw [hgy, one_pow]; exact hf)
    obtain ⟨z, hz, hzn⟩ := near_root M (T * x₀) (x₀ ^ 2 - ε) y₀ y hgy hf hy'
    exact ⟨x₀, z, hx, norm_le_of_near hzn hy, by linear_combination hz⟩
  · have hf : ‖1 * x₀ ^ 2 + T * y₀ * x₀ + (M * y₀ ^ 2 - ε)‖ < 1 := by
      have e2 : 1 * x₀ ^ 2 + T * y₀ * x₀ + (M * y₀ ^ 2 - ε) = x₀ ^ 2 + T * x₀ * y₀ + M * y₀ ^ 2 - ε := by ring
      rw [e2]; exact h0
    have hg : ‖2 * 1 * x₀ + T * y₀‖ = 1 := by rw [mul_one]; exact heq
    obtain ⟨x, hx'⟩ := unitNormLoc_newton 1 (T * y₀) (M * y₀ ^ 2 - ε) x₀ (by rw [norm_one])
      (by rw [hg, one_pow]; exact hf)
    obtain ⟨z, hz, hzn⟩ := near_root 1 (T * y₀) (M * y₀ ^ 2 - ε) x₀ x hg hf hx'
    exact ⟨z, y₀, norm_le_of_near hzn hx, hy, by linear_combination hz⟩
end PI.OmLocU.Nrm
