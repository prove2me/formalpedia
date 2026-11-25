-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SmallSetBallCover_proof_35cb474ad1cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:40:45.175833+00:00
-- url     : https://prove2.me/submissions/e5fa6d54-e142-423a-8e94-2815fa25e045

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSmallSetBallCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSmallSetTubeVolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSmallSetBallCover
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_cover_le_volume_thickening_5b3271255eb1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory ComplexSets Metric
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace SmallSetBallCover
theorem _root_.solution (h : SmallSetTubeVolume.Statement) : SmallSetBallCover.Statement := by
  intro n d I K hdim hK
  obtain ⟨C, hC0, hC⟩ := h n d I K hdim hK
  refine ⟨C * (16 / Real.pi) ^ n, by positivity, fun r hr => ?_⟩
  have hr0 := hr.1
  have hZ : IsClosed (zeroSet I) := by
    have : zeroSet I = ⋂ q ∈ I, {x : Fin n → ℂ | eval x q = 0} := by ext x; simp [zeroSet]
    rw [this]
    exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
  have hA : IsCompact (zeroSet I ∩ K) := hK.inter_left hZ
  obtain ⟨T, hTA, hcov, hcount⟩ := exists_cover_le_volume_thickening hA hr0
  refine ⟨T, hTA, hcov, ?_⟩
  have hV := ENNReal.toReal_le_of_le_ofReal (by positivity) (hC r hr)
  have hz : r ^ ((2 * n + 2 : ℤ) - 2 * d) * r ^ (2 * d) = r ^ (2 * n) * r ^ 2 := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hr0.ne', ← zpow_add₀ hr0.ne']
    congr 1; push_cast; ring
  have hP : 0 < (Real.pi / 16) ^ n * r ^ (2 * n) := by positivity
  have he : (16 / Real.pi) ^ n * (Real.pi / 16) ^ n = 1 := by
    rw [← mul_pow, div_mul_div_comm, mul_comm 16, div_self (by positivity), one_pow]
  have hball : (Real.pi * (r / 4) ^ 2) ^ n = (Real.pi / 16) ^ n * r ^ (2 * n) := by
    rw [pow_mul, ← mul_pow]; ring_nf
  refine le_of_mul_le_mul_right ?_ hP
  calc (T.card : ℝ) * r ^ (2 * d) * ((Real.pi / 16) ^ n * r ^ (2 * n))
      = ((T.card : ℝ) * (Real.pi * (r / 4) ^ 2) ^ n) * r ^ (2 * d) := by rw [hball]; ring
    _ ≤ (C * r ^ ((2 * n + 2 : ℤ) - 2 * d)) * r ^ (2 * d) := mul_le_mul_of_nonneg_right (hcount.trans hV) (by positivity)
    _ = C * (16 / Real.pi) ^ n * r ^ 2 * ((Real.pi / 16) ^ n * r ^ (2 * n)) := by
      rw [mul_assoc, hz]
      linear_combination (-(C * r ^ (2 * n) * r ^ 2)) * he
end SmallSetBallCover
end GroundTheory.Heights₂.Heights
