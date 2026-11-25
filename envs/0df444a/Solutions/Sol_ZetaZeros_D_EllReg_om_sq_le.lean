-- Prove2me | solution 1 for ZetaZeros.D.EllReg.om_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:06:51.423364+00:00
-- url     : https://prove2.me/submissions/b357a596-61c8-436f-8287-ece54cef31ad

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegStep
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_BaseLevel
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeightedNormFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
private theorem rpow_le_rpow_of_le_of_exponent_nonpos {x y z : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hz : z ≤ 0) :
    y ^ z ≤ x ^ z := by
  exact Real.rpow_le_rpow_of_nonpos hx hxy hz
private theorem sq_one_add_rpow_mul_rpow_le_max_mul_rpow (s M ε t : ℝ) (hε : 0 < ε) (ht : 0 ≤ t) :
    ((1 + t) ^ (s / 2) * (1 + ε ^ 2 * t) ^ (-(M / 2))) ^ 2 ≤
      max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)) * (1 + t) ^ (s - M) := by
  have hA : 0 < 1 + t := by linarith
  have hε2 : 0 < ε ^ 2 := by positivity
  have hB : 0 < 1 + ε ^ 2 * t := add_pos_of_pos_of_nonneg one_pos (mul_nonneg hε2.le ht)
  have ha : 0 < min 1 (ε ^ 2) := lt_min one_pos hε2
  have hb : 0 < max 1 (ε ^ 2) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have h1 : ((1 + t) ^ (s / 2)) ^ 2 = (1 + t) ^ s := by
    rw [sq ((1 + t) ^ (s / 2)), ← Real.rpow_add hA]
    congr 1
    ring
  have h2 : ((1 + ε ^ 2 * t) ^ (-(M / 2))) ^ 2 = (1 + ε ^ 2 * t) ^ (-M) := by
    rw [sq ((1 + ε ^ 2 * t) ^ (-(M / 2))), ← Real.rpow_add hB]
    congr 1
    ring
  have hAp : 0 ≤ (1 + t) ^ (-M) := Real.rpow_nonneg hA.le _
  have key : (1 + ε ^ 2 * t) ^ (-M) ≤
      max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)) * (1 + t) ^ (-M) := by
    rcases le_total 0 M with hM | hM
    · have hle : min 1 (ε ^ 2) * (1 + t) ≤ 1 + ε ^ 2 * t := by
        have e1 : min 1 (ε ^ 2) ≤ 1 := min_le_left _ _
        have e2 : min 1 (ε ^ 2) * t ≤ ε ^ 2 * t := mul_le_mul_of_nonneg_right (min_le_right _ _) ht
        nlinarith
      calc (1 + ε ^ 2 * t) ^ (-M) ≤ (min 1 (ε ^ 2) * (1 + t)) ^ (-M) :=
            rpow_le_rpow_of_le_of_exponent_nonpos (mul_pos ha hA) hle (by linarith)
        _ = (min 1 (ε ^ 2)) ^ (-M) * (1 + t) ^ (-M) := Real.mul_rpow ha.le hA.le
        _ ≤ max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)) * (1 + t) ^ (-M) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hAp
    · have hle : 1 + ε ^ 2 * t ≤ max 1 (ε ^ 2) * (1 + t) := by
        have e1 : 1 ≤ max 1 (ε ^ 2) := le_max_left _ _
        have e2 : ε ^ 2 * t ≤ max 1 (ε ^ 2) * t := mul_le_mul_of_nonneg_right (le_max_right _ _) ht
        nlinarith
      calc (1 + ε ^ 2 * t) ^ (-M) ≤ (max 1 (ε ^ 2) * (1 + t)) ^ (-M) :=
            Real.rpow_le_rpow hB.le hle (by linarith)
        _ = (max 1 (ε ^ 2)) ^ (-M) * (1 + t) ^ (-M) := Real.mul_rpow hb.le hA.le
        _ ≤ max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)) * (1 + t) ^ (-M) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hAp
  rw [mul_pow, h1, h2, sub_eq_add_neg, Real.rpow_add hA]
  calc (1 + t) ^ s * (1 + ε ^ 2 * t) ^ (-M)
      ≤ (1 + t) ^ s * (max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)) * (1 + t) ^ (-M)) :=
        mul_le_mul_of_nonneg_left key (Real.rpow_nonneg hA.le _)
    _ = max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)) * ((1 + t) ^ s * (1 + t) ^ (-M)) := by
        ring
end ZetaZeros.D.EllReg
end

set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
namespace ZetaZeros.D.EllReg
theorem _root_.solution {d : ℕ} (s M ε : ℝ) (hε : 0 < ε) (ξ : E d) :
    om s M ε ξ ^ 2 ≤ max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)) * (1 + ‖ξ‖ ^ 2) ^ (s - M) := by
  unfold om
  exact sq_one_add_rpow_mul_rpow_le_max_mul_rpow s M ε _ hε (by positivity)
end ZetaZeros.D.EllReg
