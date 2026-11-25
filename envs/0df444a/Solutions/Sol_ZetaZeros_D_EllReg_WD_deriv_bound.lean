-- Prove2me | solution 1 for ZetaZeros.D.EllReg.WD.deriv_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:00:36.869796+00:00
-- url     : https://prove2.me/submissions/cd633c21-34bd-4c00-bb24-e5d42777943f

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_WeightDiff
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
noncomputable section
namespace WD
variable {d : ℕ}
private theorem abs_mul_sub_le_of_sq_eq_one_add_sq (g t s M e r b V : ℝ) (hg : 0 ≤ g) (hV : 0 ≤ V) (ht : |t| ≤ g * V)
    (hM : 0 ≤ M) (he0 : 0 ≤ e) (he1 : e ≤ 1) (hr0 : 0 < r) (hr2 : r ^ 2 = 1 + g ^ 2)
    (hb : b = 1 + e * g ^ 2) :
    |t * (s * r⁻¹ - M * e * r * b⁻¹)| ≤ (|s| + M) * V := by
  subst hb
  have hb0 : 0 < 1 + e * g ^ 2 := add_pos_of_pos_of_nonneg one_pos (mul_nonneg he0 (sq_nonneg g))
  have hgr : g ≤ r := by
    by_contra hcon
    have hlt := not_le.mp hcon
    nlinarith [mul_lt_mul'' hlt hlt hr0.le hr0.le]
  have hgr' : g * r⁻¹ ≤ 1 := by
    calc g * r⁻¹ ≤ r * r⁻¹ := mul_le_mul_of_nonneg_right hgr (inv_nonneg.2 hr0.le)
      _ = 1 := mul_inv_cancel₀ hr0.ne'
  have hsq : (g * e * r) ^ 2 ≤ (1 + e * g ^ 2) ^ 2 := by
    have h := mul_nonneg (mul_nonneg he0 (sq_nonneg g)) (by linarith : (0 : ℝ) ≤ 2 - e)
    have h' : (g * e * r) ^ 2 = g ^ 2 * e ^ 2 * r ^ 2 := by ring
    rw [h', hr2]
    nlinarith
  have hX : g * e * r ≤ 1 + e * g ^ 2 := by
    by_contra hcon
    have hlt := not_le.mp hcon
    nlinarith [mul_lt_mul'' hlt hlt hb0.le hb0.le]
  have hgb : g * (e * r * (1 + e * g ^ 2)⁻¹) ≤ 1 := by
    calc g * (e * r * (1 + e * g ^ 2)⁻¹) = (g * e * r) * (1 + e * g ^ 2)⁻¹ := by ring
      _ ≤ (1 + e * g ^ 2) * (1 + e * g ^ 2)⁻¹ := mul_le_mul_of_nonneg_right hX (inv_nonneg.2 hb0.le)
      _ = 1 := mul_inv_cancel₀ hb0.ne'
  have hpos : 0 ≤ M * e * r * (1 + e * g ^ 2)⁻¹ :=
    mul_nonneg (mul_nonneg (mul_nonneg hM he0) hr0.le) (inv_nonneg.2 hb0.le)
  have h1 : |s * r⁻¹ - M * e * r * (1 + e * g ^ 2)⁻¹| ≤ |s| * r⁻¹ + M * (e * r * (1 + e * g ^ 2)⁻¹) := by
    have h := norm_sub_le (s * r⁻¹) (M * e * r * (1 + e * g ^ 2)⁻¹)
    simp only [Real.norm_eq_abs] at h
    rw [abs_mul, abs_of_pos (inv_pos.2 hr0), abs_of_nonneg hpos] at h
    have e' : M * e * r * (1 + e * g ^ 2)⁻¹ = M * (e * r * (1 + e * g ^ 2)⁻¹) := by ring
    linarith
  have hsum : |s| * (g * r⁻¹) + M * (g * (e * r * (1 + e * g ^ 2)⁻¹)) ≤ |s| + M := by
    nlinarith [mul_le_mul_of_nonneg_left hgr' (abs_nonneg s), mul_le_mul_of_nonneg_left hgb hM]
  rw [abs_mul]
  calc |t| * |s * r⁻¹ - M * e * r * (1 + e * g ^ 2)⁻¹|
      ≤ (g * V) * (|s| * r⁻¹ + M * (e * r * (1 + e * g ^ 2)⁻¹)) :=
        mul_le_mul ht h1 (abs_nonneg _) (mul_nonneg hg hV)
    _ = V * (|s| * (g * r⁻¹) + M * (g * (e * r * (1 + e * g ^ 2)⁻¹))) := by ring
    _ ≤ V * (|s| + M) := mul_le_mul_of_nonneg_left hsum hV
    _ = (|s| + M) * V := by ring
end WD
end
end ZetaZeros.D.EllReg
end

set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
open ZetaZeros.D.EllReg.WD
variable {d : ℕ}
namespace ZetaZeros.D.EllReg.WD
theorem _root_.solution (s M ε : ℝ) (hM : 0 ≤ M) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (γ v : E d) :
    |(2 * inner ℝ γ v) * (s / 2) * (1 + ‖γ‖ ^ 2) ^ (s / 2 - 1) * (1 + ε ^ 2 * ‖γ‖ ^ 2) ^ (-(M / 2)) +
      (1 + ‖γ‖ ^ 2) ^ (s / 2) *
        ((ε ^ 2 * (2 * inner ℝ γ v)) * (-(M / 2)) * (1 + ε ^ 2 * ‖γ‖ ^ 2) ^ (-(M / 2) - 1))|
    ≤ (|s| + M) * ‖v‖ * om (s - 1) M ε γ := by
  have ha : (0 : ℝ) < 1 + ‖γ‖ ^ 2 := by positivity
  have hb : (0 : ℝ) < 1 + ε ^ 2 * ‖γ‖ ^ 2 := by positivity
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.sqrt (1 + ‖γ‖ ^ 2) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact Real.sqrt_pos.2 ha
  have hr2 : r ^ 2 = 1 + ‖γ‖ ^ 2 := by rw [hr]; exact Real.sq_sqrt ha.le
  have e1 : (1 + ‖γ‖ ^ 2) ^ (s / 2 - 1) = (1 + ‖γ‖ ^ 2) ^ ((s - 1) / 2) * r⁻¹ := by
    rw [hr, Real.sqrt_eq_rpow, ← Real.rpow_neg ha.le, ← Real.rpow_add ha]
    congr 1
    ring
  have e2 : (1 + ‖γ‖ ^ 2) ^ (s / 2) = (1 + ‖γ‖ ^ 2) ^ ((s - 1) / 2) * r := by
    rw [hr, Real.sqrt_eq_rpow, ← Real.rpow_add ha]
    congr 1
    ring
  have e3 : (1 + ε ^ 2 * ‖γ‖ ^ 2) ^ (-(M / 2) - 1) =
      (1 + ε ^ 2 * ‖γ‖ ^ 2) ^ (-(M / 2)) * (1 + ε ^ 2 * ‖γ‖ ^ 2)⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hb]
    congr 1
  have hP : 0 < (1 + ‖γ‖ ^ 2) ^ ((s - 1) / 2) := by positivity
  have hQ : 0 < (1 + ε ^ 2 * ‖γ‖ ^ 2) ^ (-(M / 2)) := by positivity
  have key := abs_mul_sub_le_of_sq_eq_one_add_sq ‖γ‖ (inner ℝ γ v) s M (ε ^ 2) r (1 + ε ^ 2 * ‖γ‖ ^ 2) ‖v‖
    (norm_nonneg _) (norm_nonneg _) (abs_real_inner_le_norm γ v) hM (sq_nonneg ε) hε2 hr0 hr2 rfl
  rw [e1, e2, e3]
  unfold ZetaZeros.D.EllReg.om
  calc _ = |((1 + ‖γ‖ ^ 2) ^ ((s - 1) / 2) * (1 + ε ^ 2 * ‖γ‖ ^ 2) ^ (-(M / 2))) *
        (inner ℝ γ v * (s * r⁻¹ - M * ε ^ 2 * r * (1 + ε ^ 2 * ‖γ‖ ^ 2)⁻¹))| := by
          congr 1
          ring
    _ = ((1 + ‖γ‖ ^ 2) ^ ((s - 1) / 2) * (1 + ε ^ 2 * ‖γ‖ ^ 2) ^ (-(M / 2))) *
        |inner ℝ γ v * (s * r⁻¹ - M * ε ^ 2 * r * (1 + ε ^ 2 * ‖γ‖ ^ 2)⁻¹)| := by
          rw [abs_mul, abs_of_pos (mul_pos hP hQ)]
    _ ≤ ((1 + ‖γ‖ ^ 2) ^ ((s - 1) / 2) * (1 + ε ^ 2 * ‖γ‖ ^ 2) ^ (-(M / 2))) * ((|s| + M) * ‖v‖) :=
          mul_le_mul_of_nonneg_left key (mul_pos hP hQ).le
    _ = _ := by ring
end ZetaZeros.D.EllReg.WD
