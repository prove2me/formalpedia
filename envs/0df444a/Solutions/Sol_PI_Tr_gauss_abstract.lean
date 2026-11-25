-- Prove2me | solution 1 for PI.Tr.gauss_abstract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:29:52.864664+00:00
-- url     : https://prove2.me/submissions/ab4aa82a-bf00-4573-b448-34c63029ef45

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeTransference_GaussAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped Real
namespace PI.Tr
private theorem summable_mul_of_nonneg_of_abs_le_one {ι : Type} {e θ : ι → ℝ} (he : Summable e)
    (he0 : ∀ i, 0 ≤ e i) (hθ : ∀ i, |θ i| ≤ 1) : Summable fun i => e i * θ i := by
  have h1 : Summable fun i => e i * θ i + e i := by
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (he.mul_left 2)
    · have := (abs_le.mp (hθ i)).1
      nlinarith [mul_nonneg (he0 i) (by linarith : 0 ≤ θ i + 1)]
    · have := (abs_le.mp (hθ i)).2
      nlinarith [mul_nonneg (he0 i) (by linarith : 0 ≤ 1 - θ i)]
  exact (h1.sub he).congr (fun i => by ring)
private theorem one_le_inv_of_pos_of_le_one {τ : ℝ} (h : 0 < τ) (h' : τ ≤ 1) : 1 ≤ τ⁻¹ := by
  have h1 := mul_inv_cancel₀ h.ne'
  nlinarith [mul_nonneg (inv_pos.mpr h).le (sub_nonneg.mpr h')]
end PI.Tr
end

set_option autoImplicit false
open scoped Real
open PI PI.Tr
namespace PI.Tr
theorem _root_.solution {X Y : Type} (a a0 : X → ℝ) (q θ : Y → ℝ) (n c : ℝ)
    (hq : ∀ y, 0 ≤ q y) (ha0 : ∀ x, 0 ≤ a0 x) (hθ : ∀ y, |θ y| ≤ 1) (hc : 0 < c) (y0 : Y)
    (sA : ∀ t : ℝ, 0 < t → Summable fun x => Real.exp (-π * t * a x))
    (compactWordAction : ∀ t : ℝ, 0 < t → Summable fun x => Real.exp (-π * t * a0 x))
    (sQ : ∀ t : ℝ, 0 < t → Summable fun y => Real.exp (-π * q y / t))
    (Pu : ∀ t : ℝ, 0 < t → ∑' x, Real.exp (-π * t * a x) =
      c * t ^ (-n / 2) * ∑' y, Real.exp (-π * q y / t) * θ y)
    (P0 : ∀ t : ℝ, 0 < t → ∑' x, Real.exp (-π * t * a0 x) =
      c * t ^ (-n / 2) * ∑' y, Real.exp (-π * q y / t))
    (R2 l2 : ℝ) (hR : ∀ x, R2 ≤ a x) (hl : ∀ y, q y < l2 → θ y = 1)
    (s τ₁ τ₂ : ℝ) (hs : 0 < s) (h1 : 0 < τ₁) (h1' : τ₁ ≤ 1) (h2 : 0 < τ₂) (h2' : τ₂ ≤ 1) :
    1 ≤ Real.exp (-π * s * (1 - τ₁) * R2) * τ₁ ^ (-n / 2) +
      2 * (Real.exp (-π * (1 - τ₂) * l2 / s) * τ₂ ^ (-n / 2)) := by
  have hπ : 0 < π := Real.pi_pos
  have hst1 : 0 < s * τ₁ := mul_pos hs h1
  have hst2 : 0 < s / τ₂ := div_pos hs h2
  have hQs := sQ s hs
  have hQ1 := sQ _ hst1
  have hQ2 := sQ _ hst2
  have hK : 0 < c * s ^ (-n / 2) := mul_pos hc (Real.rpow_pos_of_pos hs _)
  have hA : 0 < τ₁ ^ (-n / 2) := Real.rpow_pos_of_pos h1 _
  have hT : 0 < τ₂ ^ (-n / 2) := Real.rpow_pos_of_pos h2 _
  have hE1 : 0 < Real.exp (-π * s * (1 - τ₁) * R2) := Real.exp_pos _
  have hE2 : 0 < Real.exp (-π * (1 - τ₂) * l2 / s) := Real.exp_pos _
  have hS0pos : 0 < ∑' y, Real.exp (-π * q y / s) :=
    lt_of_lt_of_le (Real.exp_pos _)
      (le_hasSum hQs.hasSum y0 (fun j _ => (Real.exp_pos _).le))
  have up1 : ∑' x, Real.exp (-π * s * a x) ≤
      Real.exp (-π * s * (1 - τ₁) * R2) * ∑' x, Real.exp (-π * (s * τ₁) * a x) := by
    refine hasSum_le (fun x => ?_) (sA s hs).hasSum ((sA _ hst1).hasSum.mul_left _)
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h0 : 0 ≤ π * s * (1 - τ₁) := mul_nonneg (mul_nonneg hπ.le hs.le) (sub_nonneg.mpr h1')
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr (hR x))]
  have hle1 : ∑' y, Real.exp (-π * q y / (s * τ₁)) * θ y ≤ ∑' y, Real.exp (-π * q y / s) := by
    refine hasSum_le (fun y => ?_)
      (summable_mul_of_nonneg_of_abs_le_one hQ1 (fun _ => (Real.exp_pos _).le) hθ).hasSum hQs.hasSum
    have hθ1 := (abs_le.mp (hθ y)).2
    have he := Real.exp_pos (-π * q y / (s * τ₁))
    have hmono : Real.exp (-π * q y / (s * τ₁)) ≤ Real.exp (-π * q y / s) := by
      apply Real.exp_le_exp.mpr
      have hw : 0 ≤ π * q y / s := div_nonneg (mul_nonneg hπ.le (hq y)) hs.le
      have e1 : -π * q y / (s * τ₁) = -(π * q y / s) * τ₁⁻¹ := by ring
      have e2 : -π * q y / s = -(π * q y / s) := by ring
      have hinv := one_le_inv_of_pos_of_le_one h1 h1'
      rw [e1, e2]
      nlinarith [mul_nonneg hw (sub_nonneg.mpr hinv)]
    nlinarith [mul_nonneg he.le (sub_nonneg.mpr hθ1)]
  have up2 : ∑' x, Real.exp (-π * (s * τ₁) * a x) ≤
      c * s ^ (-n / 2) * (τ₁ ^ (-n / 2) * ∑' y, Real.exp (-π * q y / s)) := by
    rw [Pu _ hst1, Real.mul_rpow hs.le h1.le]
    calc c * (s ^ (-n / 2) * τ₁ ^ (-n / 2)) * ∑' y, Real.exp (-π * q y / (s * τ₁)) * θ y
        ≤ c * (s ^ (-n / 2) * τ₁ ^ (-n / 2)) * ∑' y, Real.exp (-π * q y / s) :=
          mul_le_mul_of_nonneg_left hle1
            (mul_pos hc (mul_pos (Real.rpow_pos_of_pos hs _) hA)).le
      _ = c * s ^ (-n / 2) * (τ₁ ^ (-n / 2) * ∑' y, Real.exp (-π * q y / s)) := by ring
  have hup : ∑' y, Real.exp (-π * q y / s) * θ y ≤
      Real.exp (-π * s * (1 - τ₁) * R2) * (τ₁ ^ (-n / 2) * ∑' y, Real.exp (-π * q y / s)) := by
    have h := (Pu s hs).symm.le.trans (up1.trans (mul_le_mul_of_nonneg_left up2 hE1.le))
    have h' : c * s ^ (-n / 2) * ∑' y, Real.exp (-π * q y / s) * θ y ≤
        c * s ^ (-n / 2) * (Real.exp (-π * s * (1 - τ₁) * R2) *
          (τ₁ ^ (-n / 2) * ∑' y, Real.exp (-π * q y / s))) := by
      calc _ ≤ _ := h
        _ = _ := by ring
    exact le_of_mul_le_mul_left h' hK
  have hlow : ∑' y, Real.exp (-π * q y / s) -
      2 * Real.exp (-π * (1 - τ₂) * l2 / s) * ∑' y, Real.exp (-π * q y / (s / τ₂)) ≤
      ∑' y, Real.exp (-π * q y / s) * θ y := by
    refine hasSum_le (fun y => ?_) (hQs.hasSum.sub (hQ2.hasSum.mul_left _))
      (summable_mul_of_nonneg_of_abs_le_one hQs (fun _ => (Real.exp_pos _).le) hθ).hasSum
    have he := Real.exp_pos (-π * q y / s)
    have hf := Real.exp_pos (-π * q y / (s / τ₂))
    have hprod : 0 < 2 * Real.exp (-π * (1 - τ₂) * l2 / s) * Real.exp (-π * q y / (s / τ₂)) :=
      mul_pos (mul_pos two_pos hE2) hf
    by_cases hql : q y < l2
    · rw [hl y hql, mul_one]
      linarith
    · have hql : l2 ≤ q y := not_lt.mp hql
      have hef : Real.exp (-π * q y / s) ≤
          Real.exp (-π * (1 - τ₂) * l2 / s) * Real.exp (-π * q y / (s / τ₂)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have e1 : -π * q y / (s / τ₂) = -π * q y * τ₂ / s := div_div_eq_mul_div _ _ _
        rw [e1]
        have key : -π * q y / s - (-π * (1 - τ₂) * l2 / s + -π * q y * τ₂ / s) =
            -(π * (1 - τ₂) * (q y - l2) / s) := by ring
        have hnn : 0 ≤ π * (1 - τ₂) * (q y - l2) / s :=
          div_nonneg (mul_nonneg (mul_nonneg hπ.le (sub_nonneg.mpr h2')) (sub_nonneg.mpr hql)) hs.le
        linarith
      have hθ0 := (abs_le.mp (hθ y)).1
      nlinarith [mul_nonneg he.le (by linarith : 0 ≤ θ y + 1)]
  have hfB : ∑' y, Real.exp (-π * q y / (s / τ₂)) ≤
      τ₂ ^ (-n / 2) * ∑' y, Real.exp (-π * q y / s) := by
    have m : ∑' x, Real.exp (-π * (s / τ₂) * a0 x) ≤ ∑' x, Real.exp (-π * s * a0 x) := by
      refine hasSum_le (fun x => ?_) (compactWordAction _ hst2).hasSum (compactWordAction s hs).hasSum
      apply Real.exp_le_exp.mpr
      have hinv := one_le_inv_of_pos_of_le_one h2 h2'
      have hsle : s ≤ s / τ₂ := by
        rw [div_eq_mul_inv]
        nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hinv)]
      nlinarith [mul_nonneg (mul_nonneg hπ.le (ha0 x)) (sub_nonneg.mpr hsle)]
    rw [P0 _ hst2, P0 s hs, Real.div_rpow hs.le h2.le] at m
    have hPT : s ^ (-n / 2) / τ₂ ^ (-n / 2) * τ₂ ^ (-n / 2) = s ^ (-n / 2) := by
      field_simp [hT.ne']
    have m3 : c * s ^ (-n / 2) * ∑' y, Real.exp (-π * q y / (s / τ₂)) ≤
        c * s ^ (-n / 2) * (τ₂ ^ (-n / 2) * ∑' y, Real.exp (-π * q y / s)) := by
      have m2 := mul_le_mul_of_nonneg_right m hT.le
      calc c * s ^ (-n / 2) * ∑' y, Real.exp (-π * q y / (s / τ₂))
          = c * (s ^ (-n / 2) / τ₂ ^ (-n / 2) * τ₂ ^ (-n / 2)) *
              ∑' y, Real.exp (-π * q y / (s / τ₂)) := by rw [hPT]
        _ = (c * (s ^ (-n / 2) / τ₂ ^ (-n / 2)) * ∑' y, Real.exp (-π * q y / (s / τ₂))) *
              τ₂ ^ (-n / 2) := by ring
        _ ≤ (c * s ^ (-n / 2) * ∑' y, Real.exp (-π * q y / s)) * τ₂ ^ (-n / 2) := m2
        _ = c * s ^ (-n / 2) * (τ₂ ^ (-n / 2) * ∑' y, Real.exp (-π * q y / s)) := by ring
    exact le_of_mul_le_mul_left m3 hK
  have hfin : (∑' y, Real.exp (-π * q y / s)) * 1 ≤
      (∑' y, Real.exp (-π * q y / s)) * (Real.exp (-π * s * (1 - τ₁) * R2) * τ₁ ^ (-n / 2) +
        2 * (Real.exp (-π * (1 - τ₂) * l2 / s) * τ₂ ^ (-n / 2))) := by
    nlinarith [mul_le_mul_of_nonneg_left hfB (mul_pos two_pos hE2).le]
  exact le_of_mul_le_mul_left hfin hS0pos
end PI.Tr
