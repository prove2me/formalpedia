-- Prove2me | solution 1 for RiskBalancingMNL.markup_share_inverse
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T05:47:04.875829+00:00
-- url     : https://prove2.me/submissions/81ccd2e2-c741-4b44-b0bc-4c4f127bb763

import Mathlib
import Definitions.Def_RiskBalancingMNL_Params
import Definitions.Def_RiskBalancingMNL_mHat

open RiskBalancingMNL in
theorem solution {n : ℕ} [NeZero n] (P : Params n) :
    (∀ m : Fin n → ℝ,
      (∀ i, 0 < share P m i) ∧ 0 < noPurchase P m ∧
      noPurchase P m + ∑ i, share P m i = 1 ∧
      (∀ i, share P m i / noPurchase P m = Real.exp (P.a i - P.b * P.c i - P.b * m i)) ∧
      ∀ i, m i = (P.a i + Real.log (noPurchase P m) - Real.log (share P m i)) / P.b - P.c i) ∧
    (∀ x : ℝ, 0 < x → x < 1 → noPurchase P (constM (mHat P x)) = x) ∧
    (∀ t : ℝ, mHat P (noPurchase P (constM t)) = t) ∧
    StrictMonoOn (mHat P) (Set.Ioo 0 1) := by
  have hb := P.hb
  have hbne : P.b ≠ 0 := hb.ne'
  have hZ : 0 < zeroMarkupMass P := by
    unfold zeroMarkupMass
    exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have hsumc : ∀ t : ℝ, ∑ j, attraction P (constM t) j =
      zeroMarkupMass P * Real.exp (-(P.b * t)) := by
    intro t
    unfold attraction constM zeroMarkupMass
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Real.exp_add]
    ring_nf
  refine ⟨fun m => ?_, fun x hx0 hx1 => ?_, fun t => ?_, ?_⟩
  · have hA : ∀ i, 0 < attraction P m i := fun i => Real.exp_pos _
    have hS : 0 ≤ ∑ j, attraction P m j := Finset.sum_nonneg fun j _ => (hA j).le
    have hS1 : 0 < (∑ j, attraction P m j) + 1 := by linarith
    have hS1' : 0 < 1 + ∑ j, attraction P m j := by linarith
    have hS1n := hS1.ne'
    have hS1n' := hS1'.ne'
    have hshare : ∀ i, share P m i = attraction P m i / ((∑ j, attraction P m j) + 1) :=
      fun i => rfl
    have hq : noPurchase P m = 1 / (1 + ∑ j, attraction P m j) := rfl
    refine ⟨fun i => ?_, ?_, ?_, fun i => ?_, fun i => ?_⟩
    · rw [hshare]; exact div_pos (hA i) hS1
    · rw [hq]; exact div_pos one_pos hS1'
    · rw [hq]
      simp only [hshare]
      rw [← Finset.sum_div]
      field_simp <;> ring
    · rw [hq, hshare]
      have : Real.exp (P.a i - P.b * P.c i - P.b * m i) = attraction P m i := rfl
      rw [this]
      field_simp <;> ring
    · have hAn := (hA i).ne'
      have hsq : share P m i = attraction P m i * noPurchase P m := by
        rw [hq, hshare]; field_simp <;> ring
      rw [hsq, Real.log_mul hAn (by rw [hq]; exact (div_pos one_pos hS1').ne')]
      have : Real.log (attraction P m i) = P.a i - P.b * P.c i - P.b * m i := by
        unfold attraction; exact Real.log_exp _
      rw [this]
      have e : P.a i + Real.log (noPurchase P m) -
          (P.a i - P.b * P.c i - P.b * m i + Real.log (noPurchase P m)) =
          P.b * (m i + P.c i) := by ring
      rw [e, mul_div_cancel_left₀ _ hbne]
      ring
  · have hx1' : 0 < 1 - x := by linarith
    have hxx : 0 < x / (1 - x) := div_pos hx0 hx1'
    have hxn := hx0.ne'
    have hx1n := hx1'.ne'
    have hZn := hZ.ne'
    have hbm : P.b * mHat P x = Real.log (zeroMarkupMass P) + Real.log (x / (1 - x)) := by
      unfold mHat; rw [mul_comm]; exact div_mul_cancel₀ _ hbne
    have hE : Real.exp (-(P.b * mHat P x)) = (1 - x) / (zeroMarkupMass P * x) := by
      rw [hbm, Real.exp_neg, Real.exp_add, Real.exp_log hZ, Real.exp_log hxx]
      field_simp
    unfold noPurchase
    rw [hsumc, hE]
    field_simp <;> ring
  · have hE := Real.exp_pos (-(P.b * t))
    have hZE : 0 < zeroMarkupMass P * Real.exp (-(P.b * t)) := mul_pos hZ hE
    have hq : noPurchase P (constM t) = 1 / (1 + zeroMarkupMass P * Real.exp (-(P.b * t))) := by
      unfold noPurchase; rw [hsumc]
    have hu := hZE.ne'
    have h1 : (1 : ℝ) + zeroMarkupMass P * Real.exp (-(P.b * t)) ≠ 0 := by linarith
    have h1q : 1 - 1 / (1 + zeroMarkupMass P * Real.exp (-(P.b * t))) =
        zeroMarkupMass P * Real.exp (-(P.b * t)) /
          (1 + zeroMarkupMass P * Real.exp (-(P.b * t))) := by
      field_simp <;> ring
    have hratio : noPurchase P (constM t) / (1 - noPurchase P (constM t)) =
        1 / (zeroMarkupMass P * Real.exp (-(P.b * t))) := by
      rw [hq, h1q]
      field_simp
    unfold mHat
    rw [hratio, one_div, Real.log_inv, Real.log_mul hZ.ne' hE.ne', Real.log_exp]
    have e : Real.log (zeroMarkupMass P) + -(Real.log (zeroMarkupMass P) + -(P.b * t)) =
        P.b * t := by ring
    rw [e, mul_div_cancel_left₀ _ hbne]
  · intro x hx y hy hxy
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨hy0, hy1⟩ := hy
    unfold mHat
    rw [div_lt_div_iff_of_pos_right hb]
    apply (add_lt_add_iff_left _).mpr
    apply Real.log_lt_log (div_pos hx0 (by linarith))
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
