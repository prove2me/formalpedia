-- Prove2me | solution 1 for Shoppertainment.OptimalBandwidth.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:42:26.650977+00:00
-- url     : https://prove2.me/submissions/1307b4b1-0ce7-4785-a7c2-4c54a9c607e8

import Mathlib
import Definitions.Def_Shoppertainment_OptimalBandwidth_Model

set_option autoImplicit false
open Shoppertainment.OptimalBandwidth

lemma sho_split (a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b) (F G g : ℝ → ℝ)
    (hF : Continuous F) (hG : Continuous G)
    (hg1 : ∀ x, a < x → x < c → g x = F x) (hg2 : ∀ x, c < x → x < b → g x = G x) :
    ∫ x in a..b, g x = (∫ x in a..c, F x) + ∫ x in c..b, G x := by
  have e1 : Set.EqOn F g (Set.uIoo a c) := by
    intro x hx
    rw [Set.uIoo_of_le hac] at hx
    exact (hg1 x hx.1 hx.2).symm
  have e2 : Set.EqOn G g (Set.uIoo c b) := by
    intro x hx
    rw [Set.uIoo_of_le hcb] at hx
    exact (hg2 x hx.1 hx.2).symm
  have i1 : IntervalIntegrable g MeasureTheory.volume a c :=
    (hF.intervalIntegrable a c).congr_uIoo e1
  have i2 : IntervalIntegrable g MeasureTheory.volume c b :=
    (hG.intervalIntegrable c b).congr_uIoo e2
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2]
  congr 1
  · exact intervalIntegral.integral_congr_uIoo e1.symm
  · exact intervalIntegral.integral_congr_uIoo e2.symm

lemma sho_surplus_low (v te q : ℝ) (hv : 0 < v) (hte1 : te ≤ 1) :
    buyerSurplus v te q (pL v te q) = (1 - te) * q * v := by
  unfold buyerSurplus
  have : pH v te q - pL v te q = (1 - te) * v := by unfold pH pL; ring
  rw [this, sub_self, max_self, max_eq_left (mul_nonneg (by linarith) hv.le)]
  ring

lemma sho_surplus_high (v te q : ℝ) (hv : 0 < v) (hte1 : te ≤ 1) :
    buyerSurplus v te q (pH v te q) = 0 := by
  unfold buyerSurplus
  have : pL v te q - pH v te q = -((1 - te) * v) := by unfold pH pL; ring
  rw [this, sub_self, max_self, max_eq_right (by nlinarith)]
  ring

theorem solution (v ql : ℝ) (hv : 0 < v) (hql : 0 ≤ ql) (hql1 : ql < 1) :
    ∀ te ∈ Set.Icc (0:ℝ) 1, Eup v ql te =
      if teHat ql < te then (1 / (1 - ql)) * ∫ q in ql..qHat te, (1 - te) * q * v else 0 := by
  intro te ⟨hte0, hte1⟩
  unfold Eup
  split_ifs with hlt
  · congr 1
    have h2ql : 0 < 2 - ql := by linarith
    have hte : 0 < te := lt_of_le_of_lt (by unfold teHat; positivity) hlt
    unfold teHat at hlt
    rw [div_lt_iff₀ h2ql] at hlt
    have hq1 : ql < qHat te := by
      unfold qHat
      have : 1 / te < 2 - ql := by rw [div_lt_iff₀ hte]; linarith
      linarith
    have hq2 : qHat te ≤ 1 := by
      unfold qHat
      have : 1 ≤ 1 / te := by rw [le_div_iff₀ hte]; linarith
      linarith
    have key := sho_split ql (qHat te) 1 hq1.le hq2
      (fun q => (1 - te) * q * v) (fun _ => 0)
      (fun q => buyerSurplus v te q (eqPrice v te q))
      (by fun_prop) continuous_const ?_ ?_
    · rw [key]; simp
    · intro x hx1 hx2
      have h1 : 1 / (2 - x) < te := by
        have hx : 0 < 2 - x := by unfold qHat at hx2; have : 0 < 1 / te := by positivity
                                  linarith
        rw [div_lt_iff₀ hx]
        have : 1 / te < 2 - x := by unfold qHat at hx2; linarith
        rw [div_lt_iff₀ hte] at this
        linarith
      show buyerSurplus v te x (eqPrice v te x) = _
      unfold eqPrice
      rw [if_pos h1, sho_surplus_low v te x hv hte1]
    · intro x hx1 hx2
      have h1 : ¬ 1 / (2 - x) < te := by
        have hx : 0 < 2 - x := by linarith
        rw [not_lt, le_div_iff₀ hx]
        have : 2 - x < 1 / te := by unfold qHat at hx1; linarith
        rw [lt_div_iff₀ hte] at this
        linarith
      show buyerSurplus v te x (eqPrice v te x) = _
      unfold eqPrice
      rw [if_neg h1, sho_surplus_high v te x hv hte1]
  · have : ∫ q in ql..1, buyerSurplus v te q (eqPrice v te q) = 0 := by
      have : ∫ q in ql..1, buyerSurplus v te q (eqPrice v te q) = ∫ q in ql..1, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hql1.le] at hx
        have h1 : ¬ 1 / (2 - x) < te := by
          have hx2 : 0 < 2 - x := by linarith [hx.2]
          rw [not_lt]
          have : te ≤ 1 / (2 - ql) := by unfold teHat at hlt; exact not_lt.1 hlt
          refine this.trans ?_
          exact one_div_le_one_div_of_le hx2 (by linarith [hx.1])
        show buyerSurplus v te x (eqPrice v te x) = _
        unfold eqPrice
        rw [if_neg h1, sho_surplus_high v te x hv hte1]
      rw [this]; simp
    rw [this]; simp
