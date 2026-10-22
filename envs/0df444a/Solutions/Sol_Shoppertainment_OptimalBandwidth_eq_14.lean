-- Prove2me | solution 1 for Shoppertainment.OptimalBandwidth.eq_14
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:48:57.671144+00:00
-- url     : https://prove2.me/submissions/bb215ef5-d5e9-47a8-ab11-3efe34b10c6c

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

lemma sho_rpc_low (v te q : ℝ) :
    revenuePerConsumer v te q (pL v te q) = pL v te q := by
  unfold revenuePerConsumer
  rw [if_pos le_rfl, mul_one]

lemma sho_rpc_high (v te q : ℝ) (hv : 0 < v) (hte : te < 1) :
    revenuePerConsumer v te q (pH v te q) = pH v te q * q := by
  unfold revenuePerConsumer
  have : ¬ pH v te q ≤ pL v te q := by
    unfold pH pL; nlinarith
  rw [if_neg this, if_pos le_rfl]

theorem solution (α v ql : ℝ) (hα : 0 < α) (hα1 : α < 1) (hv : 0 < v) (hql : 0 ≤ ql) (hql1 : ql < 1) :
    ∀ te ∈ Set.Icc (0:ℝ) 1, profitability α v ql te =
      if teHat ql < te then
        α * ((1 / (1 - ql)) * (∫ q in ql..qHat te, pL v te q) +
          (1 / (1 - ql)) * ∫ q in qHat te..1, pH v te q * q)
      else α * ((1 / (1 - ql)) * ∫ q in ql..1, pH v te q * q) := by
  intro te ⟨hte0, hte1⟩
  unfold profitability
  split_ifs with hlt
  · have h2ql : 0 < 2 - ql := by linarith
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
      (fun q => pL v te q) (fun q => pH v te q * q)
      (fun q => revenuePerConsumer v te q (eqPrice v te q))
      (by unfold pL; fun_prop) (by unfold pH; fun_prop) ?_ ?_
    · rw [key]; ring
    · intro x hx1 hx2
      have h1 : 1 / (2 - x) < te := by
        have hx : 0 < 2 - x := by
          unfold qHat at hx2
          have : 0 < 1 / te := by positivity
          linarith
        rw [div_lt_iff₀ hx]
        have : 1 / te < 2 - x := by unfold qHat at hx2; linarith
        rw [div_lt_iff₀ hte] at this
        linarith
      show revenuePerConsumer v te x (eqPrice v te x) = _
      unfold eqPrice
      rw [if_pos h1, sho_rpc_low]
    · intro x hx1 hx2
      have h1 : ¬ 1 / (2 - x) < te := by
        have hx : 0 < 2 - x := by linarith
        rw [not_lt, le_div_iff₀ hx]
        have : 2 - x < 1 / te := by unfold qHat at hx1; linarith
        rw [lt_div_iff₀ hte] at this
        linarith
      have hte' : te < 1 := by
        unfold qHat at hx1
        have h3 : 1 < 1 / te := by linarith
        rw [lt_div_iff₀ hte] at h3
        linarith
      show revenuePerConsumer v te x (eqPrice v te x) = _
      unfold eqPrice
      rw [if_neg h1, sho_rpc_high v te x hv hte']
  · have hteHat : te ≤ 1 / (2 - ql) := by unfold teHat at hlt; exact not_lt.1 hlt
    have hte' : te < 1 := by
      have : 1 / (2 - ql) < 1 := by
        rw [div_lt_iff₀ (by linarith)]; linarith
      linarith
    have : ∫ q in ql..1, revenuePerConsumer v te q (eqPrice v te q) = ∫ q in ql..1, pH v te q * q := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hql1.le] at hx
      have h1 : ¬ 1 / (2 - x) < te := by
        have hx2 : 0 < 2 - x := by linarith [hx.2]
        rw [not_lt]
        refine hteHat.trans ?_
        exact one_div_le_one_div_of_le hx2 (by linarith [hx.1])
      show revenuePerConsumer v te x (eqPrice v te x) = _
      unfold eqPrice
      rw [if_neg h1, sho_rpc_high v te x hv hte']
    rw [this]
