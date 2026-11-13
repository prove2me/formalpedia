-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.weak_ks_from_variational
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T04:02:38.74935+00:00
-- url     : https://prove2.me/submissions/2435d6c9-ed14-4fcb-b04b-4c538aaa932b

import Mathlib
import Theorems.Thm_ZeroFreeRRG_Hardcore_ks_fourth_order_witness
open scoped Classical
namespace ZeroFreeRRG.Hardcore

private lemma coefficient_nonpos (A C ε₀ : ℝ) (hC : 0 < C) (hε₀ : 0 < ε₀)
    (hbound : ∀ ε : ℝ, 0 < ε → ε < ε₀ → A*ε^4 - C*ε^6 ≤ 0) : A ≤ 0 := by
  by_contra hn
  have hA : 0 < A := lt_of_not_ge hn
  let ε : ℝ := min (ε₀/2) (min 1 (A / (2*(C+1))))
  have hεpos : 0 < ε := by
    dsimp [ε]
    apply lt_min (by positivity)
    apply lt_min (by positivity)
    positivity
  have hεlt : ε < ε₀ := by
    have he := min_le_left (ε₀/2) (min 1 (A/(2*(C+1))))
    dsimp [ε] at *
    linarith
  have hεle1 : ε ≤ 1 := by
    dsimp [ε]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hεbound : ε ≤ A / (2*(C+1)) := by
    dsimp [ε]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hsq : ε^2 ≤ ε := by nlinarith
  have hmul : ε * (2*(C+1)) ≤ A := (le_div_iff₀ (by positivity)).mp hεbound
  have hdiff : 0 < A - C*ε^2 := by
    nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hsq)]
  have hpos : 0 < (A - C*ε^2)*ε^4 := mul_pos hdiff (pow_pos hεpos _)
  have hzero : (A - C*ε^2)*ε^4 ≤ 0 := by
    have hh := hbound ε hεpos hεlt
    nlinarith [hh]
  exact (not_lt_of_ge hzero) hpos
end ZeroFreeRRG.Hardcore

namespace ZeroFreeRRG.Hardcore

theorem _root_.solution (d q : ℕ) (hd : 3 ≤ d) (hq : 2 ≤ q) :
    (∀ α : ℝ, 0 < α → α < 1 / 2 → VariationalRS .hardcore d α →
       ((d : ℝ) - 1) * (α / (1 - α)) ^ 2 ≤ 1) ∧
    (∀ β : ℝ, 0 ≤ β → β < 1 → VariationalRS (.potts q) d β →
       ((d : ℝ) - 1) * ((1 - β) / ((q : ℝ) - 1 + β)) ^ 2 ≤ 1) := by
  have hd' : (3:ℝ) ≤ d := by exact_mod_cast hd
  have hq' : (2:ℝ) ≤ q := by exact_mod_cast hq
  constructor
  · intro α hα hα2 hrs
    have ha : 0 < α/(1-α) := div_pos hα (by linarith)
    obtain ⟨C, ε₀, hC, hε₀, hwitness⟩ :=
      (ks_fourth_order_witness d q hd hq).1 α hα hα2
    have hbound : ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ((d:ℝ)/4)*(α/(1-α))^2*(((d:ℝ)-1)*(α/(1-α))^2-1)*ε^4 - C*ε^6 ≤ 0 := by
      intro ε hε hε'
      obtain ⟨ν, hν, hνbound⟩ := hwitness ε hε hε'
      exact hνbound.trans (hrs ν hν)
    have hcoef := coefficient_nonpos _ C ε₀ hC hε₀ hbound
    have hfactor : 0 < ((d:ℝ)/4) * (α/(1-α))^2 := by positivity
    have hbracket : ((d:ℝ)-1)*(α/(1-α))^2-1 ≤ 0 :=
      nonpos_of_mul_nonpos_right hcoef hfactor
    linarith
  · intro β hβ hβ1 hrs
    have hb : 0 < (1-β)/((q:ℝ)-1+β) := div_pos (by linarith) (by linarith)
    obtain ⟨C, ε₀, hC, hε₀, hwitness⟩ :=
      (ks_fourth_order_witness d q hd hq).2 β hβ hβ1
    have hbound : ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ((d:ℝ)/4)*((1-β)/((q:ℝ)-1+β))^2*
          (((d:ℝ)-1)*((1-β)/((q:ℝ)-1+β))^2-1)*ε^4 - C*ε^6 ≤ 0 := by
      intro ε hε hε'
      obtain ⟨ν, hν, hνbound⟩ := hwitness ε hε hε'
      exact hνbound.trans (hrs ν hν)
    have hcoef := coefficient_nonpos _ C ε₀ hC hε₀ hbound
    have hfactor : 0 < ((d:ℝ)/4) * ((1-β)/((q:ℝ)-1+β))^2 := by positivity
    have hbracket : ((d:ℝ)-1)*((1-β)/((q:ℝ)-1+β))^2-1 ≤ 0 :=
      nonpos_of_mul_nonpos_right hcoef hfactor
    linarith
end ZeroFreeRRG.Hardcore
