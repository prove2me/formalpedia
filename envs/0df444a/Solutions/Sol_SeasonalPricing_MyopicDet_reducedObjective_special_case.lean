-- Prove2me | solution 1 for SeasonalPricing.MyopicDet.reducedObjective_special_case
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T11:22:19.684953+00:00
-- url     : https://prove2.me/submissions/fc9b0dfe-ed29-47e8-9114-3290e3fb74d8

import Definitions.Def_SeasonalPricing_MyopicDet_reducedObjective
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic
open Set
open SeasonalPricing.MyopicDet

private theorem log_minimum (C x : ℝ) (hx : 0 < x) :
    -Real.exp (C-1) ≤ x*(Real.log x-C) ∧
      (x*(Real.log x-C) = -Real.exp (C-1) → x=Real.exp (C-1)) := by
  let q := Real.exp (C-1)
  have hq : 0 < q := Real.exp_pos _
  have he : q*((x/q)*Real.log (x/q)-(x/q)+1)=x*(Real.log x-C)+q := by
    rw [Real.log_div hx.ne' hq.ne']
    rw [show Real.log q=C-1 from Real.log_exp _]
    field_simp
    ring
  have h1:=Real.self_sub_one_le_mul_log (div_pos hx hq).le
  have h2:=mul_nonneg hq.le (sub_nonneg.mpr h1)
  have hl : -q ≤ x*(Real.log x-C) := by nlinarith
  refine ⟨hl,?_⟩
  intro hh
  by_contra hne
  have hne' : x/q ≠ 1 := by intro heq; apply hne; exact (div_eq_one_iff_eq hq.ne').mp heq
  have h3:=Real.self_sub_one_lt_mul_log (div_pos hx hq).le hne'
  have h4:=mul_pos hq (sub_pos.mpr h3)
  change x*(Real.log x-C) = -q at hh
  nlinarith

private theorem numerator_bound (p1 p2 : ℝ) (h1 : 0 < p1) (h2 : 0 < p2) :
    -Real.exp (-1+Real.exp (-1)) ≤ (p1-p2)*Real.log p1+p2*Real.log p2 ∧
    ((p1-p2)*Real.log p1+p2*Real.log p2 = -Real.exp (-1+Real.exp (-1)) →
      p1=Real.exp (-1+Real.exp (-1)) ∧ p2=p1/Real.exp 1) := by
  let r := p2/p1
  have hr : 0 < r := div_pos h2 h1
  have hminr:=log_minimum 0 r hr
  have hminp:=log_minimum (Real.exp (-1)) p1 h1
  simp only [sub_zero,zero_sub] at hminr
  rw [show Real.exp (-1)-1 = -1+Real.exp (-1) by ring] at hminp
  have he : (p1-p2)*Real.log p1+p2*Real.log p2 = p1*(Real.log p1+r*Real.log r) := by
    dsimp [r]
    rw [Real.log_div h2.ne' h1.ne']
    field_simp
    ring
  have hh:=mul_le_mul_of_nonneg_left hminr.1 h1.le
  have hl : -Real.exp (-1+Real.exp (-1)) ≤ (p1-p2)*Real.log p1+p2*Real.log p2 := by
    rw [he]
    nlinarith [hminp.1]
  refine ⟨hl,?_⟩
  intro heq
  rw [he] at heq
  have hpEq : p1*(Real.log p1-Real.exp (-1)) = -Real.exp (-1+Real.exp (-1)) := by
    nlinarith [hminp.1]
  have hrEq : r*Real.log r = -Real.exp (-1) := by nlinarith
  have hp:=hminp.2 hpEq
  have hr':=hminr.2 hrEq
  refine ⟨hp,?_⟩
  dsimp [r] at hr'
  rw [Real.exp_neg] at hr'
  have heq := (div_eq_iff h1.ne').mp hr'
  simpa [div_eq_mul_inv,mul_comm] using heq

private theorem optimum_values :
    (0 < Real.exp (-1+Real.exp (-1))) ∧
    (Real.exp (-1+Real.exp (-1)) ≤ 1) ∧
    (Real.exp (-1+Real.exp (-1))/Real.exp 1 = Real.exp (-2+Real.exp (-1))) ∧
    (Real.exp (-1+Real.exp (-1))/Real.exp 1 ≤ Real.exp (-1+Real.exp (-1))) := by
  have he : Real.exp (-1) < 1 := by exact Real.exp_lt_one_iff.mpr (by norm_num)
  refine ⟨Real.exp_pos _,Real.exp_le_one_iff.mpr (by linarith),?_,?_⟩
  · rw [←Real.exp_sub]
    congr 1
    ring
  · exact div_le_self (Real.exp_pos _).le (Real.one_le_exp_iff.mpr (by norm_num))

private theorem optimal_numerator :
    (Real.exp (-1+Real.exp (-1))-Real.exp (-1+Real.exp (-1))/Real.exp 1)*Real.log (Real.exp (-1+Real.exp (-1)))
      +(Real.exp (-1+Real.exp (-1))/Real.exp 1)*Real.log (Real.exp (-1+Real.exp (-1))/Real.exp 1)
      = -Real.exp (-1+Real.exp (-1)) := by
  rw [Real.log_div (Real.exp_pos _).ne' (Real.exp_pos _).ne',Real.log_exp,Real.log_exp]
  rw [Real.exp_neg]
  field_simp
  ring

theorem solution (ρ : ℝ) (hρ0 : 0 < ρ)
    (hρ : ρ ≤ Real.exp (-2 + Real.exp (-1))) :
    IsGreatest {g : ℝ | ∃ p1 p2 : ℝ, ρ ≤ p2 ∧ p2 ≤ p1 ∧ p1 ≤ 1 ∧ g = reducedObjective ρ p1 p2}
        (-Real.exp (-1 + Real.exp (-1)) / Real.log ρ) ∧
      ρ ≤ Real.exp (-1 + Real.exp (-1)) / Real.exp 1 ∧
      Real.exp (-1 + Real.exp (-1)) ≤ 1 ∧
      reducedObjective ρ (Real.exp (-1 + Real.exp (-1)))
          (Real.exp (-1 + Real.exp (-1)) / Real.exp 1) =
        -Real.exp (-1 + Real.exp (-1)) / Real.log ρ ∧
      ∀ p1 p2 : ℝ, ρ ≤ p2 → p2 ≤ p1 → p1 ≤ 1 →
        reducedObjective ρ p1 p2 = -Real.exp (-1 + Real.exp (-1)) / Real.log ρ →
          p1 = Real.exp (-1 + Real.exp (-1)) ∧ p2 = Real.exp (-1 + Real.exp (-1)) / Real.exp 1 := by
  obtain ⟨hp0,hp1,heq,hp12⟩:=optimum_values
  have hp2 : ρ ≤ Real.exp (-1+Real.exp (-1))/Real.exp 1 := by rwa [heq]
  have hρ1 : ρ < 1 := by
    have hh : Real.exp (-2+Real.exp (-1)) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith [Real.exp_lt_one_iff.mpr (by norm_num : (-1:ℝ)<0)])
    exact hρ.trans_lt hh
  have hl : Real.log ρ < 0 := Real.log_neg hρ0 hρ1
  have hid : ∀ p1 p2,reducedObjective ρ p1 p2 =
      ((p1-p2)*Real.log p1+p2*Real.log p2)/Real.log ρ := by
    intro p1 p2
    unfold reducedObjective
    ring
  have hop : reducedObjective ρ (Real.exp (-1+Real.exp (-1)))
      (Real.exp (-1+Real.exp (-1))/Real.exp 1) = -Real.exp (-1+Real.exp (-1))/Real.log ρ := by
    rw [hid,optimal_numerator]
  refine ⟨⟨?_,?_⟩,hp2,hp1,hop,?_⟩
  · exact ⟨_,_,hp2,hp12,hp1,hop.symm⟩
  · rintro g ⟨p1,p2,hp2',hp12',hp1',rfl⟩
    rw [hid]
    exact (div_le_div_right_of_neg hl).mpr (numerator_bound p1 p2
      (hρ0.trans_le (hp2'.trans hp12')) (hρ0.trans_le hp2')).1
  · intro p1 p2 hp2' hp12' hp1' hop'
    rw [hid] at hop'
    have he := (div_left_inj' hl.ne).mp hop'
    obtain ⟨h1,h2⟩:=(numerator_bound p1 p2 (hρ0.trans_le (hp2'.trans hp12'))
      (hρ0.trans_le hp2')).2 he
    exact ⟨h1,by simpa [h1] using h2⟩
