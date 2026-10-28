-- Prove2me | solution 1 for RobustGeneralization.BernLower.posterior_mean_bound
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-24T06:51:33.36848+00:00
-- url     : https://prove2.me/submissions/0ae7de51-d711-4e63-a7b6-666b37a38880

import Init
import Mathlib
import Definitions.Def_RobustGeneralization_BernLower_Model

namespace RobustGeneralization.BernLower

theorem aux_eq5odds_bern1W_pos (θ : Bool) (τ : ℝ) (hτ : 0 < τ) (hτ' : τ < 1 / 2)
    (p : Bool × Bool) : 0 < bern1W θ τ p := by
  have ha : (0 : ℝ) < 1 / 2 + τ := by linarith
  have hb : (0 : ℝ) < 1 / 2 - τ := by linarith
  unfold bern1W
  split_ifs
  · exact mul_pos (by norm_num) ha
  · exact mul_pos (by norm_num) hb

end RobustGeneralization.BernLower

open RobustGeneralization.BernLower

theorem RobustGeneralization.BernLower.odds_eq_product (n : ℕ) (τ : ℝ) (hτ : 0 < τ) (hτ' : τ < 1 / 2)
    (S : Fin n → Bool × Bool) :
    odds1 τ S = ∏ k, ((1 / 2 + τ) / (1 / 2 - τ)) ^ (lab (S k).2 * lab (S k).1) := by
  have ha : (0 : ℝ) < 1 / 2 + τ := by linarith
  have hb : (0 : ℝ) < 1 / 2 - τ := by linarith
  have hJ : ∀ θ, 0 < joint1 τ θ S := fun θ => by
    unfold joint1
    exact mul_pos (by norm_num)
      (Finset.prod_pos fun k _ => aux_eq5odds_bern1W_pos θ τ hτ hτ' (S k))
  have hD : (∑ θ : Bool, joint1 τ θ S) ≠ 0 := by
    rw [Fintype.sum_bool]
    exact ne_of_gt (add_pos (hJ true) (hJ false))
  unfold odds1 post1
  rw [div_div_div_cancel_right₀ hD]
  unfold joint1
  rw [mul_div_mul_left _ _ (by norm_num : (1 / 2 : ℝ) ≠ 0), ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro k _
  obtain ⟨x, y⟩ := S k
  cases x <;> cases y <;>
    simp [bern1W, lab, Real.rpow_neg_one, mul_div_mul_left _ _ (by norm_num : (2⁻¹ : ℝ) ≠ 0)]

open MeasureTheory ProbabilityTheory Finset
namespace FiniteHoeffding
variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
noncomputable def law (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hs : ∑ x, w x = 1) : PMF Ω :=
  PMF.ofFintype (fun x => ENNReal.ofReal (w x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hw x), hs]
    simp)

theorem integral_law (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hs : ∑ x, w x = 1) (f : Ω → ℝ) :
    (∫ x, f x ∂(law w hw hs).toMeasure) = ∑ x, w x * f x := by
  rw [PMF.integral_eq_sum]
  simp [law,ENNReal.toReal_ofReal,hw,smul_eq_mul]

theorem one_mgf (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hs : ∑ x, w x = 1)
    (X : Ω → ℝ) (hX : ∀ x, X x ∈ Set.Icc (-1) 1) (t : ℝ) :
    (∑ x, w x * Real.exp (t * (X x - ∑ y, w y * X y))) ≤ Real.exp (t^2/2) := by
  have hsub := hasSubgaussianMGF_of_mem_Icc
    (μ := (law w hw hs).toMeasure) (X := X) (measurable_of_finite X).aemeasurable
    (Filter.Eventually.of_forall hX)
  have hb := hsub.mgf_le t
  norm_num [mgf,integral_law] at hb
  exact hb

theorem product_mgf (w : Ω → ℝ) (X : Ω → ℝ) (n : ℕ) (t m : ℝ) :
    (∑ S : Fin n → Ω, (∏ i, w (S i)) * Real.exp (t * ((∑ i, X (S i)) - n*m))) =
      (∑ x, w x * Real.exp (t * (X x-m)))^n := by
  classical
  calc
    _ = ∑ S : Fin n → Ω, ∏ i, (w (S i) * Real.exp (t*(X (S i)-m))) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.prod_mul_distrib,← Real.exp_sum]
      congr 2
      simp only [mul_sub,Finset.mul_sum,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,nsmul_eq_mul]
      ring
    _ = ∏ _i : Fin n, ∑ x, w x * Real.exp (t*(X x-m)) := (Fintype.prod_sum (fun (_i : Fin n) (x : Ω) => w x * Real.exp (t*(X x-m)))).symm
    _ = _ := by simp

theorem product_mgf_le (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hs : ∑ x, w x = 1)
    (X : Ω → ℝ) (hX : ∀ x, X x ∈ Set.Icc (-1) 1) (n : ℕ) (t : ℝ) :
    (∑ S : Fin n → Ω, (∏ i, w (S i)) * Real.exp (t * ((∑ i, X (S i)) - n*(∑ y,w y*X y)))) ≤
      Real.exp (n*t^2/2) := by
  rw [product_mgf]
  calc
    _ ≤ (Real.exp (t^2/2))^n := pow_le_pow_left₀
      (Finset.sum_nonneg (fun x _ => mul_nonneg (hw x) (Real.exp_nonneg _)))
      (one_mgf w hw hs X hX t) n
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem one_tail (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hs : ∑ x, w x = 1)
    (X : Ω → ℝ) (hX : ∀ x, X x ∈ Set.Icc (-1) 1) (n : ℕ) (hn : 0 < n)
    (a : ℝ) (ha : 0 ≤ a) :
    (∑ S : Fin n → Ω, (∏ i, w (S i)) *
      (if a ≤ (∑ i,X (S i))-n*(∑ y,w y*X y) then (1:ℝ) else 0)) ≤
      Real.exp (-a^2/(2*n)) := by
  classical
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  let t := a/n
  have ht : 0 ≤ t := div_nonneg ha hnR.le
  have hmk : (∑ S : Fin n → Ω, (∏ i,w (S i)) *
      (if a ≤ (∑ i,X (S i))-n*(∑ y,w y*X y) then (1:ℝ) else 0)) * Real.exp (t*a) ≤
      Real.exp (n*t^2/2) := by
    rw [Finset.sum_mul]
    apply le_trans _ (product_mgf_le w hw hs X hX n t)
    apply Finset.sum_le_sum
    intro S _
    have hp : 0 ≤ ∏ i,w (S i) := Finset.prod_nonneg (fun i _ => hw _)
    split_ifs with he
    · simpa using mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left he ht)) hp
    · simp [mul_nonneg hp (Real.exp_nonneg _)]
  have hb := (le_div_iff₀ (Real.exp_pos (t*a))).mpr hmk
  calc
    _ ≤ Real.exp (n*t^2/2) / Real.exp (t*a) := hb
    _ = Real.exp (-a^2/(2*n)) := by
      rw [← Real.exp_sub]
      congr 1
      dsimp [t]
      field_simp
      <;> ring

theorem product_mass (w : Ω → ℝ) (hs : ∑ x,w x = 1) (n : ℕ) :
    (∑ S : Fin n → Ω, ∏ i,w (S i)) = 1 := by
  rw [← Fintype.prod_sum]
  simp [hs]


theorem two_tail (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hs : ∑ x, w x = 1)
    (X : Ω → ℝ) (hX : ∀ x, X x ∈ Set.Icc (-1) 1) (n : ℕ) (hn : 0 < n)
    (a : ℝ) (ha : 0 ≤ a) :
    (∑ S : Fin n → Ω, (∏ i,w (S i)) *
      (if a ≤ |(∑ i,X (S i))-n*(∑ y,w y*X y)| then (1:ℝ) else 0)) ≤
      2 * Real.exp (-a^2/(2*n)) := by
  classical
  have hp := one_tail w hw hs X hX n hn a ha
  have hm := one_tail w hw hs (fun x => -X x)
    (fun x => by have hh := hX x; constructor <;> linarith [hh.1,hh.2]) n hn a ha
  have hminus : (∑ S : Fin n → Ω, (∏ i,w (S i)) *
      (if a ≤ -((∑ i,X (S i))-n*(∑ y,w y*X y)) then (1:ℝ) else 0)) ≤
      Real.exp (-a^2/(2*n)) := by
    simpa [Finset.sum_neg_distrib,mul_neg,sub_eq_add_neg,add_comm] using hm
  have hu : (∑ S : Fin n → Ω, (∏ i,w (S i)) *
      (if a ≤ |(∑ i,X (S i))-n*(∑ y,w y*X y)| then (1:ℝ) else 0)) ≤
      (∑ S : Fin n → Ω, (∏ i,w (S i)) *
        (if a ≤ (∑ i,X (S i))-n*(∑ y,w y*X y) then (1:ℝ) else 0)) +
      (∑ S : Fin n → Ω, (∏ i,w (S i)) *
        (if a ≤ -((∑ i,X (S i))-n*(∑ y,w y*X y)) then (1:ℝ) else 0)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro S _
    have hwS : 0 ≤ ∏ i,w (S i) := Finset.prod_nonneg (fun i _ => hw _)
    by_cases hpos : a ≤ (∑ i,X (S i))-n*(∑ y,w y*X y) <;>
      by_cases hneg : a ≤ -((∑ i,X (S i))-n*(∑ y,w y*X y)) <;>
      simp [le_abs,hpos,hneg,hwS] <;> split_ifs <;> linarith
  linarith

theorem good_probability (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hs : ∑ x, w x = 1)
    (X : Ω → ℝ) (hX : ∀ x, X x ∈ Set.Icc (-1) 1) (n : ℕ) (hn : 0 < n)
    (a : ℝ) (ha : 0 ≤ a) :
    1-2*Real.exp (-a^2/(2*n)) ≤
      ∑ S : Fin n → Ω, (∏ i,w (S i)) *
        (if |(∑ i,X (S i))-n*(∑ y,w y*X y)| ≤ a then (1:ℝ) else 0) := by
  classical
  have hb := two_tail w hw hs X hX n hn a ha
  have hu : 1 ≤
      (∑ S : Fin n → Ω, (∏ i,w (S i)) *
        (if |(∑ i,X (S i))-n*(∑ y,w y*X y)| ≤ a then (1:ℝ) else 0)) +
      (∑ S : Fin n → Ω, (∏ i,w (S i)) *
        (if a ≤ |(∑ i,X (S i))-n*(∑ y,w y*X y)| then (1:ℝ) else 0)) := by
    rw [← Finset.sum_add_distrib]
    conv_lhs => rw [← product_mass w hs n]
    apply Finset.sum_le_sum
    intro S _
    have hwS : 0 ≤ ∏ i,w (S i) := Finset.prod_nonneg (fun i _ => hw _)
    by_cases hg : |(∑ i,X (S i))-n*(∑ y,w y*X y)| ≤ a
    · simp only [if_pos hg,mul_one]
      apply le_add_of_nonneg_right
      apply mul_nonneg hwS
      split_ifs <;> norm_num
    · have hg' := le_of_lt (lt_of_not_ge hg)
      simp [hg,hg']
  linarith

#print axioms good_probability
end FiniteHoeffding

namespace RobustGeneralization.BernLower.LogBound
open Finset

theorem log_odds (n : ℕ) (τ : ℝ) (hτ : 0 < τ) (hτ' : τ < 1/2)
    (S : Fin n → Bool × Bool) :
    Real.log (odds1 τ S) = Real.log ((1/2+τ)/(1/2-τ)) * ∑ i,lab (S i).2 * lab (S i).1 := by
  have hp : 0 < (1/2+τ)/(1/2-τ) := div_pos (by linarith) (by linarith)
  rw [odds_eq_product n τ hτ hτ' S,Real.log_prod]
  · simp_rw [Real.log_rpow hp]
    rw [← Finset.sum_mul]
    ring
  · intro i _
    exact ne_of_gt (Real.rpow_pos_of_pos hp _)

theorem coefficient_nonneg (τ : ℝ) (hτ : 0 ≤ τ) (hτ' : τ < 1/2) :
    0 ≤ Real.log ((1/2+τ)/(1/2-τ)) := by
  apply Real.log_nonneg
  apply (le_div_iff₀ (by linarith : 0 < 1/2-τ)).mpr
  linarith

theorem coefficient_le (τ : ℝ) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/4) :
    Real.log ((1/2+τ)/(1/2-τ)) ≤ (16/3)*τ := by
  let g : ℝ → ℝ := fun x => (16/3)*x - (Real.log (1+2*x)-Real.log (1-2*x))
  let d : ℝ → ℝ := fun x => (16/3) - (2/(1+2*x) - (-2)/(1-2*x))
  have hd : ∀ x ∈ Set.Icc (0:ℝ) (1/4), HasDerivAt g (d x) x := by
    intro x hx
    have hp : 1+2*x ≠ 0 := ne_of_gt (by linarith [hx.1])
    have hm : 1-2*x ≠ 0 := ne_of_gt (by linarith [hx.2])
    have hplus := ((hasDerivAt_const x (1:ℝ)).add ((hasDerivAt_id x).const_mul 2)).log hp
    have hminus := ((hasDerivAt_const x (1:ℝ)).sub ((hasDerivAt_id x).const_mul 2)).log hm
    convert ((hasDerivAt_id x).const_mul (16/3)).fun_sub (hplus.fun_sub hminus) using 1 <;> first | rfl | norm_num [g,d]
  have hd0 : ∀ x ∈ Set.Icc (0:ℝ) (1/4), 0 ≤ d x := by
    intro x hx
    have hp : 0 < 1+2*x := by linarith [hx.1]
    have hm : 0 < 1-2*x := by linarith [hx.2]
    have hs : x^2 ≤ (1/16:ℝ) := by nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (show 0 ≤ 1/4+x by linarith [hx.1])]
    have hden : 0 < 1-4*x^2 := by nlinarith
    have he : 2/(1+2*x)-(-2)/(1-2*x) = 4/(1-4*x^2) := by
      apply (eq_div_iff (ne_of_gt hden)).mpr
      field_simp [ne_of_gt hp,ne_of_gt hm] <;> ring
    dsimp [d]
    rw [he,sub_nonneg,div_le_iff₀ hden]
    nlinarith
  have hmono : MonotoneOn g (Set.Icc (0:ℝ) (1/4)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => hd0 x (interior_subset hx))
  have hb := hmono (show (0:ℝ) ∈ Set.Icc (0:ℝ) (1/4) by constructor <;> norm_num)
    ⟨hτ,hτ'⟩ hτ
  have hr : (1/2+τ)/(1/2-τ) = (1+2*τ)/(1-2*τ) := by field_simp <;> ring
  rw [hr,Real.log_div (by linarith : 1+2*τ ≠ 0) (by linarith : 1-2*τ ≠ 0)]
  simpa [g] using hb

#print axioms coefficient_le
end RobustGeneralization.BernLower.LogBound

namespace RobustGeneralization.BernLower.Moments
open Finset

theorem weight_nonneg (θ : Bool) (τ : ℝ) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/2)
    (p : Bool × Bool) : 0 ≤ bern1W θ τ p := by
  unfold bern1W
  split_ifs <;> positivity

theorem weight_sum (θ : Bool) (τ : ℝ) : ∑ p : Bool × Bool, bern1W θ τ p = 1 := by
  cases θ <;> simp [Fintype.sum_prod_type, Fintype.sum_bool, bern1W] <;> ring

theorem signed_range (p : Bool × Bool) : lab p.2 * lab p.1 ∈ Set.Icc (-1:ℝ) 1 := by
  rcases p with ⟨a,b⟩
  cases a <;> cases b <;> norm_num [lab]

theorem signed_mean (θ : Bool) (τ : ℝ) :
    ∑ p : Bool × Bool, bern1W θ τ p * (lab p.2 * lab p.1) = 2*τ*lab θ := by
  cases θ <;> simp [Fintype.sum_prod_type,Fintype.sum_bool,bern1W,lab] <;> ring

theorem centered_probability (θ : Bool) (τ : ℝ) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/2)
    (n : ℕ) (hn : 0 < n) (a : ℝ) (ha : 0 ≤ a) :
    1 - 2*Real.exp (-a^2/(2*n)) ≤
    ∑ S : Fin n → Bool × Bool, (∏ i,bern1W θ τ (S i)) *
      (if |(∑ i,lab (S i).2 * lab (S i).1) - n*(2*τ*lab θ)| ≤ a then (1:ℝ) else 0) := by
  classical
  simpa only [signed_mean] using FiniteHoeffding.good_probability
    (bern1W θ τ) (weight_nonneg θ τ hτ hτ') (weight_sum θ τ)
    (fun p => lab p.2 * lab p.1) signed_range n hn a ha

theorem radius_error (n : ℕ) (hn : 0 < n) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    2*Real.exp (-(Real.sqrt (2*n*Real.log (2/δ)))^2/(2*n)) = δ := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log (2/δ) := Real.log_nonneg (by
    apply (le_div_iff₀ hδ).mpr
    linarith)
  rw [Real.sq_sqrt (by positivity)]
  have he : -(2*(n:ℝ)*Real.log (2/δ))/(2*n) = -Real.log (2/δ) := by
    field_simp
  rw [he,Real.exp_neg,Real.exp_log (div_pos (by norm_num) hδ)]
  field_simp

theorem centered_confidence (θ : Bool) (τ : ℝ) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/2)
    (n : ℕ) (hn : 0 < n) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    1-δ ≤ ∑ S : Fin n → Bool × Bool, (∏ i,bern1W θ τ (S i)) *
      (if |(∑ i,lab (S i).2 * lab (S i).1) - n*(2*τ*lab θ)| ≤
        Real.sqrt (2*n*Real.log (2/δ)) then (1:ℝ) else 0) := by
  classical
  have hh := centered_probability θ τ hτ hτ' n hn
    (Real.sqrt (2*n*Real.log (2/δ))) (Real.sqrt_nonneg _)
  rwa [radius_error n hn δ hδ hδ'] at hh
end RobustGeneralization.BernLower.Moments

namespace RobustGeneralization.BernLower.Constants
open Finset

theorem radius_lower (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    (9/8)*Real.sqrt n ≤ Real.sqrt (2*n*Real.log (2/δ)) := by
  have hl : (2/3:ℝ) ≤ Real.log (2/δ) := by
    have h := Real.log_le_log (by norm_num : (0:ℝ)<2)
      (show (2:ℝ) ≤ 2/δ by apply (le_div_iff₀ hδ).mpr; linarith)
    linarith [Real.log_two_gt_d9]
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ n by positivity)
  have ha := Real.sq_sqrt (show 0 ≤ 2*(n:ℝ)*Real.log (2/δ) by positivity)
  have hm := mul_le_mul_of_nonneg_left hl (show (0:ℝ) ≤ 2*n by positivity)
  nlinarith [Real.sqrt_nonneg (n:ℝ), Real.sqrt_nonneg (2*n*Real.log (2/δ))]

theorem drift_bound (n : ℕ) (τ : ℝ) (hτ : 0 < τ) (hn : (n:ℝ) ≤ 1/τ^2) :
    τ*n ≤ Real.sqrt n := by
  have hn0 : (0:ℝ) ≤ n := by positivity
  have hb : (n:ℝ)*τ^2 ≤ 1 := (le_div_iff₀ (sq_pos_of_pos hτ)).mp hn
  have hc := mul_le_mul_of_nonneg_right hb hn0
  have hs := Real.sq_sqrt hn0
  nlinarith [Real.sqrt_nonneg (n:ℝ)]

theorem log_control (n : ℕ) (τ δ : ℝ) (hτ : 0 < τ) (hτ' : τ ≤ 1/4)
    (hn : (n:ℝ) ≤ 1/τ^2) (hδ : 0 < δ) (hδ' : δ ≤ 1)
    (θ : Bool) (S : Fin n → Bool × Bool)
    (hc : |(∑ i,lab (S i).2*lab (S i).1)-n*(2*τ*lab θ)| ≤
      Real.sqrt (2*n*Real.log (2/δ))) :
    |Real.log (odds1 τ S)| ≤ 15*τ*Real.sqrt (2*n*Real.log (2/δ)) := by
  let a := Real.sqrt (2*n*Real.log (2/δ))
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hrad : (9/8)*Real.sqrt n ≤ a := radius_lower n δ hδ hδ'
  have hd := drift_bound n τ hτ hn
  have hm : |(n:ℝ)*(2*τ*lab θ)| = 2*τ*n := by
    cases θ <;> simp [lab,abs_mul,abs_of_nonneg hτ.le] <;> ring
  have hb : |∑ i,lab (S i).2*lab (S i).1| ≤ (25/9)*a := by
    have hh := abs_add_le ((∑ i,lab (S i).2*lab (S i).1)-n*(2*τ*lab θ)) (n*(2*τ*lab θ))
    rw [sub_add_cancel,hm] at hh
    change _ ≤ a at hc
    nlinarith
  rw [LogBound.log_odds n τ hτ (by linarith) S,abs_mul,
    abs_of_nonneg (LogBound.coefficient_nonneg τ hτ.le (by linarith))]
  have hh := mul_le_mul (LogBound.coefficient_le τ hτ.le hτ') hb
    (abs_nonneg _) (by positivity : (0:ℝ) ≤ (16/3)*τ)
  have hta : 0 ≤ τ*a := mul_nonneg hτ.le ha
  dsimp [a] at *
  nlinarith
end RobustGeneralization.BernLower.Constants

open RobustGeneralization.BernLower Finset

theorem accepted_lemma29_log_odds_bound (n : ℕ) (τ δ : ℝ) (hτ : 0 < τ) (hτ' : τ ≤ 1 / 4)
    (hn : (n : ℝ) ≤ 1 / τ ^ 2) (hδ : 0 < δ) :
    1 - δ ≤ ∑ θ : Bool, (1 / 2) * ∑ S : Fin n → Bool × Bool,
      (∏ k, bern1W θ τ (S k)) *
        (if |Real.log (odds1 τ S)| ≤ 15 * τ * Real.sqrt (2 * n * Real.log (2 / δ))
          then 1 else 0) := by
  classical
  have hw : ∀ θ (S : Fin n → Bool × Bool), 0 ≤ ∏ k,bern1W θ τ (S k) := by
    intro θ S
    exact Finset.prod_nonneg (fun i _ => Moments.weight_nonneg θ τ hτ.le (by linarith) _)
  by_cases hd : 1 ≤ δ
  · apply le_trans (show 1-δ ≤ 0 by linarith)
    apply Finset.sum_nonneg
    intro θ _
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro S _
    apply mul_nonneg (hw θ S)
    split_ifs <;> norm_num
  have hd' : δ ≤ 1 := le_of_lt (lt_of_not_ge hd)
  by_cases hn0 : n = 0
  · subst n
    simp [odds1,post1,joint1,Fintype.sum_bool]
    linarith
  have hn' : 0 < n := Nat.pos_of_ne_zero hn0
  have hp : ∀ θ : Bool, 1-δ ≤ ∑ S : Fin n → Bool × Bool,
      (∏ k, bern1W θ τ (S k)) *
        (if |Real.log (odds1 τ S)| ≤ 15 * τ * Real.sqrt (2 * n * Real.log (2 / δ))
          then 1 else 0) := by
    intro θ
    apply le_trans (Moments.centered_confidence θ τ hτ.le (by linarith) n hn' δ hδ hd')
    apply Finset.sum_le_sum
    intro S _
    apply mul_le_mul_of_nonneg_left _ (hw θ S)
    split_ifs with hc hg hg
    · rfl
    · exact False.elim (hg (Constants.log_control n τ δ hτ hτ' hn hδ hd' θ S hc))
    · norm_num
    · rfl
  calc
    1-δ = ∑ θ : Bool, (1/2:ℝ)*(1-δ) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun θ _ => mul_le_mul_of_nonneg_left (hp θ) (by norm_num))

namespace RobustGeneralization.BernLower.Posterior
open Finset

theorem sum_product_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Bool → ℝ) (i : ι) (g : Bool → ℝ) :
    (∑ θ : ι → Bool, (∏ j, f j (θ j)) * g (θ i)) =
      (∑ b : Bool, f i b * g b) * ∏ j ∈ univ.erase i, ∑ b : Bool, f j b := by
  classical
  calc
    _ = ∑ θ : ι → Bool, ∏ j, f j (θ j) * (if j = i then g (θ j) else 1) := by
      apply sum_congr rfl
      intro θ _
      rw [prod_mul_distrib]
      simp
    _ = ∏ j, ∑ b : Bool, f j b * (if j = i then g b else 1) :=
      (Fintype.prod_sum (fun (j : ι) (b : Bool) => f j b * (if j = i then g b else 1))).symm
    _ = _ := by
      rw [← mul_prod_erase univ (fun j => ∑ b : Bool, f j b * (if j = i then g b else 1)) (mem_univ i)]
      simp only [ite_true]
      congr 1
      apply prod_congr rfl
      intro j hj
      simp [(mem_erase.mp hj).1]

theorem positive_product_marginal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Bool → ℝ) (hf : ∀ i b, 0 < f i b) (i : ι) (b : Bool) :
    (∑ θ : ι → Bool, if θ i = b then ∏ j, f j (θ j) else 0) /
      (∑ θ : ι → Bool, ∏ j, f j (θ j)) = f i b / (f i false + f i true) := by
  classical
  have hnum : (∑ θ : ι → Bool, if θ i = b then ∏ j, f j (θ j) else 0) =
      f i b * ∏ j ∈ univ.erase i, ∑ b : Bool, f j b := by
    cases b with
    | false => simpa using sum_product_coordinate f i (fun a => if a = false then 1 else 0)
    | true => simpa using sum_product_coordinate f i (fun a => if a = true then 1 else 0)
  rw [hnum, ← Fintype.prod_sum]
  rw [← mul_prod_erase univ (fun j => ∑ b : Bool, f j b) (mem_univ i)]
  have hp : (∏ j ∈ univ.erase i, ∑ b : Bool, f j b) ≠ 0 := ne_of_gt <|
    prod_pos (fun j _ => by simpa only [Fintype.sum_bool] using add_pos (hf j true) (hf j false))
  rw [mul_div_mul_right _ _ hp]
  simp only [Fintype.sum_bool, add_comm]

noncomputable def coordW {d n : ℕ} (τ : ℝ) (S : Fin n → (Fin d → Bool) × Bool)
    (i : Fin d) (b : Bool) : ℝ :=
  ∏ k, if (S k).1 i = ((S k).2 == b) then 1/2+τ else 1/2-τ

theorem coordW_pos {d n : ℕ} (τ : ℝ) (hτ : 0 < τ) (hτ' : τ < 1/2)
    (S : Fin n → (Fin d → Bool) × Bool) (i : Fin d) (b : Bool) :
    0 < coordW τ S i b := by
  unfold coordW
  apply prod_pos
  intro k _
  split_ifs <;> linarith

theorem joint_factor {d n : ℕ} (τ : ℝ) (θ : Fin d → Bool)
    (S : Fin n → (Fin d → Bool) × Bool) :
    joint τ θ S = ((1/2:ℝ)^d * (1/2:ℝ)^n) * ∏ i, coordW τ S i (θ i) := by
  simp only [joint, bernW, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, coordW]
  rw [prod_comm]
  ring

theorem postProb_factor {d n : ℕ} (τ : ℝ) (hτ : 0 < τ) (hτ' : τ < 1/2)
    (S : Fin n → (Fin d → Bool) × Bool) (i : Fin d) (b : Bool) :
    postProb τ S i b = coordW τ S i b / (coordW τ S i false + coordW τ S i true) := by
  classical
  unfold postProb
  simp only [joint_factor]
  have hn : (∑ θ : Fin d → Bool,
      if θ i = b then ((1/2:ℝ)^d*(1/2:ℝ)^n) * ∏ j, coordW τ S j (θ j) else 0) =
      ((1/2:ℝ)^d*(1/2:ℝ)^n) *
        ∑ θ : Fin d → Bool, if θ i = b then ∏ j, coordW τ S j (θ j) else 0 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro θ _
    split_ifs <;> simp
  rw [hn, ← mul_sum]
  rw [mul_div_mul_left _ _ (by positivity : ((1/2:ℝ)^d*(1/2:ℝ)^n) ≠ 0)]
  exact positive_product_marginal (coordW τ S) (coordW_pos τ hτ hτ' S) i b

end RobustGeneralization.BernLower.Posterior

namespace RobustGeneralization.BernLower.Posterior
open Finset

theorem normalized_difference_le_log_of_le (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hqp : q ≤ p) : |(p-q)/(p+q)| ≤ |Real.log (p/q)| := by
  calc
    _ = (p-q)/(p+q) := abs_of_nonneg (div_nonneg (sub_nonneg.mpr hqp) (by positivity))
    _ ≤ (p-q)/p := div_le_div_of_nonneg_left (sub_nonneg.mpr hqp) hp (by linarith)
    _ = 1 - (p/q)⁻¹ := by rw [inv_div]; field_simp
    _ ≤ Real.log (p/q) := Real.one_sub_inv_le_log_of_pos (div_pos hp hq)
    _ ≤ |Real.log (p/q)| := le_abs_self _

theorem normalized_difference_le_log (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    |(p-q)/(p+q)| ≤ |Real.log (p/q)| := by
  by_cases hqp : q ≤ p
  · exact normalized_difference_le_log_of_le p q hp hq hqp
  · have h := normalized_difference_le_log_of_le q p hq hp (le_of_lt (lt_of_not_ge hqp))
    have hd : (q-p)/(q+p) = -((p-q)/(p+q)) := by ring
    have hl : Real.log (q/p) = -Real.log (p/q) := by
      rw [Real.log_div hq.ne' hp.ne', Real.log_div hp.ne' hq.ne']
      ring
    rwa [hd, hl, abs_neg, abs_neg] at h

theorem joint1_coordinate_factor {d n : ℕ} (τ : ℝ)
    (S : Fin n → (Fin d → Bool) × Bool) (i : Fin d) (b : Bool) :
    joint1 τ b (fun k => ((S k).1 i, (S k).2)) =
      ((1/2:ℝ)*(1/2:ℝ)^n) * coordW τ S i b := by
  simp only [joint1, bern1W, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, coordW]
  ring

theorem postProb_eq_post1 {d n : ℕ} (τ : ℝ) (hτ : 0 < τ) (hτ' : τ < 1/2)
    (S : Fin n → (Fin d → Bool) × Bool) (i : Fin d) (b : Bool) :
    postProb τ S i b = post1 τ (fun k => ((S k).1 i, (S k).2)) b := by
  rw [postProb_factor τ hτ hτ']
  unfold post1
  simp only [joint1_coordinate_factor, ← mul_sum]
  rw [mul_div_mul_left _ _ (by positivity : ((1/2:ℝ)*(1/2:ℝ)^n) ≠ 0)]
  simp only [Fintype.sum_bool, add_comm]

theorem postMean_log_bound {d n : ℕ} (τ : ℝ) (hτ : 0 < τ) (hτ' : τ < 1/2)
    (S : Fin n → (Fin d → Bool) × Bool) (i : Fin d) :
    |postMean τ S i| ≤ |Real.log (odds1 τ (fun k => ((S k).1 i, (S k).2)))| := by
  have hp := coordW_pos τ hτ hτ' S i true
  have hq := coordW_pos τ hτ hτ' S i false
  have hs : coordW τ S i false + coordW τ S i true ≠ 0 := by positivity
  have ho : odds1 τ (fun k => ((S k).1 i, (S k).2)) =
      coordW τ S i true / coordW τ S i false := by
    unfold odds1
    rw [← postProb_eq_post1 τ hτ hτ' S i true, ← postProb_eq_post1 τ hτ hτ' S i false]
    rw [postProb_factor τ hτ hτ',postProb_factor τ hτ hτ']
    field_simp
  rw [ho]
  unfold postMean
  rw [postProb_factor τ hτ hτ',postProb_factor τ hτ hτ', ← sub_div, add_comm (coordW τ S i false)]
  exact normalized_difference_le_log _ _ hp hq

end RobustGeneralization.BernLower.Posterior

namespace RobustGeneralization.BernLower.Posterior
open Finset

theorem product_project {Ω Δ ι : Type*} [Fintype Ω] [Fintype Δ] [DecidableEq Δ]
    [Fintype ι] [DecidableEq ι] (w : Ω → ℝ) (π : Ω → Δ) (F : (ι → Δ) → ℝ) :
    (∑ S : ι → Ω, (∏ k, w (S k)) * F (fun k => π (S k))) =
      ∑ T : ι → Δ, (∏ k, ∑ x : Ω, if π x = T k then w x else 0) * F T := by
  classical
  have hi (S : ι → Ω) (T : ι → Δ) :
      (∏ k, if π (S k) = T k then w (S k) else 0) =
        if (fun k => π (S k)) = T then ∏ k, w (S k) else 0 := by
    by_cases h : (fun k => π (S k)) = T
    · subst T; simp
    · rw [if_neg h]
      obtain ⟨k,hk⟩ : ∃ k, π (S k) ≠ T k := by
        by_contra hn
        exact h (funext (fun k => by by_contra hk; exact hn ⟨k,hk⟩))
      exact prod_eq_zero (mem_univ k) (if_neg hk)
  symm
  calc
    _ = ∑ T : ι → Δ, ∑ S : ι → Ω,
        (∏ k, if π (S k) = T k then w (S k) else 0) * F T := by
      apply sum_congr rfl
      intro T _
      rw [Fintype.prod_sum, sum_mul]
    _ = ∑ S : ι → Ω, ∑ T : ι → Δ,
        (∏ k, if π (S k) = T k then w (S k) else 0) * F T := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro S _
      simp only [hi, ite_mul, zero_mul]
      simp

theorem bernW_project {d : ℕ} (θ : Fin d → Bool) (τ : ℝ) (i : Fin d)
    (p : Bool × Bool) :
    (∑ x : (Fin d → Bool) × Bool,
      if (x.1 i, x.2) = p then bernW θ τ x else 0) = bern1W (θ i) τ p := by
  classical
  rcases p with ⟨b,y⟩
  rw [Fintype.sum_prod_type, sum_comm]
  have he (s : Fin d → Bool) (z : Bool) :
      (if (s i,z) = (b,y) then bernW θ τ (s,z) else 0) =
      if z = y then (1/2:ℝ) *
        (if s i = b then ∏ j, if s j = (z == θ j) then 1/2+τ else 1/2-τ else 0) else 0 := by
    by_cases hz : z = y <;> by_cases hs : s i = b <;> simp [hz,hs,bernW]
  simp_rw [he, sum_ite_irrel, ← mul_sum]
  simp only [sum_const_zero, sum_ite_eq', mem_univ, ite_true]
  have hm := sum_product_coordinate
    (fun (j : Fin d) (a : Bool) => if a = (y == θ j) then (1/2:ℝ)+τ else 1/2-τ)
    i (fun a => if a=b then 1 else 0)
  have hs (j : Fin d) : (∑ a : Bool, if a = (y == θ j) then (1/2:ℝ)+τ else 1/2-τ) = 1 := by
    cases y <;> cases h : θ j <;> simp [Fintype.sum_bool,h] <;> ring
  simp only [mul_ite, mul_one, mul_zero] at hm
  simp only [sum_ite_eq', mem_univ, ite_true, hs, prod_const_one, mul_one] at hm
  rw [hm]
  rfl

theorem bernW_sum {d : ℕ} (θ : Fin d → Bool) (τ : ℝ) :
    (∑ p : (Fin d → Bool) × Bool, bernW θ τ p) = 1 := by
  classical
  rw [Fintype.sum_prod_type, sum_comm]
  unfold bernW
  simp only [← mul_sum]
  have hs (y : Bool) (i : Fin d) :
      (∑ b : Bool, if b = (y == θ i) then (1/2:ℝ)+τ else 1/2-τ) = 1 := by
    cases y <;> cases h : θ i <;> simp [Fintype.sum_bool,h] <;> ring
  have he (y : Bool) : (∑ s : Fin d → Bool,
      ∏ i, if s i = (y == θ i) then (1/2:ℝ)+τ else 1/2-τ) = 1 := by
    rw [← Fintype.prod_sum (fun (i : Fin d) (b : Bool) =>
      if b = (y == θ i) then (1/2:ℝ)+τ else 1/2-τ)]
    simp only [hs, prod_const_one]
  simp only [he]
  norm_num

theorem joint_mass {d n : ℕ} (τ : ℝ) :
    (∑ θ : Fin d → Bool, ∑ S : Fin n → (Fin d → Bool) × Bool, joint τ θ S) = 1 := by
  classical
  unfold joint
  simp only [← mul_sum, ← Fintype.prod_sum, bernW_sum, prod_const_one, mul_one]
  simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rw [← mul_pow]
  norm_num

theorem joint_nonneg {d n : ℕ} (τ : ℝ) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/2)
    (θ : Fin d → Bool) (S : Fin n → (Fin d → Bool) × Bool) : 0 ≤ joint τ θ S := by
  unfold joint bernW
  apply mul_nonneg (by positivity)
  apply prod_nonneg
  intro k _
  apply mul_nonneg (by norm_num)
  apply prod_nonneg
  intro i _
  split_ifs <;> linarith

theorem joint_project {d n : ℕ} (τ : ℝ) (i : Fin d)
    (F : (Fin n → Bool × Bool) → ℝ) :
    (∑ θ : Fin d → Bool, ∑ S : Fin n → (Fin d → Bool) × Bool,
      joint τ θ S * F (fun k => ((S k).1 i,(S k).2))) =
      ∑ b : Bool, (1/2:ℝ) * ∑ T : Fin n → Bool × Bool,
        (∏ k, bern1W b τ (T k)) * F T := by
  classical
  have he (θ : Fin d → Bool) :
      (∑ S : Fin n → (Fin d → Bool) × Bool,
        (∏ k, bernW θ τ (S k)) * F (fun k => ((S k).1 i,(S k).2))) =
      ∑ T : Fin n → Bool × Bool, (∏ k,bern1W (θ i) τ (T k)) * F T := by
    simpa only [bernW_project] using product_project (bernW θ τ)
      (fun p => (p.1 i,p.2)) F
  unfold joint
  simp only [mul_assoc, ← mul_sum, he]
  have hm := sum_product_coordinate (fun (_j : Fin d) (_b : Bool) => (1/2:ℝ)) i
    (fun b => ∑ T : Fin n → Bool × Bool, (∏ k,bern1W b τ (T k)) * F T)
  simpa [← mul_sum] using hm

end RobustGeneralization.BernLower.Posterior

namespace RobustGeneralization.BernLower.Posterior
open Finset

theorem weighted_complement {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (hw : ∑ x, w x = 1) (P : Ω → Prop) [DecidablePred P] :
    (∑ x, w x * (if ¬P x then (1:ℝ) else 0)) =
      1 - ∑ x, w x * (if P x then (1:ℝ) else 0) := by
  classical
  rw [← hw, ← sum_sub_distrib]
  apply sum_congr rfl
  intro x _
  by_cases h : P x <;> simp [h,hw]

theorem weighted_union {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hs : ∑ x, w x = 1)
    (P : ι → Ω → Prop) [∀ i, DecidablePred (P i)] (δ : ℝ)
    (hp : ∀ i, 1-δ ≤ ∑ x, w x * (if P i x then (1:ℝ) else 0)) :
    1 - (Fintype.card ι:ℝ)*δ ≤
      ∑ x, w x * (if ∀ i, P i x then (1:ℝ) else 0) := by
  classical
  have hpoint (x : Ω) : (if ¬∀ i, P i x then (1:ℝ) else 0) ≤
      ∑ i, if ¬P i x then (1:ℝ) else 0 := by
    by_cases h : ∀ i, P i x
    · simp [h]
    · rw [if_pos h]
      obtain ⟨i,hi⟩ := not_forall.mp h
      exact le_trans (by simp [hi])
        (single_le_sum (f := fun j => if ¬P j x then (1:ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) (mem_univ i))
  have hfail : (∑ x, w x * (if ¬∀ i, P i x then (1:ℝ) else 0)) ≤
      (Fintype.card ι:ℝ)*δ := by
    calc
      _ ≤ ∑ x, w x * ∑ i, if ¬P i x then (1:ℝ) else 0 :=
        sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hpoint x) (hw x))
      _ = ∑ i, ∑ x, w x * (if ¬P i x then (1:ℝ) else 0) := by
        simp only [mul_sum]
        rw [sum_comm]
      _ ≤ ∑ _i : ι, δ := by
        apply sum_le_sum
        intro i _
        rw [weighted_complement w hs (P i)]
        linarith [hp i]
      _ = _ := by simp
  rw [weighted_complement w hs (fun x => ∀ i, P i x)] at hfail
  linarith

end RobustGeneralization.BernLower.Posterior

open RobustGeneralization.BernLower RobustGeneralization.BernLower.Posterior Finset

theorem solution (d n : ℕ) (τ γ : ℝ) (hτ : 0 < τ) (hτ' : τ ≤ 1 / 4)
    (hn : (n : ℝ) ≤ 1 / τ ^ 2) (hγ : 0 < γ)
    (hx : 15 * τ * Real.sqrt (2 * n * Real.log (4 * d / γ)) ≤ 1) :
    1 - γ / 2 ≤ ∑ θ : Fin d → Bool, ∑ S : Fin n → (Fin d → Bool) × Bool,
      joint τ θ S *
        (if ∀ i, |postMean τ S i| ≤ 15 * τ * Real.sqrt (2 * n * Real.log (4 * d / γ))
          then 1 else 0) := by
  classical
  by_cases hd : d = 0
  · subst d
    have he : (∑ θ : Fin 0 → Bool, ∑ S : Fin n → (Fin 0 → Bool) × Bool,
        joint τ θ S *
          (if ∀ i, |postMean τ S i| ≤ 15 * τ * Real.sqrt (2 * n * Real.log (4 * 0 / γ))
            then 1 else 0)) = 1 := by
      simpa using (joint_mass (d := 0) (n := n) τ)
    simp only [Nat.cast_zero]
    rw [he]
    linarith
  have hdR : (0:ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  let δ := γ / (2*d)
  let R := 15 * τ * Real.sqrt (2*n*Real.log (4*d/γ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hquot : 2/δ = 4*d/γ := by dsimp [δ]; field_simp; ring
  have hi (i : Fin d) : 1-δ ≤
      ∑ θ : Fin d → Bool, ∑ S : Fin n → (Fin d → Bool) × Bool,
        joint τ θ S *
          (if |Real.log (odds1 τ (fun k => ((S k).1 i,(S k).2)))| ≤ R then (1:ℝ) else 0) := by
    rw [joint_project τ i (fun T => if |Real.log (odds1 τ T)| ≤ R then (1:ℝ) else 0)]
    simpa only [hquot] using accepted_lemma29_log_odds_bound n τ δ hτ hτ' hn hδ
  let w : (Fin d → Bool) × (Fin n → (Fin d → Bool) × Bool) → ℝ :=
    fun z => joint τ z.1 z.2
  let P (i : Fin d) (z : (Fin d → Bool) × (Fin n → (Fin d → Bool) × Bool)) : Prop :=
    |Real.log (odds1 τ (fun k => ((z.2 k).1 i,(z.2 k).2)))| ≤ R
  have hu := weighted_union w (fun z => joint_nonneg τ hτ.le (by linarith) z.1 z.2)
    (by simpa only [w,Fintype.sum_prod_type] using joint_mass (d := d) (n := n) τ)
    P δ (fun i => by simpa only [w,P,Fintype.sum_prod_type] using hi i)
  have hc : (d:ℝ)*δ = γ/2 := by dsimp [δ]; field_simp
  simp only [Fintype.card_fin,hc,w,P,Fintype.sum_prod_type] at hu
  apply hu.trans
  apply sum_le_sum
  intro θ _
  apply sum_le_sum
  intro S _
  apply mul_le_mul_of_nonneg_left _ (joint_nonneg τ hτ.le (by linarith) θ S)
  split_ifs with hlog hmean hmean
  · rfl
  · exact False.elim (hmean (fun i =>
      (postMean_log_bound τ hτ (by linarith) S i).trans (hlog i)))
  · norm_num
  · rfl
