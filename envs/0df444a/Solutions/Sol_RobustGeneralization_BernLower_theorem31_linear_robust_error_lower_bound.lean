-- Prove2me | solution 1 for RobustGeneralization.BernLower.theorem31_linear_robust_error_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-24T09:43:06.210731+00:00
-- url     : https://prove2.me/submissions/731e7d66-9e55-4a77-bd73-b2348f254375

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

theorem accepted_posterior_mean_bound (d n : ℕ) (τ γ : ℝ) (hτ : 0 < τ) (hτ' : τ ≤ 1 / 4)
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

namespace RobustGeneralization.BernLower.Tail
open Finset

theorem symmetric_half {Ω : Type*} [Fintype Ω]
    (q : Ω → ℝ) (hq : ∀ x, 0 ≤ q x) (hs : ∑ x, q x = 1)
    (flip : Ω ≃ Ω) (hqf : ∀ x, q (flip x) = q x)
    (noise : Ω → ℝ) (hn : ∀ x, noise (flip x) = -noise x) :
    1/2 ≤ ∑ x, q x * (if noise x ≤ 0 then (1:ℝ) else 0) := by
  classical
  have heq : (∑ x, q x * (if 0 ≤ noise x then (1:ℝ) else 0)) =
      ∑ x, q x * (if noise x ≤ 0 then (1:ℝ) else 0) := by
    calc
      _ = ∑ x, q (flip x) * (if 0 ≤ noise (flip x) then (1:ℝ) else 0) :=
        (Equiv.sum_comp flip _).symm
      _ = _ := by simp only [hqf,hn,neg_nonneg]
  have hbound : 1 ≤ (∑ x, q x * (if noise x ≤ 0 then (1:ℝ) else 0)) +
      ∑ x, q x * (if 0 ≤ noise x then (1:ℝ) else 0) := by
    rw [← sum_add_distrib]
    calc
      1 = ∑ x, q x := hs.symm
      _ ≤ _ := by
        apply sum_le_sum
        intro x _
        by_cases h : noise x ≤ 0
        · simp only [if_pos h,mul_one]
          exact le_add_of_nonneg_right (mul_nonneg (hq x) (by split_ifs <;> norm_num))
        · have h' : 0 ≤ noise x := le_of_lt (lt_of_not_ge h)
          simp [h,h']
  linarith

theorem weighted_markov {Ω : Type*} [Fintype Ω]
    (p V : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1)
    (hV : ∀ x, 0 ≤ V x) (T γ : ℝ) (hT : 0 < T)
    (hmean : (∑ x, p x * V x) ≤ γ*T) :
    1-γ ≤ ∑ x, p x * (if V x ≤ T then (1:ℝ) else 0) := by
  classical
  have hpoint (x : Ω) : T*(p x*(1-(if V x ≤ T then (1:ℝ) else 0))) ≤ p x*V x := by
    by_cases h : V x ≤ T
    · simpa [h] using mul_nonneg (hp x) (hV x)
    · simp only [if_neg h,sub_zero,mul_one]
      nlinarith [mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge h)) (hp x)]
  have hsum := sum_le_sum (fun x (_ : x ∈ (univ : Finset Ω)) => hpoint x)
  have heq : (∑ x, T*(p x*(1-(if V x ≤ T then (1:ℝ) else 0)))) =
      T*(1-∑ x, p x*(if V x ≤ T then (1:ℝ) else 0)) := by
    simp only [mul_sub,mul_one,sum_sub_distrib,← mul_sum,hs]
  rw [heq] at hsum
  nlinarith

theorem mixture_tail {Α Ω : Type*} [Fintype Α] [Fintype Ω]
    (p : Α → ℝ) (q : Ω → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hp1 : ∑ a, p a = 1) (hq : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1)
    (flip : Ω ≃ Ω) (hqf : ∀ x, q (flip x) = q x)
    (shift bound : Α → ℝ) (noise : Α → Ω → ℝ)
    (hbound : ∀ a, shift a ≤ bound a) (hnonneg : ∀ a, 0 ≤ bound a)
    (hn : ∀ a x, noise a (flip x) = -noise a x)
    (T γ : ℝ) (hT : 0 < T) (hmean : (∑ a, p a*bound a) ≤ γ*T) :
    (1-γ)/2 ≤ ∑ a, p a * ∑ x, q x *
      (if shift a + noise a x ≤ T then (1:ℝ) else 0) := by
  classical
  have hmark := weighted_markov p bound hp hp1 hnonneg T γ hT hmean
  have hinner (a : Α) : (1/2:ℝ)*(if bound a ≤ T then (1:ℝ) else 0) ≤
      ∑ x, q x*(if shift a+noise a x ≤ T then (1:ℝ) else 0) := by
    by_cases ha : bound a ≤ T
    · simp only [if_pos ha,mul_one]
      apply le_trans (symmetric_half q hq hq1 flip hqf (noise a) (hn a))
      apply sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (hq x)
      by_cases hx : noise a x ≤ 0
      · have hx' : shift a+noise a x ≤ T := by linarith [hbound a]
        simp [hx,hx']
      · simp only [if_neg hx]
        split_ifs <;> norm_num
    · simp only [if_neg ha,mul_zero]
      exact sum_nonneg (fun x _ => mul_nonneg (hq x) (by split_ifs <;> norm_num))
  have hsum := sum_le_sum (fun a (_ : a ∈ (univ : Finset Α)) =>
    mul_le_mul_of_nonneg_left (hinner a) (hp a))
  have heq : (∑ a, p a*((1/2:ℝ)*(if bound a ≤ T then (1:ℝ) else 0))) =
      (1/2:ℝ)*∑ a, p a*(if bound a ≤ T then (1:ℝ) else 0) := by
    rw [mul_sum]; apply sum_congr rfl; intros; ring
  rw [heq] at hsum
  linarith

end RobustGeneralization.BernLower.Tail

namespace RobustGeneralization.BernLower.Tail
open Finset

def bitFlip {ι : Type*} : (ι → Bool) ≃ (ι → Bool) where
  toFun s i := !(s i)
  invFun s i := !(s i)
  left_inv s := by funext i; simp
  right_inv s := by funext i; simp

noncomputable def coin (r : ℝ) (b : Bool) : ℝ := if b then r else 1-r
noncomputable def mass {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → ℝ) (s : ι → Bool) : ℝ :=
  ∏ i, coin (r i) (s i)

@[simp] theorem coin_sum (r : ℝ) : (∑ b : Bool, coin r b) = 1 := by
  simp [coin]

theorem mass_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → ℝ)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1) (s : ι → Bool) : 0 ≤ mass r s := by
  apply prod_nonneg
  intro i _
  unfold coin
  split_ifs <;> linarith [(hr i).1,(hr i).2]

@[simp] theorem mass_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → ℝ) :
    (∑ s, mass r s) = 1 := by
  unfold mass
  rw [← Fintype.prod_sum]
  simp [coin]

@[simp] theorem coin_half (b : Bool) : coin (1/2) b = (1/2:ℝ) := by
  cases b <;> norm_num [coin]

@[simp] theorem lab_not (b : Bool) : lab (!b) = -lab b := by
  cases b <;> norm_num [lab]

theorem product_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
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

theorem activation_mean {ι : Type*} [Fintype ι] [DecidableEq ι] (r u : ι → ℝ) :
    (∑ a, mass r a * ∑ i, u i * (if a i then (1:ℝ) else 0)) = ∑ i, u i*r i := by
  classical
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  change (∑ a : ι → Bool, (∏ j, coin (r j) (a j)) * (u i * (if a i then (1:ℝ) else 0))) = _
  rw [product_coordinate (fun j b => coin (r j) b) i (fun b => u i*(if b then (1:ℝ) else 0))]
  simp [coin]
  ring

theorem product_kernel {ι Α Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Α] [Fintype Ω]
    (p : ι → Α → ℝ) (q : ι → Α → Ω → ℝ) (F : (ι → Ω) → ℝ) :
    (∑ a : ι → Α, (∏ i, p i (a i)) * ∑ x : ι → Ω, (∏ i, q i (a i) (x i))*F x) =
      ∑ x : ι → Ω, (∏ i, ∑ a : Α, p i a*q i a (x i))*F x := by
  classical
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp only [← mul_assoc]
  rw [← sum_mul]
  simp_rw [← prod_mul_distrib]
  congr 1
  exact (Fintype.prod_sum (fun i a => p i a*q i a (x i))).symm

theorem product_project {Ω Δ ι : Type*} [Fintype Ω] [Fintype Δ] [DecidableEq Δ]
    [Fintype ι] [DecidableEq ι] (w : ι → Ω → ℝ) (π : ι → Ω → Δ) (F : (ι → Δ) → ℝ) :
    (∑ S : ι → Ω, (∏ k, w k (S k)) * F (fun k => π k (S k))) =
      ∑ T : ι → Δ, (∏ k, ∑ x : Ω, if π k x = T k then w k x else 0) * F T := by
  classical
  have hi (S : ι → Ω) (T : ι → Δ) :
      (∏ k, if π k (S k) = T k then w k (S k) else 0) =
        if (fun k => π k (S k)) = T then ∏ k, w k (S k) else 0 := by
    by_cases h : (fun k => π k (S k)) = T
    · subst T; simp
    · rw [if_neg h]
      obtain ⟨k,hk⟩ : ∃ k, π k (S k) ≠ T k := by
        by_contra hn
        exact h (funext (fun k => by by_contra hk; exact hn ⟨k,hk⟩))
      exact prod_eq_zero (mem_univ k) (if_neg hk)
  symm
  calc
    _ = ∑ T : ι → Δ, ∑ S : ι → Ω,
        (∏ k, if π k (S k) = T k then w k (S k) else 0) * F T := by
      apply sum_congr rfl
      intro T _
      rw [Fintype.prod_sum, sum_mul]
    _ = ∑ S : ι → Ω, ∑ T : ι → Δ,
        (∏ k, if π k (S k) = T k then w k (S k) else 0) * F T := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro S _
      simp only [hi, ite_mul, zero_mul]
      simp

end RobustGeneralization.BernLower.Tail

namespace RobustGeneralization.BernLower.Tail
open Finset
set_option maxHeartbeats 2000000

theorem mixed_law {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → ℝ) (t : ι → Bool)
    (F : (ι → Bool) → ℝ) :
    (∑ a, mass r a * ∑ s, mass (fun _ : ι => (1/2:ℝ)) s *
      F (fun i => if a i then t i else s i)) =
      ∑ z : ι → Bool, (∏ i, (1+r i*lab (t i)*lab (z i))/2)*F z := by
  classical
  calc
    _ = ∑ a : ι → Bool, (∏ i, coin (r i) (a i)) * ∑ z : ι → Bool,
        (∏ i, ∑ s : Bool, if (if a i then t i else s) = z i then coin (1/2) s else 0)*F z := by
      apply sum_congr rfl
      intro a _
      congr 1
      exact product_project (fun _ s => coin (1/2) s) (fun i s => if a i then t i else s) F
    _ = ∑ z : ι → Bool, (∏ i, ∑ a : Bool, coin (r i) a *
        ∑ s : Bool, if (if a then t i else s) = z i then coin (1/2) s else 0)*F z :=
      product_kernel (fun i (a : Bool) => coin (r i) a)
        (fun i (a z : Bool) => ∑ s : Bool, if (if a then t i else s) = z then coin (1/2) s else 0) F
    _ = _ := by
      apply sum_congr rfl
      intro z _
      congr 1
      apply prod_congr rfl
      intro i _
      cases ht : t i <;> cases hz : z i <;> simp [coin,lab,ht,hz] <;> ring

theorem signed_product_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r w : ι → ℝ) (t : ι → Bool) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1)
    (T γ : ℝ) (hT : 0 < T) (hm : (∑ i, |w i| *r i) ≤ γ*T) :
    (1-γ)/2 ≤ ∑ z : ι → Bool, (∏ i, (1+r i*lab (t i)*lab (z i))/2) *
      (if (∑ i, w i*lab (z i)) ≤ T then (1:ℝ) else 0) := by
  classical
  let shift (a : ι → Bool) : ℝ := ∑ i, w i*lab (t i)*(if a i then (1:ℝ) else 0)
  let bound (a : ι → Bool) : ℝ := ∑ i, |w i| *(if a i then (1:ℝ) else 0)
  let noise (a s : ι → Bool) : ℝ := ∑ i, w i*(if a i then 0 else lab (s i))
  have hb (a : ι → Bool) : shift a ≤ bound a := by
    apply sum_le_sum
    intro i _
    cases ha : a i <;> cases ht : t i <;> simp [ha,ht,lab]
    · exact neg_le_abs (w i)
    · exact le_abs_self (w i)
  have hn (a : ι → Bool) : 0 ≤ bound a :=
    sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (by split_ifs <;> norm_num))
  have hsym (a s : ι → Bool) : noise a (bitFlip s) = -noise a s := by
    simp only [noise,← sum_neg_distrib]
    apply sum_congr rfl
    intro i _
    cases ha : a i <;> simp [ha,bitFlip,lab_not]
  have hmean : (∑ a, mass r a*bound a) ≤ γ*T := by
    change (∑ a, mass r a*∑ i, |w i| *(if a i then (1:ℝ) else 0)) ≤ _
    rw [activation_mean]
    exact hm
  have h := mixture_tail (mass r) (mass (fun _ : ι => (1/2:ℝ)))
    (mass_nonneg r hr) (mass_sum r)
    (mass_nonneg _ (by intro i; norm_num)) (mass_sum _)
    bitFlip (by intro s; simp only [mass,coin_half]) shift bound noise hb hn hsym T γ hT hmean
  have hv (a s : ι → Bool) : shift a+noise a s =
      ∑ i, w i*lab (if a i then t i else s i) := by
    dsimp only [shift,noise]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    cases ha : a i <;> simp [ha]
  simp_rw [hv] at h
  rw [mixed_law r t (fun z => if (∑ i, w i*lab (z i)) ≤ T then (1:ℝ) else 0)] at h
  exact h

end RobustGeneralization.BernLower.Tail

namespace RobustGeneralization.BernLower.Tail
open Finset
set_option maxHeartbeats 2000000

theorem prodLaw_sum (d : ℕ) (μ : Fin d → ℝ) : (∑ z, prodLaw μ z) = 1 := by
  unfold prodLaw
  rw [← Fintype.prod_sum (fun i b => (1+μ i*lab b)/2)]
  have he (i : Fin d) : (∑ b : Bool, (1+μ i*lab b)/2) = 1 := by
    simp [lab]; ring
  simp only [he,prod_const_one]

theorem signed_abs (x : ℝ) : |x| *lab (decide (0 ≤ x)) = x := by
  by_cases h : 0 ≤ x
  · simp [h,lab,abs_of_nonneg h]
  · simp [h,lab,abs_of_nonpos (le_of_lt (lt_of_not_ge h))]

theorem biased_product_tail (d : ℕ) (a γ : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (μ w : Fin d → ℝ) (hμ : ∀ i, |μ i| ≤ a) (hγ : 0 < γ) :
    (1-γ)/2 ≤ ∑ z, prodLaw μ z *
      (if (∑ i, w i*lab (z i)) ≤ (a/γ)*∑ i, |w i| then (1:ℝ) else 0) := by
  classical
  by_cases ha0 : a = 0
  · have hm0 : μ = fun _ => 0 := by
      funext i
      exact abs_eq_zero.mp (le_antisymm (by simpa [ha0] using hμ i) (abs_nonneg _))
    subst μ
    have h := symmetric_half (mass (fun _ : Fin d => (1/2:ℝ)))
      (mass_nonneg _ (by intro i; norm_num)) (mass_sum _)
      bitFlip (by intro s; simp only [mass,coin_half]) (fun z => ∑ i, w i*lab (z i))
      (by intro z; simp [bitFlip,lab_not,mul_neg,← sum_neg_distrib])
    have hp (z : Fin d → Bool) : prodLaw (fun _ => (0:ℝ)) z =
        mass (fun _ : Fin d => (1/2:ℝ)) z := by simp only [prodLaw,mass,zero_mul,add_zero,coin_half]
    simp only [ha0,zero_div,zero_mul,hp]
    linarith
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hW : 0 ≤ ∑ i, |w i| := sum_nonneg (fun i _ => abs_nonneg _)
  by_cases hW0 : (∑ i, |w i|) = 0
  · have hw0 (i : Fin d) : w i = 0 := by
      apply abs_eq_zero.mp
      exact (sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ (univ : Finset (Fin d))) => abs_nonneg (w j))).mp hW0 i (mem_univ i)
    simp only [hw0,zero_mul,sum_const_zero,abs_zero,mul_zero,le_refl,ite_true,mul_one]
    rw [prodLaw_sum]
    linarith
  have hW' : 0 < ∑ i, |w i| := lt_of_le_of_ne hW (Ne.symm hW0)
  have hT : 0 < (a/γ)*(∑ i, |w i|) := mul_pos (div_pos ha' hγ) hW'
  have hm : (∑ i, |w i| * |μ i|) ≤ γ*((a/γ)*∑ i, |w i|) := by
    calc
      _ ≤ ∑ i, |w i| *a := sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hμ i) (abs_nonneg _))
      _ = a*∑ i, |w i| := by rw [← sum_mul]; ring
      _ = _ := by field_simp <;> ring
  have h := signed_product_tail (fun i => |μ i|) w (fun i => decide (0 ≤ μ i))
    (fun i => ⟨abs_nonneg _,(hμ i).trans ha1⟩) ((a/γ)*∑ i, |w i|) γ hT hm
  simpa only [signed_abs,prodLaw] using h

end RobustGeneralization.BernLower.Tail

namespace RobustGeneralization.BernLower.Tail
open Finset
set_option maxHeartbeats 2000000

theorem label_product_law (d : ℕ) (τ : ℝ) (m : Fin d → ℝ) (y : Bool)
    (F : (Fin d → Bool) → ℝ) :
    (∑ θ, prodLaw m θ * ∑ s : Fin d → Bool,
      (∏ i, if s i = (y == θ i) then (1/2:ℝ)+τ else 1/2-τ) *
        F (fun i => y == s i)) =
    ∑ z, prodLaw (fun i => 2*τ*m i) z*F z := by
  classical
  calc
    _ = ∑ θ : Fin d → Bool, (∏ i, (1+m i*lab (θ i))/2) *
        ∑ z : Fin d → Bool, (∏ i, ∑ s : Bool,
          if (y == s) = z i then
            (if s = (y == θ i) then (1/2:ℝ)+τ else 1/2-τ) else 0)*F z := by
      apply sum_congr rfl
      intro θ _
      congr 1
      exact product_project
        (fun i s => if s = (y == θ i) then (1/2:ℝ)+τ else 1/2-τ)
        (fun _ s => y == s) F
    _ = ∑ z : Fin d → Bool, (∏ i, ∑ θ : Bool, (1+m i*lab θ)/2 *
        ∑ s : Bool, if (y == s) = z i then
          (if s = (y == θ) then (1/2:ℝ)+τ else 1/2-τ) else 0)*F z :=
      product_kernel (fun i (θ : Bool) => (1+m i*lab θ)/2)
        (fun _ (θ z : Bool) => ∑ s : Bool, if (y == s) = z then
          (if s = (y == θ) then (1/2:ℝ)+τ else 1/2-τ) else 0) F
    _ = _ := by
      apply sum_congr rfl
      intro z _
      congr 1
      apply prod_congr rfl
      intro i _
      cases y <;> cases hz : z i <;> simp [lab,hz] <;> ring

theorem margin_law (d : ℕ) (τ : ℝ) (m : Fin d → ℝ)
    (F : (Fin d → Bool) → ℝ) :
    (∑ θ, prodLaw m θ * ∑ p : (Fin d → Bool) × Bool,
      bernW θ τ p*F (fun i => p.2 == p.1 i)) =
      ∑ z, prodLaw (fun i => 2*τ*m i) z*F z := by
  classical
  have he (θ : Fin d → Bool) :
      (∑ p : (Fin d → Bool) × Bool, bernW θ τ p*F (fun i => p.2 == p.1 i)) =
      ∑ y : Bool, (1/2:ℝ)*∑ s : Fin d → Bool,
        (∏ i, if s i = (y == θ i) then (1/2:ℝ)+τ else 1/2-τ)*F (fun i => y == s i) := by
    rw [Fintype.sum_prod_type,sum_comm]
    simp only [bernW,mul_sum,mul_assoc]
  simp_rw [he,mul_sum]
  rw [sum_comm]
  have hf (y : Bool) :
      (∑ θ : Fin d → Bool, ∑ s : Fin d → Bool, prodLaw m θ *
        ((1/2:ℝ)*((∏ i, if s i = (y == θ i) then (1/2:ℝ)+τ else 1/2-τ)*F (fun i => y == s i)))) =
      (1/2:ℝ)*∑ z, prodLaw (fun i => 2*τ*m i) z*F z := by
    rw [← label_product_law d τ m y F]
    simp only [mul_sum]
    apply sum_congr rfl
    intro θ _
    apply sum_congr rfl
    intro s _
    ring
  simp_rw [hf]
  simp

end RobustGeneralization.BernLower.Tail

open Finset RobustGeneralization.BernLower RobustGeneralization.BernLower.Tail

theorem accepted_margin_tail_bound (d : ℕ) (τ b γ : ℝ) (hτ : 0 < τ) (hτ' : τ ≤ 1 / 2)
    (hb : 0 ≤ b) (hb' : b ≤ 1) (m : Fin d → ℝ) (hm : ∀ i, |m i| ≤ b) (w : E d) (hγ : 0 < γ) :
    (1 - γ) / 2 ≤ ∑ θ : Fin d → Bool, prodLaw m θ * ∑ p : (Fin d → Bool) × Bool,
      bernW θ τ p *
        (if lab p.2 * inner ℝ w (pm p.1) ≤ (2 * τ * b / γ) * ∑ i, |w i| then 1 else 0) := by
  classical
  have ha : 0 ≤ 2*τ*b := mul_nonneg (by positivity) hb
  have ha1 : 2*τ*b ≤ 1 := by nlinarith
  have hμ (i : Fin d) : |2*τ*m i| ≤ 2*τ*b := by
    rw [abs_mul,abs_of_nonneg (show 0 ≤ 2*τ by positivity)]
    exact mul_le_mul_of_nonneg_left (hm i) (by positivity)
  have h := biased_product_tail d (2*τ*b) γ ha ha1 (fun i => 2*τ*m i) (fun i => w i) hμ hγ
  rw [← margin_law d τ m (fun z =>
    if (∑ i, w i*lab (z i)) ≤ (2*τ*b/γ)*∑ i, |w i| then (1:ℝ) else 0)] at h
  have hl (y s : Bool) : lab (y == s) = lab y*lab s := by
    cases y <;> cases s <;> norm_num [lab]
  have he (p : (Fin d → Bool) × Bool) : lab p.2*inner ℝ w (pm p.1) =
      ∑ i, w i*lab (p.2 == p.1 i) := by
    simp only [PiLp.inner_apply,pm,hl,mul_sum]
    apply sum_congr rfl
    intro i _
    change lab p.2*(lab (p.1 i)*w i) = _
    ring
  simpa only [he] using h

namespace RobustGeneralization.BernLower.RobustBridge
open Finset
variable {d : ℕ}
noncomputable def signVector (w : E d) (i : Fin d) : ℝ := if 0 ≤ w i then 1 else -1
noncomputable def adversary (w x : E d) (y : Bool) (ε : ℝ) : E d :=
  WithLp.toLp 2 (fun i => x i - ε * lab y * signVector w i)

theorem abs_lab (y : Bool) : |lab y| = 1 := by cases y <;> norm_num [lab]
theorem abs_signVector (w : E d) (i : Fin d) : |signVector w i| = 1 := by
  unfold signVector; split_ifs <;> norm_num

theorem signVector_mul (w : E d) (i : Fin d) : signVector w i * w i = |w i| := by
  unfold signVector
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (lt_of_not_ge h)]

theorem adversary_in_ball (w x : E d) (y : Bool) (ε : ℝ) (hε : 0 ≤ ε) :
    adversary w x y ε ∈ linfBall x ε := by
  intro i
  change |x i - ε * lab y * signVector w i - x i| ≤ ε
  rw [show x i - ε * lab y * signVector w i - x i = -(ε * lab y * signVector w i) by ring]
  simp only [abs_neg,abs_mul,abs_lab,abs_signVector,abs_of_nonneg hε,mul_one,le_refl]

theorem adversary_margin (w x : E d) (y : Bool) (ε : ℝ) :
    lab y * inner ℝ w (adversary w x y ε) = lab y * inner ℝ w x - ε * ∑ i, |w i| := by
  have hy : lab y * lab y = 1 := by cases y <;> norm_num [lab]
  simp only [PiLp.inner_apply, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  change lab y * ((x i - ε * lab y * signVector w i) * w i) =
    lab y * (x i * w i) - ε * |w i|
  rw [← signVector_mul w i]
  cases y <;> norm_num [lab] <;> ring

theorem negative_margin_wrong (w x : E d) (y : Bool)
    (h : lab y * inner ℝ w x < 0) : linClf w x ≠ y := by
  cases y <;> simp_all [lab,linClf] <;> linarith

theorem strict_margin_implies_robust (w x : E d) (y : Bool) (ε : ℝ)
    (hε : 0 ≤ ε) (h : lab y * inner ℝ w x < ε * ∑ i, |w i|) :
    ∃ x' ∈ linfBall x ε, linClf w x' ≠ y := by
  refine ⟨adversary w x y ε, adversary_in_ball w x y ε hε, ?_⟩
  apply negative_margin_wrong
  rw [adversary_margin]
  linarith

#print axioms strict_margin_implies_robust
end RobustGeneralization.BernLower.RobustBridge

namespace RobustGeneralization.BernLower.RobustBridge
open Finset Posterior
variable {d n : ℕ}

/-- Every finite observed sample has positive evidence for an interior Bernoulli bias. -/
theorem evidence_pos (τ : ℝ) (hτ : 0 < τ) (hτ' : τ < 1/2)
    (S : Fin n → (Fin d → Bool) × Bool) : 0 < ∑ θ : Fin d → Bool, joint τ θ S := by
  apply sum_pos
  · intro θ _
    rw [joint_factor]
    apply mul_pos (by positivity)
    exact prod_pos (fun i _ => coordW_pos τ hτ hτ' S i (θ i))
  · exact univ_nonempty

/-- The joint posterior is exactly the product of its coordinate laws. -/
theorem joint_eq_evidence_prodLaw (τ : ℝ) (hτ : 0 < τ) (hτ' : τ < 1/2)
    (S : Fin n → (Fin d → Bool) × Bool) (θ : Fin d → Bool) :
    joint τ θ S = (∑ η : Fin d → Bool, joint τ η S) * prodLaw (postMean τ S) θ := by
  have hp (i : Fin d) :
      (1 + postMean τ S i * lab (θ i)) / 2 =
        coordW τ S i (θ i) / (coordW τ S i false + coordW τ S i true) := by
    unfold postMean
    rw [postProb_factor τ hτ hτ',postProb_factor τ hτ hτ']
    have hd : coordW τ S i false + coordW τ S i true ≠ 0 :=
      ne_of_gt (add_pos (coordW_pos τ hτ hτ' S i false) (coordW_pos τ hτ hτ' S i true))
    cases hi : θ i <;> simp only [lab,hi,Bool.false_eq_true,ite_false,ite_true]
    all_goals field_simp; ring
  have hsum : (∑ η : Fin d → Bool, joint τ η S) =
      ((1/2:ℝ)^d * (1/2:ℝ)^n) * ∏ i, (coordW τ S i false + coordW τ S i true) := by
    simp only [joint_factor,← mul_sum,← Fintype.prod_sum,Fintype.sum_bool]
    congr 1
    apply prod_congr rfl
    intro i _
    exact add_comm _ _
  have hd : (∏ i, (coordW τ S i false + coordW τ S i true)) ≠ 0 := by
    apply ne_of_gt
    exact prod_pos (fun i _ => add_pos (coordW_pos τ hτ hτ' S i false) (coordW_pos τ hτ hτ' S i true))
  rw [joint_factor,hsum]
  unfold prodLaw
  simp_rw [hp]
  rw [prod_div_distrib]
  field_simp

#print axioms joint_eq_evidence_prodLaw
end RobustGeneralization.BernLower.RobustBridge

namespace RobustGeneralization.BernLower.RobustBridge
open Finset Tail
variable {d : ℕ}

theorem bernW_nonneg (θ : Fin d → Bool) (τ : ℝ) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/2)
    (p : (Fin d → Bool) × Bool) : 0 ≤ bernW θ τ p := by
  unfold bernW
  apply mul_nonneg (by norm_num)
  apply prod_nonneg
  intro i _
  split_ifs <;> linarith

theorem prodLaw_nonneg (m : Fin d → ℝ) (hm : ∀ i, |m i| ≤ 1) (θ : Fin d → Bool) :
    0 ≤ prodLaw m θ := by
  apply prod_nonneg
  intro i _
  have hi := abs_le.mp (hm i)
  cases h : θ i <;> simp only [lab,h,Bool.false_eq_true,ite_false,ite_true]
  all_goals nlinarith

theorem robErr_nonneg (θ : Fin d → Bool) (τ ε : ℝ)
    (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/2) (f : E d → Bool) : 0 ≤ robErr θ τ f ε := by
  classical
  unfold robErr
  apply sum_nonneg
  intro p _
  exact mul_nonneg (bernW_nonneg θ τ hτ hτ' p) (by split_ifs <;> norm_num)

theorem bernW_label_mass (θ : Fin d → Bool) (τ : ℝ) (y : Bool) :
    (∑ s : Fin d → Bool, bernW θ τ (s,y)) = 1/2 := by
  classical
  unfold bernW
  simp only [Prod.fst,Prod.snd]
  rw [← mul_sum, ← Fintype.prod_sum (fun (i : Fin d) (b : Bool) => if b = (y == θ i) then (1/2:ℝ)+τ else 1/2-τ)]
  have hc (i : Fin d) :
      (∑ b : Bool, if b = (y == θ i) then (1/2:ℝ)+τ else 1/2-τ) = 1 := by
    cases y <;> cases hi : θ i <;> simp [hi] <;> ring
  simp only [hc,prod_const_one,mul_one]

theorem robErr_zero (θ : Fin d → Bool) (τ ε : ℝ) (hε : 0 ≤ ε) :
    robErr θ τ (linClf (0 : E d)) ε = 1/2 := by
  classical
  have he (p : (Fin d → Bool) × Bool) :
      (∃ x' ∈ linfBall (pm p.1) ε, linClf (0 : E d) x' ≠ p.2) ↔ p.2 = false := by
    cases h : p.2
    · constructor
      · intro _; rfl
      · intro _
        refine ⟨pm p.1, ?_, ?_⟩
        · intro i; simp [hε]
        · simp [linClf,h]
    · simp [linClf]
  unfold robErr
  simp_rw [he]
  rw [Fintype.sum_prod_type]
  simpa using bernW_label_mass θ τ false

/-- The strict radius gap converts the accepted margin tail into robust error. -/
theorem robust_error_of_bias (τ b γ ε : ℝ) (hτ : 0 < τ) (hτ' : τ ≤ 1/2)
    (hb : 0 ≤ b) (hb' : b ≤ 1) (hγ : 0 < γ) (hε : 0 ≤ ε)
    (hgap : 2*τ*b/γ < ε) (m : Fin d → ℝ) (hm : ∀ i, |m i| ≤ b) (w : E d) :
    (1-γ)/2 ≤ ∑ θ : Fin d → Bool, prodLaw m θ * robErr θ τ (linClf w) ε := by
  classical
  by_cases hw : w = 0
  · subst w
    simp_rw [robErr_zero _ _ _ hε]
    rw [← sum_mul,prodLaw_sum,one_mul]
    linarith
  have hn : 0 < ∑ i, |w i| := by
    have hnon : 0 ≤ ∑ i, |w i| := sum_nonneg (fun i _ => abs_nonneg _)
    by_contra h
    have he : ∑ i, |w i| = 0 := le_antisymm (le_of_not_gt h) hnon
    have hi := (sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ (univ : Finset (Fin d))) => abs_nonneg (w i))).mp he
    apply hw
    ext i
    exact abs_eq_zero.mp (hi i (mem_univ i))
  apply (accepted_margin_tail_bound d τ b γ hτ hτ' hb hb' m hm w hγ).trans
  apply sum_le_sum
  intro θ _
  apply mul_le_mul_of_nonneg_left _ (prodLaw_nonneg m (fun i => (hm i).trans hb') θ)
  unfold robErr
  apply sum_le_sum
  intro p _
  apply mul_le_mul_of_nonneg_left _ (bernW_nonneg θ τ hτ.le hτ' p)
  split_ifs with hmargin hbad hbad
  · rfl
  · exact False.elim (hbad (strict_margin_implies_robust w (pm p.1) p.2 ε hε
      (hmargin.trans_lt (mul_lt_mul_of_pos_right hgap hn))))
  · norm_num
  · rfl

#print axioms robust_error_of_bias
end RobustGeneralization.BernLower.RobustBridge

namespace RobustGeneralization.BernLower.RobustBridge
open Finset Posterior
variable {d n : ℕ}

theorem expected_error_posterior (g : (Fin n → (Fin d → Bool) × Bool) → E d)
    (τ ε : ℝ) (hτ : 0 < τ) (hτ' : τ < 1/2) :
    expRobErr g τ ε = ∑ S : Fin n → (Fin d → Bool) × Bool,
      (∑ η : Fin d → Bool, joint τ η S) *
        ∑ θ : Fin d → Bool, prodLaw (postMean τ S) θ * robErr θ τ (linClf (g S)) ε := by
  unfold expRobErr
  rw [sum_comm]
  apply sum_congr rfl
  intro S _
  rw [mul_sum]
  apply sum_congr rfl
  intro θ _
  rw [joint_eq_evidence_prodLaw τ hτ hτ' S θ]
  ring

/-- Finite posterior averaging reduces Theorem31 to its explicit scalar bounds. -/
theorem root_of_scalar_bounds
    (g : (Fin n → (Fin d → Bool) × Bool) → E d)
    (τ ε γ : ℝ) (hτ : 0 < τ) (hτ' : τ ≤ 1/4)
    (hε : 0 ≤ ε) (hγ : 0 < γ) (hγ' : γ < 1/2)
    (hn : (n:ℝ) ≤ 1/τ^2)
    (hb : 15*τ*Real.sqrt (2*n*Real.log (4*d/γ)) ≤ 1)
    (hgap : 2*τ*(15*τ*Real.sqrt (2*n*Real.log (4*d/γ)))/γ < ε) :
    1/2-γ ≤ expRobErr g τ ε := by
  classical
  let b := 15*τ*Real.sqrt (2*n*Real.log (4*d/γ))
  let G (S : Fin n → (Fin d → Bool) × Bool) : Prop := ∀ i, |postMean τ S i| ≤ b
  let ev (S : Fin n → (Fin d → Bool) × Bool) := ∑ θ : Fin d → Bool, joint τ θ S
  have hev (S) : 0 ≤ ev S := (evidence_pos τ hτ (by linarith) S).le
  have htail (S) (hG : G S) : (1-γ)/2 ≤
      ∑ θ : Fin d → Bool, prodLaw (postMean τ S) θ * robErr θ τ (linClf (g S)) ε := by
    exact robust_error_of_bias τ b γ ε hτ (by linarith) (by dsimp [b]; positivity)
      hb hγ hε hgap (postMean τ S) hG (g S)
  have htotal (S) : 0 ≤ ∑ θ : Fin d → Bool, joint τ θ S * robErr θ τ (linClf (g S)) ε := by
    apply sum_nonneg
    intro θ _
    exact mul_nonneg (joint_nonneg τ hτ.le (by linarith) θ S)
      (robErr_nonneg θ τ ε hτ.le (by linarith) _)
  have hmean := accepted_posterior_mean_bound d n τ γ hτ hτ' hn hγ hb
  have hgood : 1-γ/2 ≤ ∑ S, ev S * (if G S then (1:ℝ) else 0) := by
    simpa only [ev,G,b,expRobErr,sum_mul] using (by rw [sum_comm] at hmean; exact hmean)
  have hlower : ((1-γ)/2) * (∑ S, ev S * (if G S then (1:ℝ) else 0)) ≤ expRobErr g τ ε := by
    unfold expRobErr
    rw [sum_comm,mul_sum]
    apply sum_le_sum
    intro S _
    by_cases hG : G S
    · simp only [if_pos hG,mul_one]
      have ht := mul_le_mul_of_nonneg_left (htail S hG) (hev S)
      dsimp only [ev] at ht
      simp_rw [mul_sum,← mul_assoc,← joint_eq_evidence_prodLaw τ hτ (by linarith) S] at ht
      simpa only [ev,mul_comm] using ht
    · simpa only [if_neg hG,mul_zero] using htotal S
  have hmul := mul_le_mul_of_nonneg_left hgood (show 0 ≤ (1-γ)/2 by linarith)
  have hscalar : 1/2-γ ≤ ((1-γ)/2)*(1-γ/2) := by nlinarith [sq_nonneg γ]
  exact hscalar.trans (hmul.trans hlower)

#print axioms root_of_scalar_bounds
end RobustGeneralization.BernLower.RobustBridge

namespace RobustGeneralization.BernLower.RobustBridge
open Finset
variable {d : ℕ}

theorem uniform_prior_predictive (τ : ℝ) (s : Fin d → Bool) (y : Bool) :
    (∑ θ : Fin d → Bool, prodLaw (fun _ => 0) θ * bernW θ τ (s,y)) = (1/2:ℝ)^(d+1) := by
  classical
  have he (θ : Fin d → Bool) : prodLaw (fun _ => 0) θ * bernW θ τ (s,y) =
      (1/2:ℝ) * ∏ i, ((1/2:ℝ) * (if s i = (y == θ i) then 1/2+τ else 1/2-τ)) := by
    simp only [prodLaw,zero_mul,add_zero,bernW,prod_mul_distrib]
    ring
  simp_rw [he]
  rw [← mul_sum,← Fintype.prod_sum (fun (i : Fin d) (b : Bool) => (1/2:ℝ)*(if s i = (y == b) then 1/2+τ else 1/2-τ))]
  have hc (i : Fin d) : (∑ b : Bool, (1/2:ℝ) *
      (if s i = (y == b) then 1/2+τ else 1/2-τ)) = 1/2 := by
    cases y <;> cases hi : s i <;> simp [hi] <;> ring
  simp only [hc,prod_const,card_univ,Fintype.card_fin,pow_succ]
  ring

theorem uniform_prior_robust_error (τ ε : ℝ) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/2)
    (hε : 0 ≤ ε) (f : E d → Bool) :
    1/2 ≤ ∑ θ : Fin d → Bool, prodLaw (fun _ => 0) θ * robErr θ τ f ε := by
  classical
  let F (p : (Fin d → Bool) × Bool) : ℝ := if f (pm p.1) ≠ p.2 then 1 else 0
  have hstd : (∑ θ : Fin d → Bool, prodLaw (fun _ => 0) θ *
      ∑ p : (Fin d → Bool) × Bool, bernW θ τ p * F p) = 1/2 := by
    simp only [mul_sum,← mul_assoc]
    rw [sum_comm]
    simp_rw [← sum_mul,uniform_prior_predictive]
    rw [Fintype.sum_prod_type]
    have hs (s : Fin d → Bool) :
        (∑ y : Bool, (1/2:ℝ)^(d+1)*F (s,y)) = (1/2:ℝ)^(d+1) := by
      cases h : f (pm s) <;> simp [F,h]
    simp_rw [hs]
    simp only [sum_const,card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,nsmul_eq_mul]
    push_cast
    rw [pow_succ,← mul_assoc,← mul_pow]
    norm_num
  rw [← hstd]
  apply sum_le_sum
  intro θ _
  apply mul_le_mul_of_nonneg_left _ (prodLaw_nonneg _ (by intro i; norm_num) θ)
  unfold robErr
  apply sum_le_sum
  intro p _
  apply mul_le_mul_of_nonneg_left _ (bernW_nonneg θ τ hτ hτ' p)
  dsimp [F]
  split_ifs with herr hbad hbad
  · norm_num
  · norm_num
  · rfl
  · exact False.elim (hbad ⟨pm p.1,by intro i; simp [hε],herr⟩)

/-- With no training data, every learner has prior-averaged robust error at least one half. -/
theorem no_data_lower_bound (g : (Fin 0 → (Fin d → Bool) × Bool) → E d)
    (τ ε : ℝ) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/2) (hε : 0 ≤ ε) :
    1/2 ≤ expRobErr g τ ε := by
  classical
  let S₀ : Fin 0 → (Fin d → Bool) × Bool := fun i => Fin.elim0 i
  have h := uniform_prior_robust_error τ ε hτ hτ' hε (linClf (g S₀))
  have he : expRobErr g τ ε =
      ∑ θ : Fin d → Bool, prodLaw (fun _ => 0) θ * robErr θ τ (linClf (g S₀)) ε := by
    unfold expRobErr
    apply sum_congr rfl
    intro θ _
    rw [Fintype.sum_unique]
    have hh (S : Fin 0 → (Fin d → Bool) × Bool) :
        joint τ θ S * robErr θ τ (linClf (g S)) ε =
          prodLaw (fun _ => 0) θ * robErr θ τ (linClf (g S₀)) ε := by
      have hs : S = S₀ := by funext i; exact Fin.elim0 i
      rw [hs]
      simp [joint,prodLaw]
    exact hh _
  rw [he]
  exact h

#print axioms uniform_prior_robust_error
end RobustGeneralization.BernLower.RobustBridge

namespace RobustGeneralization.BernLower.RobustBridge

/-- All scalar side conditions used in the posterior/tail composition. -/
theorem scalar_bounds (N L τ ε γ : ℝ) (hN : 0 ≤ N) (hL : 1 ≤ L)
    (hτ : 0 < τ) (hε : 0 < ε) (hε' : ε < 3*τ)
    (hγ : 0 < γ) (hγ' : γ < 1/2)
    (hn : N ≤ ε^2*γ^2/(5000*τ^4*L)) :
    N ≤ 1/τ^2 ∧ 15*τ*Real.sqrt (2*N*L) ≤ 1 ∧
      2*τ*(15*τ*Real.sqrt (2*N*L))/γ < ε := by
  have hden : 0 < 5000*τ^4*L := by positivity
  have hbase := (le_div_iff₀ hden).mp hn
  have hr0 : 0 ≤ Real.sqrt (2*N*L) := Real.sqrt_nonneg _
  have hr2 := Real.sq_sqrt (show 0 ≤ 2*N*L by positivity)
  have hs : (50*τ^2*Real.sqrt (2*N*L))^2 ≤ (ε*γ)^2 := by
    nlinarith [mul_nonneg (sq_nonneg τ) (sq_nonneg τ),
      congrArg (fun x : ℝ => 2500*τ^4*x) hr2]
  have hr : 50*τ^2*Real.sqrt (2*N*L) ≤ ε*γ :=
    (sq_le_sq₀ (by positivity) (by positivity)).mp hs
  have heg : ε*γ < 3*τ/2 := by nlinarith [mul_lt_mul_of_pos_left hγ' hε]
  have hb : 15*τ*Real.sqrt (2*N*L) ≤ 1 := by
    apply (mul_le_mul_iff_right₀ hτ).mp
    nlinarith
  have hgap : 2*τ*(15*τ*Real.sqrt (2*N*L))/γ < ε := by
    apply (div_lt_iff₀ hγ).mpr
    nlinarith [mul_pos hε hγ]
  have he2 : ε^2*γ^2 ≤ 9*τ^2/4 := by
    have hh := (sq_le_sq₀ (show 0 ≤ ε*γ by positivity) (show 0 ≤ 3*τ/2 by positivity)).mpr heg.le
    nlinarith
  have hLL := mul_le_mul_of_nonneg_left hL (show 0 ≤ N*5000*τ^4 by positivity)
  have hnsmall : N ≤ 1/τ^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hτ)).mpr
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hτ)).mp
    nlinarith
  exact ⟨hnsmall,hb,hgap⟩

#print axioms scalar_bounds
end RobustGeneralization.BernLower.RobustBridge

open RobustGeneralization.BernLower RobustGeneralization.BernLower.RobustBridge

theorem solution (d n : ℕ)
    (g : (Fin n → (Fin d → Bool) × Bool) → E d) (τ ε γ : ℝ)
    (hτ : 0 < τ) (hτ' : τ ≤ 1 / 4) (hε : 0 ≤ ε) (hε' : ε < 3 * τ)
    (hγ : 0 < γ) (hγ' : γ < 1 / 2)
    (hn : (n : ℝ) ≤ ε ^ 2 * γ ^ 2 / (5000 * τ ^ 4 * Real.log (4 * d / γ))) :
    1 / 2 - γ ≤ expRobErr g τ ε := by
  by_cases hn0 : n = 0
  · subst n
    exact (by linarith : 1/2-γ ≤ (1/2:ℝ)).trans
      (no_data_lower_bound g τ ε hτ.le (by linarith) hε)
  have hnR : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have he : 0 < ε := by
    by_contra hh
    have hz : ε = 0 := le_antisymm (le_of_not_gt hh) hε
    simp only [hz,zero_pow (by decide : 2 ≠ 0),zero_mul,zero_div] at hn
    linarith
  have hd : d ≠ 0 := by
    intro hz
    simp only [hz,Nat.cast_zero,mul_zero,zero_div,Real.log_zero,div_zero] at hn
    linarith
  have hdR : (1:ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
  have hq : 3 < 4*(d:ℝ)/γ := (lt_div_iff₀ hγ).mpr (by nlinarith)
  have hL : 1 ≤ Real.log (4*(d:ℝ)/γ) :=
    ((Real.lt_log_iff_exp_lt (show 0 < 4*(d:ℝ)/γ by positivity)).mpr
      (Real.exp_one_lt_three.trans hq)).le
  obtain ⟨hnsmall,hb,hgap⟩ := scalar_bounds (n:ℝ) (Real.log (4*(d:ℝ)/γ)) τ ε γ
    (by positivity) hL hτ he hε' hγ hγ' hn
  exact root_of_scalar_bounds g τ ε γ hτ hτ' hε hγ hγ' hnsmall hb hgap

#print axioms solution
