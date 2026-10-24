-- Prove2me | solution 1 for RobustGeneralization.BernLower.lemma29_log_odds_bound
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-24T05:10:09.029555+00:00
-- url     : https://prove2.me/submissions/d8a6e457-5dc0-454b-8eeb-855ed607ce41

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

theorem solution (n : ℕ) (τ δ : ℝ) (hτ : 0 < τ) (hτ' : τ ≤ 1 / 4)
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
