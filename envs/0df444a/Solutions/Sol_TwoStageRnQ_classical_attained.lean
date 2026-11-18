-- Prove2me | solution 1 for TwoStageRnQ.classical_attained
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T00:30:59.095133+00:00
-- url     : https://prove2.me/submissions/37cb7830-edd8-4932-8bce-9e7875f0ce65

import Definitions.Def_TwoStageRnQ_Analytic
import Mathlib.Topology.MetricSpace.CauSeqFilter
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Theorems.Thm_TwoStageRnQ_exact_cost_classical

open Finset Filter Topology

noncomputable section

namespace TwoStageRnQ

lemma hasSum_pow_div_factorial (x : ℝ) :
    HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
  have hs := Real.summable_pow_div_factorial x
  refine (hs.hasSum_iff_tendsto_nat).mpr ?_
  have hc := CauSeq.tendsto_limit (β := ℂ) (Complex.exp' (x : ℂ))
  rw [← Complex.exp_def] at hc
  have hre := (Complex.continuous_re.tendsto _).comp hc
  rw [← Complex.ofReal_exp, Complex.ofReal_re] at hre
  refine hre.congr (fun n => ?_)
  simp only [Function.comp_apply, Complex.exp']
  show (∑ m ∈ range n, (x : ℂ) ^ m / (m.factorial : ℂ)).re = _
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [show ((x : ℂ) ^ m / (m.factorial : ℂ)) = ((x ^ m / (m.factorial : ℝ) : ℝ) : ℂ) by push_cast; ring]
  exact Complex.ofReal_re _

lemma poisW_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (n : ℕ) : 0 ≤ poisW μ n := by
  unfold poisW; positivity

lemma hasSum_poisW (μ : ℝ) : HasSum (poisW μ) 1 := by
  have h := (hasSum_pow_div_factorial μ).mul_left (Real.exp (-μ))
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  have e : poisW μ = fun n : ℕ => Real.exp (-μ) * (μ ^ n / (n.factorial : ℝ)) := by
    funext n; unfold poisW; ring
  rw [e]; exact h

lemma summable_poisW (μ : ℝ) : Summable (poisW μ) := (hasSum_poisW μ).summable

lemma tsum_poisW (μ : ℝ) : ∑' n, poisW μ n = 1 := (hasSum_poisW μ).tsum_eq

lemma poisW_succ_mul (μ : ℝ) (n : ℕ) :
    poisW μ (n + 1) * ((n + 1 : ℕ) : ℝ) = μ * poisW μ n := by
  unfold poisW
  rw [Nat.factorial_succ]
  push_cast
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma hasSum_poisW_mean (μ : ℝ) : HasSum (fun n : ℕ => poisW μ n * (n : ℝ)) μ := by
  have h1 : HasSum (fun n : ℕ => poisW μ (n + 1) * ((n + 1 : ℕ) : ℝ)) μ := by
    have := (hasSum_poisW μ).mul_left μ
    rw [mul_one] at this
    have e : (fun n : ℕ => poisW μ (n + 1) * ((n + 1 : ℕ) : ℝ)) = fun n : ℕ => μ * poisW μ n := by
      funext n; exact poisW_succ_mul μ n
    rw [e]; exact this
  exact (hasSum_nat_add_iff' 1).mp (by simpa using h1)

lemma summable_poisW_mul_nat (μ : ℝ) : Summable (fun n : ℕ => poisW μ n * (n : ℝ)) :=
  (hasSum_poisW_mean μ).summable

lemma tsum_poisW_mul_nat (μ : ℝ) : ∑' n : ℕ, poisW μ n * (n : ℝ) = μ :=
  (hasSum_poisW_mean μ).tsum_eq

def LinGrowth (f : ℕ → ℝ) : Prop := ∃ A B : ℝ, ∀ n : ℕ, |f n| ≤ A + B * n

def PInt (μ : ℝ) (f : ℕ → ℝ) : Prop := Summable (fun n => poisW μ n * |f n|)

lemma PInt.summable {μ : ℝ} (hμ : 0 ≤ μ) {f : ℕ → ℝ} (hf : PInt μ f) :
    Summable (fun n => poisW μ n * f n) := by
  refine Summable.of_norm ?_
  refine hf.congr (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (poisW_nonneg hμ n)]

lemma PInt.of_abs_le {μ : ℝ} (hμ : 0 ≤ μ) {f g : ℕ → ℝ} (hg : PInt μ g) (h : ∀ n, |f n| ≤ g n) :
    PInt μ f := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (poisW_nonneg hμ n) (abs_nonneg _))
    (fun n => ?_) hg
  have hgn : g n = |g n| := (abs_of_nonneg ((abs_nonneg _).trans (h n))).symm
  calc poisW μ n * |f n| ≤ poisW μ n * g n := mul_le_mul_of_nonneg_left (h n) (poisW_nonneg hμ n)
    _ = poisW μ n * |g n| := by rw [← hgn]

lemma pint_const {μ : ℝ} (c : ℝ) : PInt μ (fun _ => c) := by
  unfold PInt; exact (summable_poisW μ).mul_right |c|

lemma pint_nat {μ : ℝ} : PInt μ (fun n => (n : ℝ)) := by
  unfold PInt
  have e : (fun n : ℕ => poisW μ n * |(n : ℝ)|) = fun n : ℕ => poisW μ n * (n : ℝ) := by
    funext n; rw [abs_of_nonneg (Nat.cast_nonneg n)]
  rw [e]; exact summable_poisW_mul_nat μ

lemma PInt.add {μ : ℝ} (hμ : 0 ≤ μ) {f g : ℕ → ℝ} (hf : PInt μ f) (hg : PInt μ g) :
    PInt μ (fun n => f n + g n) := by
  unfold PInt at hf hg ⊢
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (poisW_nonneg hμ n) (abs_nonneg _))
    (fun n => ?_) (Summable.add hf hg)
  have := mul_le_mul_of_nonneg_left (abs_add_le (f n) (g n)) (poisW_nonneg hμ n)
  simp only [Pi.add_apply]
  linarith [mul_add (poisW μ n) |f n| |g n|]

lemma PInt.neg {μ : ℝ} {f : ℕ → ℝ} (hf : PInt μ f) : PInt μ (fun n => -f n) := by
  unfold PInt at hf ⊢; simpa [abs_neg] using hf

lemma PInt.sub {μ : ℝ} (hμ : 0 ≤ μ) {f g : ℕ → ℝ} (hf : PInt μ f) (hg : PInt μ g) :
    PInt μ (fun n => f n - g n) := by
  simpa [sub_eq_add_neg] using hf.add hμ hg.neg

lemma PInt.const_mul {μ : ℝ} {f : ℕ → ℝ} (hf : PInt μ f) (c : ℝ) :
    PInt μ (fun n => c * f n) := by
  unfold PInt at hf ⊢
  simp_rw [abs_mul, mul_left_comm _ |c|]
  exact hf.mul_left |c|

lemma PInt.div_const {μ : ℝ} {f : ℕ → ℝ} (hf : PInt μ f) (c : ℝ) :
    PInt μ (fun n => f n / c) := by
  simpa [div_eq_inv_mul] using hf.const_mul c⁻¹

lemma PInt.sum {μ : ℝ} (hμ : 0 ≤ μ) {ι : Type*} (s : Finset ι) {f : ι → ℕ → ℝ}
    (hf : ∀ i ∈ s, PInt μ (f i)) : PInt μ (fun n => ∑ i ∈ s, f i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (pint_const (μ := μ) 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (mem_insert_self a s)).add hμ (ih (fun i hi => hf i (mem_insert_of_mem hi)))

lemma PInt.abs {μ : ℝ} {f : ℕ → ℝ} (hf : PInt μ f) : PInt μ (fun n => |f n|) := by
  unfold PInt at hf ⊢; simpa using hf

lemma PInt.of_affine {μ : ℝ} (hμ : 0 ≤ μ) {f g : ℕ → ℝ} (hg : PInt μ g) {A B C : ℝ}
    (h : ∀ n, |f n| ≤ A + B * |g n| + C * n) : PInt μ f :=
  PInt.of_abs_le hμ (((pint_const A).add hμ (hg.abs.const_mul B)).add hμ (pint_nat.const_mul C))
    (fun n => h n)

lemma LinGrowth.pint {μ : ℝ} (hμ : 0 ≤ μ) {f : ℕ → ℝ} (hf : LinGrowth f) : PInt μ f := by
  obtain ⟨A, B, h⟩ := hf
  exact PInt.of_abs_le hμ ((pint_const A).add hμ (pint_nat.const_mul B)) h

lemma pexp_add {μ : ℝ} (hμ : 0 ≤ μ) {f g : ℕ → ℝ} (hf : PInt μ f) (hg : PInt μ g) :
    pexp μ (fun n => f n + g n) = pexp μ f + pexp μ g := by
  unfold pexp
  simp_rw [mul_add]
  exact Summable.tsum_add (hf.summable hμ) (hg.summable hμ)

lemma pexp_sub {μ : ℝ} (hμ : 0 ≤ μ) {f g : ℕ → ℝ} (hf : PInt μ f) (hg : PInt μ g) :
    pexp μ (fun n => f n - g n) = pexp μ f - pexp μ g := by
  unfold pexp
  simp_rw [mul_sub]
  exact Summable.tsum_sub (hf.summable hμ) (hg.summable hμ)

lemma pexp_const_mul (μ c : ℝ) (f : ℕ → ℝ) : pexp μ (fun n => c * f n) = c * pexp μ f := by
  unfold pexp
  simp_rw [mul_left_comm _ c]
  exact tsum_mul_left

lemma pexp_div_const (μ c : ℝ) (f : ℕ → ℝ) : pexp μ (fun n => f n / c) = pexp μ f / c := by
  simp_rw [div_eq_inv_mul]; rw [pexp_const_mul]

lemma pexp_const (μ c : ℝ) : pexp μ (fun _ => c) = c := by
  unfold pexp
  rw [tsum_mul_right, tsum_poisW, one_mul]

lemma pexp_nat (μ : ℝ) : pexp μ (fun n => (n : ℝ)) = μ := tsum_poisW_mul_nat μ

lemma pexp_mono {μ : ℝ} (hμ : 0 ≤ μ) {f g : ℕ → ℝ} (hf : PInt μ f) (hg : PInt μ g)
    (h : ∀ n, f n ≤ g n) : pexp μ f ≤ pexp μ g := by
  unfold pexp
  exact Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (h n) (poisW_nonneg hμ n))
    (hf.summable hμ) (hg.summable hμ)

lemma pexp_nonneg {μ : ℝ} (hμ : 0 ≤ μ) {f : ℕ → ℝ} (h : ∀ n, 0 ≤ f n) : 0 ≤ pexp μ f := by
  unfold pexp
  exact tsum_nonneg (fun n => mul_nonneg (poisW_nonneg hμ n) (h n))

lemma pexp_finset_sum {μ : ℝ} (hμ : 0 ≤ μ) {ι : Type*} (s : Finset ι) {f : ι → ℕ → ℝ}
    (hf : ∀ i ∈ s, PInt μ (f i)) :
    pexp μ (fun n => ∑ i ∈ s, f i n) = ∑ i ∈ s, pexp μ (f i) := by
  unfold pexp
  simp_rw [Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun i hi => (hf i hi).summable hμ)

lemma pexp_congr {μ : ℝ} {f g : ℕ → ℝ} (h : ∀ n, f n = g n) : pexp μ f = pexp μ g := by
  unfold pexp; simp_rw [h]

lemma abs_sub_nat (y : ℝ) (n : ℕ) : |y - n| ≤ |y| + n := by
  have h := abs_sub y (n : ℝ)
  rwa [abs_of_nonneg (show (0 : ℝ) ≤ n from Nat.cast_nonneg n)] at h

lemma phi_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (x : ℝ) : 0 ≤ phi a b x := by
  unfold phi; positivity

lemma phi_eq_max {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (x : ℝ) : phi a b x = max (a * x) (-(b * x)) := by
  unfold phi
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx, max_eq_right (by linarith : -x ≤ 0)]
    rw [max_eq_left (by nlinarith : -(b * x) ≤ a * x)]; ring
  · rw [max_eq_right hx, max_eq_left (by linarith : 0 ≤ -x)]
    rw [max_eq_right (by nlinarith : a * x ≤ -(b * x))]; ring

lemma phi_ge_left {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (x : ℝ) : a * x ≤ phi a b x := by
  rw [phi_eq_max ha hb]; exact le_max_left _ _

lemma phi_ge_right {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (x : ℝ) : -(b * x) ≤ phi a b x := by
  rw [phi_eq_max ha hb]; exact le_max_right _ _

lemma phi_convex {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x y : ℝ) :
    phi a b (θ * x + (1 - θ) * y) ≤ θ * phi a b x + (1 - θ) * phi a b y := by
  rw [phi_eq_max ha hb, phi_eq_max ha hb, phi_eq_max ha hb]
  have h1' : 0 ≤ 1 - θ := by linarith
  apply max_le
  · have := mul_le_mul_of_nonneg_left (le_max_left (a * x) (-(b * x))) h0
    have := mul_le_mul_of_nonneg_left (le_max_left (a * y) (-(b * y))) h1'
    nlinarith
  · have := mul_le_mul_of_nonneg_left (le_max_right (a * x) (-(b * x))) h0
    have := mul_le_mul_of_nonneg_left (le_max_right (a * y) (-(b * y))) h1'
    nlinarith

lemma phi_abs_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (x : ℝ) : |phi a b x| ≤ (a + b) * |x| := by
  rw [abs_of_nonneg (phi_nonneg ha hb x)]
  unfold phi
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx, max_eq_right (by linarith : -x ≤ 0), abs_of_nonneg hx]; nlinarith
  · rw [max_eq_right hx, max_eq_left (by linarith : 0 ≤ -x), abs_of_nonpos hx]; nlinarith

lemma phi_linGrowth {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (y : ℝ) :
    LinGrowth (fun n : ℕ => phi a b (y - n)) := by
  refine ⟨(a + b) * |y|, a + b, fun n => ?_⟩
  refine (phi_abs_le ha hb _).trans ?_
  have : |y - n| ≤ |y| + n := abs_sub_nat y n
  nlinarith

namespace Params

variable (P : Params)

lemma mu1_nonneg : 0 ≤ P.mu1 := mul_nonneg P.lam_nonneg P.L1_nonneg
lemma mu2_nonneg : 0 ≤ P.mu2 := mul_nonneg P.lam_nonneg P.L2_nonneg
lemma k1_nonneg : 0 ≤ P.k1 := mul_nonneg P.lam_nonneg P.K1_nonneg
lemma k2_nonneg : 0 ≤ P.k2 := mul_nonneg P.lam_nonneg P.K2_nonneg
lemma H0_nonneg : 0 ≤ P.H0 :=
  mul_nonneg (mul_nonneg P.h2_nonneg P.lam_nonneg) P.L1_nonneg
lemma a_nonneg : 0 ≤ P.h1 + P.h2 := add_nonneg P.h1_nonneg P.h2_nonneg

lemma lossDown_nonneg (x : ℝ) : 0 ≤ P.lossDown x :=
  pexp_nonneg P.mu1_nonneg (fun _ => phi_nonneg P.a_nonneg P.p_nonneg _)

lemma G0_nonneg (x : ℝ) : 0 ≤ P.G0 x := add_nonneg P.H0_nonneg (P.lossDown_nonneg x)

lemma lossDown_le (x : ℝ) : P.lossDown x ≤ (P.h1 + P.h2 + P.p) * (|x| + P.mu1) := by
  have hc := add_nonneg P.a_nonneg P.p_nonneg
  have hb : PInt P.mu1 (fun n : ℕ => (P.h1 + P.h2 + P.p) * (|x| + n)) :=
    ((pint_const |x|).add P.mu1_nonneg pint_nat).const_mul _
  calc P.lossDown x ≤ pexp P.mu1 (fun n : ℕ => (P.h1 + P.h2 + P.p) * (|x| + n)) := by
        refine pexp_mono P.mu1_nonneg ((phi_linGrowth P.a_nonneg P.p_nonneg x).pint P.mu1_nonneg)
          hb (fun n => ?_)
        refine (le_abs_self _).trans ((phi_abs_le P.a_nonneg P.p_nonneg _).trans ?_)
        exact mul_le_mul_of_nonneg_left (abs_sub_nat x n) hc
    _ = (P.h1 + P.h2 + P.p) * (|x| + P.mu1) := by
        rw [pexp_const_mul, pexp_add P.mu1_nonneg (pint_const _) pint_nat, pexp_const, pexp_nat]

lemma lossDown_convex {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x y : ℝ) :
    P.lossDown (θ * x + (1 - θ) * y) ≤ θ * P.lossDown x + (1 - θ) * P.lossDown y := by
  unfold lossDown
  have hx := (phi_linGrowth P.a_nonneg P.p_nonneg x).pint P.mu1_nonneg
  have hy := (phi_linGrowth P.a_nonneg P.p_nonneg y).pint P.mu1_nonneg
  have hm := (phi_linGrowth P.a_nonneg P.p_nonneg (θ * x + (1 - θ) * y)).pint P.mu1_nonneg
  rw [← pexp_const_mul, ← pexp_const_mul,
    ← pexp_add P.mu1_nonneg (hx.const_mul θ) (hy.const_mul (1 - θ))]
  refine pexp_mono P.mu1_nonneg hm ((hx.const_mul θ).add P.mu1_nonneg (hy.const_mul (1 - θ)))
    (fun n => ?_)
  have := phi_convex P.a_nonneg P.p_nonneg h0 h1 (x - n) (y - n)
  convert this using 2; ring

lemma G0_convex {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x y : ℝ) :
    P.G0 (θ * x + (1 - θ) * y) ≤ θ * P.G0 x + (1 - θ) * P.G0 y := by
  unfold G0; nlinarith [P.lossDown_convex h0 h1 x y]

lemma G0_abs_le (x : ℝ) : |P.G0 x| ≤ P.H0 + (P.h1 + P.h2 + P.p) * (|x| + P.mu1) := by
  rw [abs_of_nonneg (P.G0_nonneg x)]; unfold G0; linarith [P.lossDown_le x]

end Params

lemma latAvg_nonneg {j : ℕ} {F : ℝ → ℝ} (hF : ∀ x, 0 ≤ F x) (x : ℝ) : 0 ≤ latAvg j F x := by
  unfold latAvg; exact div_nonneg (Finset.sum_nonneg (fun v _ => hF _)) (Nat.cast_nonneg j)

lemma latAvg_convex {j : ℕ} {F : ℝ → ℝ}
    (hF : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 → ∀ x y, F (θ * x + (1 - θ) * y) ≤ θ * F x + (1 - θ) * F y)
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x y : ℝ) :
    latAvg j F (θ * x + (1 - θ) * y) ≤ θ * latAvg j F x + (1 - θ) * latAvg j F y := by
  unfold latAvg
  rw [mul_div_assoc', mul_div_assoc', ← add_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg j)
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun v _ => ?_)
  have := hF θ h0 h1 (x - v) (y - v)
  rwa [show θ * (x - v) + (1 - θ) * (y - v) = θ * x + (1 - θ) * y - v by ring] at this

lemma latAvg_abs_le {j : ℕ} {F : ℝ → ℝ} {A B : ℝ} (hB : 0 ≤ B) (hF : ∀ x, |F x| ≤ A + B * |x|)
    (x : ℝ) : |latAvg j F x| ≤ A + B * (|x| + j) := by
  unfold latAvg
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    simp only [range_zero, sum_empty, CharP.cast_eq_zero, div_zero, abs_zero]
    have := (abs_nonneg (F 0)).trans (hF 0); simp at this; nlinarith [abs_nonneg x]
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  rw [abs_div, abs_of_pos hjr, div_le_iff₀ hjr]
  calc |∑ v ∈ range j, F (x - v)| ≤ ∑ v ∈ range j, |F (x - v)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ v ∈ range j, (A + B * (|x| + j)) := Finset.sum_le_sum (fun v hv => by
        refine (hF _).trans ?_
        have hv' : (v : ℝ) ≤ j := by exact_mod_cast (Finset.mem_range.mp hv).le
        have : |x - v| ≤ |x| + j := by
          have := abs_sub_nat x v; linarith
        nlinarith)
    _ = (A + B * (|x| + j)) * j := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

namespace Params

variable (P : Params)

lemma latAvg_G0_nonneg (m : ℕ) (x : ℝ) : 0 ≤ latAvg m P.G0 x := latAvg_nonneg P.G0_nonneg x

lemma latAvg_G0_convex (m : ℕ) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x y : ℝ) :
    latAvg m P.G0 (θ * x + (1 - θ) * y) ≤ θ * latAvg m P.G0 x + (1 - θ) * latAvg m P.G0 y :=
  latAvg_convex (fun θ h0 h1 x y => P.G0_convex h0 h1 x y) h0 h1 x y

lemma latAvg_G0_abs_le (m : ℕ) (x : ℝ) :
    |latAvg m P.G0 x| ≤ (P.H0 + (P.h1 + P.h2 + P.p) * P.mu1) + (P.h1 + P.h2 + P.p) * (|x| + m) := by
  have hc : 0 ≤ P.h1 + P.h2 + P.p := add_nonneg P.a_nonneg P.p_nonneg
  have := latAvg_abs_le (j := m) (F := P.G0) (A := P.H0 + (P.h1 + P.h2 + P.p) * P.mu1) hc
    (fun x => by have := P.G0_abs_le x; linarith) x
  linarith

lemma pint_latAvg_G0 (m : ℕ) {f : ℕ → ℝ} (hf : PInt P.mu2 f) :
    PInt P.mu2 (fun n => latAvg m P.G0 (f n)) := by
  refine PInt.of_affine P.mu2_nonneg hf (A := (P.H0 + (P.h1 + P.h2 + P.p) * P.mu1)
    + (P.h1 + P.h2 + P.p) * m) (B := P.h1 + P.h2 + P.p) (C := 0) (fun n => ?_)
  have := P.latAvg_G0_abs_le m (f n); linarith

end Params

end TwoStageRnQ

open Finset Filter Topology

noncomputable section

namespace TwoStageRnQ

namespace Params

variable (P : Params)

lemma jointObj_nonneg {m1 m2 : ℕ} {z : ℝ} {x : ℕ → Fin m2 → ℝ} (hx : P.JointFeasible m2 z x) :
    0 ≤ P.jointObj m1 m2 z x := by
  unfold jointObj
  refine pexp_nonneg P.mu2_nonneg (fun d => div_nonneg (Finset.sum_nonneg (fun j _ => ?_))
    (Nat.cast_nonneg _))
  have := hx.1 d j
  exact add_nonneg (P.latAvg_G0_nonneg m1 _) (mul_nonneg P.h2_nonneg (by linarith))

lemma Vjoint_nonneg (m1 m2 : ℕ) : 0 ≤ P.Vjoint m1 m2 :=
  Real.iInf_nonneg (fun zx => P.jointObj_nonneg zx.2)

end Params

lemma abs_min_le_add (a b : ℝ) : |min a b| ≤ |a| + |b| :=
  (abs_min_le_max_abs_abs).trans (max_le (by linarith [abs_nonneg b]) (by linarith [abs_nonneg a]))

lemma abs_sub_nat_le (z : ℝ) (d : ℕ) (c : ℝ) : |z - d - c| ≤ |z| + |c| + d := by
  have h1 := abs_sub (z - d) c
  have h2 := abs_sub_nat z d
  linarith

namespace Params

variable (P : Params)

lemma Vjoint_feasible_nonempty (m2 : ℕ) :
    Nonempty {zx : ℝ × (ℕ → Fin m2 → ℝ) // P.JointFeasible m2 zx.1 zx.2} :=
  ⟨⟨(0, fun d j => -(d : ℝ) - ((j : ℕ) : ℝ)), fun d j => by simp,
    fun j => ((pint_nat.neg).sub P.mu2_nonneg (pint_const _))⟩⟩

end Params

end TwoStageRnQ

open Finset Filter Topology

noncomputable section

namespace TwoStageRnQ

lemma sum_div' {ι : Type*} (s : Finset ι) (f : ι → ℝ) (a : ℝ) :
    (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a := by
  simp only [div_eq_mul_inv, Finset.sum_mul]

lemma phi_affine {a b : ℝ} (n : ℤ) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    phi a b ((n : ℝ) + θ) = (1 - θ) * phi a b n + θ * phi a b ((n : ℝ) + 1) := by
  unfold phi
  rcases le_or_gt 0 n with hn | hn
  · have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
    rw [max_eq_left (by linarith : (0 : ℝ) ≤ n + θ), max_eq_left hn',
      max_eq_left (by linarith : (0 : ℝ) ≤ n + 1), max_eq_right (by linarith : -((n : ℝ) + θ) ≤ 0),
      max_eq_right (by linarith : -(n : ℝ) ≤ 0), max_eq_right (by linarith : -((n : ℝ) + 1) ≤ 0)]
    ring
  · have hn' : (n : ℝ) + 1 ≤ 0 := by
      have : n + 1 ≤ 0 := by omega
      exact_mod_cast this
    rw [max_eq_right (by linarith : (n : ℝ) + θ ≤ 0), max_eq_right (by linarith : (n : ℝ) ≤ 0),
      max_eq_right hn', max_eq_left (by linarith : (0 : ℝ) ≤ -((n : ℝ) + θ)),
      max_eq_left (by linarith : (0 : ℝ) ≤ -(n : ℝ)), max_eq_left (by linarith : (0 : ℝ) ≤ -((n : ℝ) + 1))]
    ring

namespace Params

variable (P : Params)

lemma lossDown_affine (n : ℤ) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    P.lossDown ((n : ℝ) + θ) = (1 - θ) * P.lossDown n + θ * P.lossDown ((n : ℝ) + 1) := by
  have hμ := P.mu1_nonneg
  unfold lossDown
  have i0 := (phi_linGrowth P.a_nonneg P.p_nonneg (n : ℝ)).pint hμ
  have i1 := (phi_linGrowth P.a_nonneg P.p_nonneg ((n : ℝ) + 1)).pint hμ
  rw [← pexp_const_mul, ← pexp_const_mul, ← pexp_add hμ (i0.const_mul _) (i1.const_mul _)]
  refine pexp_congr (fun d => ?_)
  have := phi_affine (a := P.h1 + P.h2) (b := P.p) (n - d) h0 h1
  push_cast at this
  convert this using 2 <;> ring

lemma G0_affine (n : ℤ) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    P.G0 ((n : ℝ) + θ) = (1 - θ) * P.G0 n + θ * P.G0 ((n : ℝ) + 1) := by
  unfold G0; rw [P.lossDown_affine n h0 h1]; ring

lemma latAvg_G0_affine (m : ℕ) (n : ℤ) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    latAvg m P.G0 ((n : ℝ) + θ)
      = (1 - θ) * latAvg m P.G0 n + θ * latAvg m P.G0 ((n : ℝ) + 1) := by
  unfold latAvg
  rw [mul_div_assoc', mul_div_assoc', ← add_div, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun v _ => ?_)
  have := P.G0_affine (n - v) h0 h1
  push_cast at this
  convert this using 2 <;> ring

def psi (m : ℕ) (v : ℝ) : ℝ := latAvg m P.G0 v - P.h2 * v

lemma psi_affine (m : ℕ) (n : ℤ) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    P.psi m ((n : ℝ) + θ) = (1 - θ) * P.psi m n + θ * P.psi m ((n : ℝ) + 1) := by
  unfold psi; rw [P.latAvg_G0_affine m n h0 h1]; ring

lemma psi_convex (m : ℕ) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x y : ℝ) :
    P.psi m (θ * x + (1 - θ) * y) ≤ θ * P.psi m x + (1 - θ) * P.psi m y := by
  unfold psi; nlinarith [P.latAvg_G0_convex m h0 h1 x y]

lemma G0_ge_neg (w : ℝ) : -(P.p * w) ≤ P.G0 w := by
  have hμ := P.mu1_nonneg
  have hL := (phi_linGrowth P.a_nonneg P.p_nonneg w).pint hμ
  have hlin : PInt P.mu1 (fun n : ℕ => -(P.p * (w - n))) :=
    (((pint_const w).sub hμ pint_nat).const_mul P.p).neg
  have h := pexp_mono hμ hlin hL (fun n => phi_ge_right P.a_nonneg P.p_nonneg (w - n))
  have e : pexp P.mu1 (fun n : ℕ => -(P.p * (w - n))) = -(P.p * (w - P.mu1)) := by
    have : (fun n : ℕ => -(P.p * (w - n))) = fun n : ℕ => (-P.p) * (w - n) := by ext n; ring
    rw [this, pexp_const_mul, pexp_sub hμ (pint_const w) pint_nat, pexp_const, pexp_nat]; ring
  rw [e] at h
  unfold G0 lossDown
  have := P.H0_nonneg; have := P.p_nonneg; nlinarith

lemma psi_ge {m : ℕ} (hm : 0 < m) (v : ℝ) : -((P.p + P.h2) * v) ≤ P.psi m v := by
  unfold psi latAvg
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : ∑ i ∈ range m, (-(P.p * v)) ≤ ∑ i ∈ range m, P.G0 (v - i) :=
    Finset.sum_le_sum (fun i _ => by
      have := P.G0_ge_neg (v - i)
      have := P.p_nonneg
      have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      nlinarith)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  have : -(P.p * v) ≤ (∑ i ∈ range m, P.G0 (v - i)) / m := by
    rw [le_div_iff₀ hmr]; linarith
  linarith

lemma lossDown_eq_zero_of (hp : P.p = 0) {v : ℝ} (hv : v ≤ 0) : P.lossDown v = 0 := by
  unfold lossDown
  have : ∀ d : ℕ, phi (P.h1 + P.h2) P.p (v - d) = 0 := fun d => by
    unfold phi; rw [hp, max_eq_right (by have := Nat.cast_nonneg (α := ℝ) d; linarith)]; ring
  simp_rw [this]
  exact pexp_const _ 0

lemma exists_int_min {m : ℕ} (hm : 0 < m) (Z : ℤ) :
    ∃ r : ℤ, r ≤ Z ∧ ∀ n : ℤ, n ≤ Z → P.psi m r ≤ P.psi m n := by
  by_cases hph : 0 < P.p + P.h2
  · set t : ℝ := -(P.psi m Z) / (P.p + P.h2) with ht
    set L : ℤ := ⌊t⌋ with hL
    have htZ : t ≤ Z := by
      rw [ht, div_le_iff₀ hph]; have := P.psi_ge hm (Z : ℝ); linarith
    have hLZ : L ≤ Z := Int.floor_le_iff.mpr (by linarith)
    obtain ⟨r, hr, hmin⟩ := (Finset.Icc L Z).exists_min_image (fun n : ℤ => P.psi m n)
      ⟨Z, Finset.mem_Icc.mpr ⟨hLZ, le_refl Z⟩⟩
    refine ⟨r, (Finset.mem_Icc.mp hr).2, fun n hn => ?_⟩
    by_cases hnL : L ≤ n
    · exact hmin n (Finset.mem_Icc.mpr ⟨hnL, hn⟩)
    · push_neg at hnL
      have h1 : (n : ℝ) < t := by
        have hn1 : (n : ℝ) + 1 ≤ L := by exact_mod_cast hnL
        have := Int.floor_le t
        linarith
      have h2 := P.psi_ge hm (n : ℝ)
      have h3 : (P.p + P.h2) * n < (P.p + P.h2) * t := mul_lt_mul_of_pos_left h1 hph
      have h4 : (P.p + P.h2) * t = -(P.psi m Z) := by rw [ht]; field_simp
      have h5 := hmin Z (Finset.mem_Icc.mpr ⟨hLZ, le_refl Z⟩)
      linarith
  · have hp : P.p = 0 := by linarith [P.p_nonneg, P.h2_nonneg]
    have hh : P.h2 = 0 := by linarith [P.p_nonneg, P.h2_nonneg]
    refine ⟨min Z 0, min_le_left _ _, fun n _ => ?_⟩
    have hz : P.psi m ((min Z 0 : ℤ) : ℝ) = 0 := by
      unfold psi latAvg
      rw [hh, zero_mul, sub_zero]
      have : ∀ i ∈ range m, P.G0 (((min Z 0 : ℤ) : ℝ) - i) = 0 := fun i _ => by
        unfold G0 H0
        rw [hh, zero_mul, zero_mul, zero_add]
        apply P.lossDown_eq_zero_of hp
        have : ((min Z 0 : ℤ) : ℝ) ≤ 0 := by exact_mod_cast min_le_right Z 0
        have := Nat.cast_nonneg (α := ℝ) i
        linarith
      rw [Finset.sum_eq_zero this, zero_div]
    rw [hz]
    unfold psi
    rw [hh, zero_mul, sub_zero]
    exact P.latAvg_G0_nonneg m n

lemma psi_min_real (m : ℕ) {Z r : ℤ} (hmin : ∀ n : ℤ, n ≤ Z → P.psi m r ≤ P.psi m n)
    {x : ℝ} (hx : x ≤ Z) : P.psi m r ≤ P.psi m x := by
  set k : ℤ := ⌊x⌋
  set θ : ℝ := Int.fract x
  have h0 : 0 ≤ θ := Int.fract_nonneg x
  have h1 : θ < 1 := Int.fract_lt_one x
  have hx' : x = (k : ℝ) + θ := (Int.floor_add_fract x).symm
  have hk : k ≤ Z := Int.floor_le_iff.mpr (by linarith)
  rw [hx', P.psi_affine m k h0 h1.le]
  by_cases hθ : θ = 0
  · rw [hθ]; simp only [sub_zero, one_mul, zero_mul, add_zero]; exact hmin k hk
  · have hk1 : k + 1 ≤ Z := by
      have hpos : 0 < θ := lt_of_le_of_ne h0 (Ne.symm hθ)
      have : (k : ℝ) < Z := by linarith
      have : k < Z := by exact_mod_cast this
      omega
    have a := hmin k hk
    have b := hmin (k + 1) hk1
    push_cast at b
    nlinarith

lemma psi_cap (m : ℕ) {Z r : ℤ} (hmin : ∀ n : ℤ, n ≤ Z → P.psi m r ≤ P.psi m n)
    {Y x : ℝ} (hY : Y ≤ Z) (hxY : x ≤ Y) : P.psi m (min (r : ℝ) Y) ≤ P.psi m x := by
  have hrx : P.psi m r ≤ P.psi m x := P.psi_min_real m hmin (hxY.trans hY)
  rcases le_total (r : ℝ) Y with h | h
  · rw [min_eq_left h]; exact hrx
  · rw [min_eq_right h]
    rcases eq_or_lt_of_le hxY with hxe | hxl
    · rw [hxe]
    rcases eq_or_lt_of_le h with hYr | hYr
    · rw [hYr]; exact hrx
    · set θ : ℝ := ((r : ℝ) - Y) / ((r : ℝ) - x) with hθ
      have hd : (0 : ℝ) < (r : ℝ) - x := by linarith
      have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hd.le
      have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hd]; linarith
      have hY' : θ * x + (1 - θ) * (r : ℝ) = Y := by
        rw [hθ]; field_simp; ring
      have := P.psi_convex m hθ0 hθ1 x (r : ℝ)
      rw [hY'] at this
      nlinarith

def capT (m1 : ℕ) (r Y : ℝ) : ℝ := latAvg m1 P.G0 (min r Y) + P.h2 * (Y - min r Y)

def capPhi (m1 m2 : ℕ) (r z : ℝ) : ℝ :=
  pexp P.mu2 (fun d => (∑ j : Fin m2, P.capT m1 r (z - d - ((j : ℕ) : ℝ))) / m2)

lemma pint_capT (m1 : ℕ) (r z c : ℝ) : PInt P.mu2 (fun d : ℕ => P.capT m1 r (z - d - c)) := by
  have hμ := P.mu2_nonneg
  have hmin : PInt P.mu2 (fun d : ℕ => min r (z - d - c)) :=
    PInt.of_affine hμ (pint_const 0) (A := |r| + |z| + |c|) (B := 0) (C := 1) (fun d => by
      have := abs_min_le_add r (z - d - c)
      have := abs_sub_nat_le z d c
      simp; nlinarith)
  unfold capT
  exact (P.pint_latAvg_G0 m1 hmin).add hμ
    (((((pint_const z).sub hμ pint_nat).sub hμ (pint_const c)).sub hμ hmin).const_mul _)

lemma pint_capInt (m1 m2 : ℕ) (r z : ℝ) :
    PInt P.mu2 (fun d : ℕ => (∑ j : Fin m2, P.capT m1 r (z - d - ((j : ℕ) : ℝ))) / m2) :=
  PInt.div_const (PInt.sum P.mu2_nonneg _ (fun j _ => P.pint_capT m1 r z _)) _

lemma capPhi_le_jointObj {m1 m2 : ℕ} {Z r : ℤ} (hmin : ∀ n : ℤ, n ≤ Z → P.psi m1 r ≤ P.psi m1 n)
    {z : ℝ} (hzZ : z ≤ Z) {x : ℕ → Fin m2 → ℝ} (hx : P.JointFeasible m2 z x) :
    P.capPhi m1 m2 r z ≤ P.jointObj m1 m2 z x := by
  have hμ := P.mu2_nonneg
  unfold capPhi jointObj
  refine pexp_mono hμ (P.pint_capInt m1 m2 r z) ?_ (fun d => ?_)
  · refine PInt.div_const (PInt.sum hμ _ (fun j _ => ?_)) _
    exact (P.pint_latAvg_G0 m1 (hx.2 j)).add hμ
      ((((((pint_const z).sub hμ pint_nat).sub hμ (pint_const _)).sub hμ (hx.2 j))).const_mul _)
  · refine div_le_div_of_nonneg_right (Finset.sum_le_sum (fun j _ => ?_)) (Nat.cast_nonneg _)
    have hY : z - d - ((j : ℕ) : ℝ) ≤ Z := by
      have := Nat.cast_nonneg (α := ℝ) d; have := Nat.cast_nonneg (α := ℝ) (j : ℕ); linarith
    have := P.psi_cap m1 hmin hY (hx.1 d j)
    unfold capT
    unfold psi at this
    linarith

lemma capT_affine (m1 : ℕ) (r K : ℤ) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    P.capT m1 r ((K : ℝ) + θ) = (1 - θ) * P.capT m1 r K + θ * P.capT m1 r ((K : ℝ) + 1) := by
  unfold capT
  rcases le_or_gt (K + 1) r with h | h
  · have h' : (K : ℝ) + 1 ≤ r := by exact_mod_cast h
    rw [min_eq_right (by linarith : (K : ℝ) + θ ≤ r), min_eq_right (by linarith : (K : ℝ) ≤ r),
      min_eq_right h', P.latAvg_G0_affine m1 K h0 h1]
    ring
  · have h' : (r : ℝ) ≤ K := by
      have : r ≤ K := by omega
      exact_mod_cast this
    rw [min_eq_left (by linarith : (r : ℝ) ≤ K + θ), min_eq_left h',
      min_eq_left (by linarith : (r : ℝ) ≤ K + 1)]
    ring

lemma capPhi_affine (m1 m2 : ℕ) (r k : ℤ) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    P.capPhi m1 m2 r ((k : ℝ) + θ)
      = (1 - θ) * P.capPhi m1 m2 r k + θ * P.capPhi m1 m2 r ((k : ℝ) + 1) := by
  have hμ := P.mu2_nonneg
  unfold capPhi
  rw [← pexp_const_mul, ← pexp_const_mul,
    ← pexp_add hμ ((P.pint_capInt m1 m2 r _).const_mul _) ((P.pint_capInt m1 m2 r _).const_mul _)]
  refine pexp_congr (fun d => ?_)
  rw [mul_div_assoc', mul_div_assoc', ← add_div, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have := P.capT_affine m1 r (k - d - (j : ℕ)) h0 h1
  push_cast at this
  convert this using 2 <;> ring_nf

lemma capPhi_ge_int (m1 m2 : ℕ) (r : ℤ) (z : ℝ) :
    ∃ z' : ℤ, (z' = ⌊z⌋ ∨ z' = ⌊z⌋ + 1) ∧ P.capPhi m1 m2 r z' ≤ P.capPhi m1 m2 r z := by
  have h0 : 0 ≤ Int.fract z := Int.fract_nonneg z
  have h1 : Int.fract z < 1 := Int.fract_lt_one z
  have hz : z = (⌊z⌋ : ℝ) + Int.fract z := (Int.floor_add_fract z).symm
  have haff := P.capPhi_affine m1 m2 r ⌊z⌋ h0 h1.le
  rw [← hz] at haff
  rcases le_total (P.capPhi m1 m2 r ⌊z⌋) (P.capPhi m1 m2 r ((⌊z⌋ : ℝ) + 1)) with h | h
  · exact ⟨⌊z⌋, Or.inl rfl, by rw [haff]; nlinarith⟩
  · exact ⟨⌊z⌋ + 1, Or.inr rfl, by push_cast; rw [haff]; nlinarith⟩

def grpSize (m1 m2 b : ℕ) : ℕ := (m2 + m1 - 1 - b) / m1

lemma lt_grpSize_iff {m1 m2 b t : ℕ} (hm1 : 0 < m1) (hb : b < m1) :
    t < grpSize m1 m2 b ↔ b + m1 * t < m2 := by
  unfold grpSize
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hm1, add_mul, one_mul, mul_comm t m1]
  generalize m1 * t = u
  omega

lemma sum_range_regroup {m1 : ℕ} (hm1 : 0 < m1) (m2 : ℕ) (f : ℕ → ℝ) :
    ∑ j ∈ range m2, f j = ∑ b ∈ range m1, ∑ t ∈ range (grpSize m1 m2 b), f (b + m1 * t) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun j => j % m1) (t := range m1)
    (fun j _ => Finset.mem_range.mpr (Nat.mod_lt j hm1))]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  have hb' := Finset.mem_range.mp hb
  have hfib : (range m2).filter (fun j => j % m1 = b)
      = (range (grpSize m1 m2 b)).image (fun t => b + m1 * t) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hj, hjb⟩
      have hdm := Nat.div_add_mod j m1
      rw [hjb] at hdm
      refine ⟨j / m1, (lt_grpSize_iff hm1 hb').mpr (by omega), by omega⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨(lt_grpSize_iff hm1 hb').mp ht, ?_⟩
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb']
  rw [hfib, Finset.sum_image]
  intro t1 _ t2 _ h
  have : m1 * t1 = m1 * t2 := by simpa using h
  exact Nat.eq_of_mul_eq_mul_left hm1 this

lemma grpSize_sum {m1 : ℕ} (hm1 : 0 < m1) (m2 : ℕ) :
    ∑ b ∈ range m1, (grpSize m1 m2 b : ℝ) = m2 := by
  have := sum_range_regroup hm1 m2 (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at this
  exact this.symm

lemma grpSize_pos_zero {m1 m2 : ℕ} (hm1 : 0 < m1) (hm2 : 0 < m2) : 0 < grpSize m1 m2 0 := by
  have := (lt_grpSize_iff (t := 0) (m2 := m2) hm1 hm1).mpr (by simpa using hm2)
  exact this

def grpEll (m1 m2 : ℕ) (z' r : ℤ) (b : ℕ) : ℤ :=
  z' - r - b - m1 * ((grpSize m1 m2 b : ℤ) - 1)

def grpCost (m1 : ℕ+) (m2 : ℕ) (z' r : ℤ) (b : ℕ) : ℝ :=
  P.classicalFormula (r - (m1 : ℕ)) (r - (m1 : ℕ) + grpEll m1 m2 z' r b) m1
    (Nat.toPNat' (grpSize m1 m2 b))

lemma capT_eq (m1 : ℕ) (r w : ℝ) :
    latAvg m1 P.G0 (r - max (-w) 0) + P.h2 * max w 0 = P.capT m1 r (r + w) := by
  unfold capT
  rcases le_total w 0 with h | h
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ -w), max_eq_right h, min_eq_right (by linarith)]
    ring
  · rw [max_eq_right (by linarith : -w ≤ 0), max_eq_left h, min_eq_left (by linarith)]
    ring

lemma grp_invCost {m1 : ℕ+} {m2 : ℕ} (z' r : ℤ) {b : ℕ} (hg : 0 < grpSize m1 m2 b) :
    ((grpSize m1 m2 b : ℕ) : ℝ) * P.invCost (grpSize m1 m2 b) m1 ((r : ℝ)) (grpEll m1 m2 z' r b)
      = ∑ t ∈ range (grpSize m1 m2 b), pexp P.mu2 (fun d : ℕ =>
          P.capT m1 r ((z' : ℝ) - d - ((b + (m1 : ℕ) * t : ℕ) : ℝ))) := by
  unfold invCost
  have hgr : ((grpSize m1 m2 b : ℕ) : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ hgr]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' := Finset.mem_range.mp hj
  refine pexp_congr (fun d => ?_)
  rw [P.capT_eq]
  congr 1
  unfold grpEll
  have hsub : ((grpSize m1 m2 b - 1 - j : ℕ) : ℝ) = (grpSize m1 m2 b : ℝ) - 1 - j := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  push_cast
  rw [hsub]
  ring

lemma grpCost_eq {m1 : ℕ+} {m2 : ℕ} (z' r : ℤ) {b : ℕ} (hg : 0 < grpSize m1 m2 b) :
    ((grpSize m1 m2 b : ℕ) : ℝ) * P.grpCost m1 m2 z' r b
      = ((grpSize m1 m2 b : ℕ) : ℝ) * (P.k1 / ((m1 : ℕ) : ℝ)) + P.k2 / ((m1 : ℕ) : ℝ)
        + ∑ t ∈ range (grpSize m1 m2 b), pexp P.mu2 (fun d : ℕ =>
          P.capT m1 r ((z' : ℝ) - d - ((b + (m1 : ℕ) * t : ℕ) : ℝ))) := by
  rw [← P.grp_invCost z' r hg]
  unfold grpCost classicalFormula
  have hn : ((Nat.toPNat' (grpSize m1 m2 b) : ℕ)) = grpSize m1 m2 b := by
    rw [Nat.toPNat'_coe, if_pos hg]
  rw [hn]
  have hgr : ((grpSize m1 m2 b : ℕ) : ℝ) ≠ 0 := by positivity
  have hm1r : ((m1 : ℕ) : ℝ) ≠ 0 := by positivity
  have e1 : ((r - ((m1 : ℕ) : ℤ) : ℤ) : ℝ) + ((m1 : ℕ) : ℝ) = (r : ℝ) := by push_cast; ring
  have e2 : (((r - ((m1 : ℕ) : ℤ) + grpEll m1 m2 z' r b : ℤ) : ℝ) - ((r - ((m1 : ℕ) : ℤ) : ℤ) : ℝ))
      = (grpEll m1 m2 z' r b : ℝ) := by push_cast; ring
  rw [e1, e2]
  field_simp

end Params

end TwoStageRnQ

open Finset Filter Topology

noncomputable section

namespace TwoStageRnQ

lemma sum_abs_ge (m : ℕ) : ∀ x : ℝ, ((m : ℝ) ^ 2 - 1) / 4 ≤ ∑ i ∈ range m, |x - i| := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro x
    match m with
    | 0 => norm_num
    | 1 => simp
    | k + 2 =>
      have h1 : ∑ i ∈ range (k + 2), |x - i|
          = |x - 0| + (|x - ((k + 1 : ℕ) : ℝ)| + ∑ i ∈ range k, |(x - 1) - i|) := by
        rw [Finset.sum_range_succ', Finset.sum_range_succ]
        have : ∀ i ∈ range k, |x - ((i + 1 : ℕ) : ℝ)| = |(x - 1) - i| := fun i _ => by
          push_cast; ring_nf
        rw [Finset.sum_congr rfl this]
        push_cast; ring
      rw [h1]
      have hk := ih k (by omega) (x - 1)
      have htri : ((k : ℝ) + 1) ≤ |x - 0| + |x - ((k + 1 : ℕ) : ℝ)| := by
        have := abs_sub_abs_le_abs_sub (x - 0) (x - ((k + 1 : ℕ) : ℝ))
        have h2 : |(x - 0) - (x - ((k + 1 : ℕ) : ℝ))| = (k : ℝ) + 1 := by
          push_cast
          rw [show x - 0 - (x - ((k : ℝ) + 1)) = (k : ℝ) + 1 by ring]
          exact abs_of_pos (by positivity)
        have h3 := abs_sub (x - 0) (x - ((k + 1 : ℕ) : ℝ))
        linarith
      push_cast at hk htri ⊢
      nlinarith

lemma avg_abs_ge (x : ℝ) {m : ℕ} (hm : 0 < m) :
    ((m : ℝ) - 1) / 4 ≤ (∑ i ∈ range m, |x - i|) / m := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [le_div_iff₀ hmr]
  have := sum_abs_ge m x
  nlinarith

namespace Params

variable (P : Params)

lemma G0_ge_lin (w : ℝ) : (P.h1 + P.h2) * (w - P.mu1) ≤ P.G0 w := by
  have hμ := P.mu1_nonneg
  have hL := (phi_linGrowth P.a_nonneg P.p_nonneg w).pint hμ
  have hlin : PInt P.mu1 (fun n : ℕ => (P.h1 + P.h2) * (w - n)) :=
    ((pint_const w).sub hμ pint_nat).const_mul _
  have h := pexp_mono hμ hlin hL (fun n => phi_ge_left P.a_nonneg P.p_nonneg (w - n))
  have e : pexp P.mu1 (fun n : ℕ => (P.h1 + P.h2) * (w - n)) = (P.h1 + P.h2) * (w - P.mu1) := by
    rw [pexp_const_mul, pexp_sub hμ (pint_const w) pint_nat, pexp_const, pexp_nat]
  rw [e] at h
  unfold G0 lossDown
  have := P.H0_nonneg
  linarith

lemma G0_ge_abs (w : ℝ) :
    min (P.h1 + P.h2) P.p * |w| - (P.h1 + P.h2) * P.mu1 ≤ P.G0 w := by
  have h1 := P.G0_ge_lin w
  have h2 := P.G0_ge_neg w
  have hm1 : min (P.h1 + P.h2) P.p ≤ P.h1 + P.h2 := min_le_left _ _
  have hm2 : min (P.h1 + P.h2) P.p ≤ P.p := min_le_right _ _
  have hm0 : 0 ≤ min (P.h1 + P.h2) P.p := le_min P.a_nonneg P.p_nonneg
  have := P.mu1_nonneg
  have := P.a_nonneg
  rcases le_total 0 w with hw | hw
  · rw [abs_of_nonneg hw]; nlinarith
  · rw [abs_of_nonpos hw]; nlinarith

lemma latAvg_G0_ge {m : ℕ} (hm : 0 < m) (x : ℝ) :
    min (P.h1 + P.h2) P.p * (((m : ℝ) - 1) / 4) - (P.h1 + P.h2) * P.mu1
      ≤ latAvg m P.G0 x := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hm0 : 0 ≤ min (P.h1 + P.h2) P.p := le_min P.a_nonneg P.p_nonneg
  unfold latAvg
  have hs : ∑ i ∈ range m, (min (P.h1 + P.h2) P.p * |x - i| - (P.h1 + P.h2) * P.mu1)
      ≤ ∑ i ∈ range m, P.G0 (x - i) := Finset.sum_le_sum (fun i _ => P.G0_ge_abs _)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hs
  have ha := avg_abs_ge x hm
  rw [le_div_iff₀ hmr]
  rw [le_div_iff₀ hmr] at ha
  nlinarith

lemma latAvg_G0_ge_neg {m : ℕ} (hm : 0 < m) (v : ℝ) : -(P.p * v) ≤ latAvg m P.G0 v := by
  have := P.psi_ge hm v
  unfold psi at this
  linarith

lemma psi_ge_up {m : ℕ} (hm : 0 < m) (v : ℝ) :
    P.h1 * v - (P.h1 + P.h2) * (m + P.mu1) ≤ P.psi m v := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  unfold psi latAvg
  have hs : ∑ i ∈ range m, ((P.h1 + P.h2) * (v - m - P.mu1)) ≤ ∑ i ∈ range m, P.G0 (v - i) :=
    Finset.sum_le_sum (fun i hi => by
      have := P.G0_ge_lin (v - i)
      have hi' : (i : ℝ) ≤ m := by exact_mod_cast (Finset.mem_range.mp hi).le
      have := P.a_nonneg
      nlinarith)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  have : (P.h1 + P.h2) * (v - m - P.mu1) ≤ (∑ i ∈ range m, P.G0 (v - i)) / m := by
    rw [le_div_iff₀ hmr]; linarith
  nlinarith

lemma exists_int_min_global {m : ℕ} (hm : 0 < m) (hh1 : 0 < P.h1) :
    ∃ r : ℤ, ∀ n : ℤ, P.psi m r ≤ P.psi m n := by
  set C := (P.h1 + P.h2) * (m + P.mu1) with hC
  set Z : ℤ := max 0 ⌈(P.psi m 0 + C) / P.h1⌉ with hZ
  obtain ⟨r, hrZ, hmin⟩ := P.exists_int_min hm Z
  refine ⟨r, fun n => ?_⟩
  by_cases hn : n ≤ Z
  · exact hmin n hn
  · push_neg at hn
    have h0 : P.psi m r ≤ P.psi m ((0 : ℤ) : ℝ) := hmin 0 (le_max_left _ _)
    have hZ' : (P.psi m 0 + C) / P.h1 ≤ (Z : ℝ) := by
      have := Int.le_ceil ((P.psi m 0 + C) / P.h1)
      have : (⌈(P.psi m 0 + C) / P.h1⌉ : ℝ) ≤ (Z : ℝ) := by exact_mod_cast le_max_right _ _
      linarith
    have hnZ : (Z : ℝ) < n := by exact_mod_cast hn
    have hup := P.psi_ge_up hm n
    have : P.psi m 0 + C ≤ P.h1 * n := by
      rw [div_le_iff₀ hh1] at hZ'; nlinarith
    push_cast at h0
    linarith

lemma capT_ge_lower {m1 : ℕ} (hm1 : 0 < m1) (r Y : ℝ) :
    min (P.h1 + P.h2) P.p * (((m1 : ℝ) - 1) / 4) - (P.h1 + P.h2) * P.mu1 ≤ P.capT m1 r Y := by
  unfold capT
  have := P.latAvg_G0_ge hm1 (min r Y)
  have : 0 ≤ P.h2 * (Y - min r Y) := mul_nonneg P.h2_nonneg (by linarith [min_le_right r Y])
  linarith

lemma capT_ge_neg {m1 : ℕ} (hm1 : 0 < m1) (r Y : ℝ) : -(P.p * Y) ≤ P.capT m1 r Y := by
  unfold capT
  have hp := P.p_nonneg
  rcases le_total r Y with h | h
  · rw [min_eq_left h]
    have := P.latAvg_G0_ge_neg hm1 r
    have : 0 ≤ P.h2 * (Y - r) := mul_nonneg P.h2_nonneg (by linarith)
    nlinarith
  · rw [min_eq_right h]
    have := P.latAvg_G0_ge_neg hm1 Y
    linarith

lemma capT_ge_up (m1 : ℕ) (r Y : ℝ) : P.h2 * (Y - r) ≤ P.capT m1 r Y := by
  unfold capT
  have hl := P.latAvg_G0_nonneg m1 (min r Y)
  rcases le_total r Y with h | h
  · rw [min_eq_left h] at hl ⊢; linarith
  · rw [min_eq_right h] at hl ⊢
    have : P.h2 * (Y - r) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos P.h2_nonneg (by linarith)
    linarith

lemma capT_ge_abs {m1 : ℕ} (hm1 : 0 < m1) (r Y : ℝ) :
    min P.h2 P.p * |Y| - P.h2 * |r| ≤ P.capT m1 r Y := by
  have hb1 : min P.h2 P.p ≤ P.h2 := min_le_left _ _
  have hb2 : min P.h2 P.p ≤ P.p := min_le_right _ _
  have hb0 : 0 ≤ min P.h2 P.p := le_min P.h2_nonneg P.p_nonneg
  have hn := P.capT_ge_neg hm1 r Y
  have hu := P.capT_ge_up m1 r Y
  have hh2 := P.h2_nonneg
  have hp := P.p_nonneg
  have hnn : 0 ≤ P.capT m1 r Y := by
    unfold capT
    have := P.latAvg_G0_nonneg m1 (min r Y)
    have : 0 ≤ P.h2 * (Y - min r Y) := mul_nonneg P.h2_nonneg (by linarith [min_le_right r Y])
    linarith
  rcases le_total 0 Y with hY | hY
  · rw [abs_of_nonneg hY]
    rcases le_total 0 r with hr | hr
    · rw [abs_of_nonneg hr]; nlinarith
    · rw [abs_of_nonpos hr]; nlinarith
  · rw [abs_of_nonpos hY]
    have := mul_nonneg (sub_nonneg.mpr hb2) (neg_nonneg.mpr hY)
    have := mul_nonneg hh2 (abs_nonneg r)
    nlinarith

lemma capPhi_ge_of {m1 m2 : ℕ} (hm2 : 0 < m2) (r z : ℝ) (g : ℕ → ℝ) (hg : PInt P.mu2 g)
    (h : ∀ d : ℕ, g d ≤ (∑ j : Fin m2, P.capT m1 r (z - d - ((j : ℕ) : ℝ))) / m2) :
    pexp P.mu2 g ≤ P.capPhi m1 m2 r z :=
  pexp_mono P.mu2_nonneg hg (P.pint_capInt m1 m2 r z) h

lemma capPhi_ge_lower {m1 m2 : ℕ} (hm1 : 0 < m1) (hm2 : 0 < m2) (r z : ℝ) :
    min (P.h1 + P.h2) P.p * (((m1 : ℝ) - 1) / 4) - (P.h1 + P.h2) * P.mu1 ≤ P.capPhi m1 m2 r z := by
  have hm2r : (0 : ℝ) < m2 := by exact_mod_cast hm2
  have := P.capPhi_ge_of (m1 := m1) hm2 r z (fun _ => min (P.h1 + P.h2) P.p * (((m1 : ℝ) - 1) / 4)
    - (P.h1 + P.h2) * P.mu1) (pint_const _) (fun d => by
      rw [le_div_iff₀ hm2r]
      have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m2)))
        (fun j _ => P.capT_ge_lower hm1 r (z - d - ((j : ℕ) : ℝ)))
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
      linarith)
  rwa [pexp_const] at this

lemma capPhi_ge_m2 {m1 m2 : ℕ} (hm1 : 0 < m1) (hm2 : 0 < m2) (r z : ℝ) :
    min P.h2 P.p * (((m2 : ℝ) - 1) / 4) - P.h2 * |r| ≤ P.capPhi m1 m2 r z := by
  have hm2r : (0 : ℝ) < m2 := by exact_mod_cast hm2
  have hb0 : 0 ≤ min P.h2 P.p := le_min P.h2_nonneg P.p_nonneg
  have := P.capPhi_ge_of (m1 := m1) hm2 r z (fun _ => min P.h2 P.p * (((m2 : ℝ) - 1) / 4) - P.h2 * |r|)
    (pint_const _) (fun d => by
      rw [le_div_iff₀ hm2r]
      have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m2)))
        (fun j _ => P.capT_ge_abs hm1 r (z - d - ((j : ℕ) : ℝ)))
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul] at hs
      have ha := avg_abs_ge (z - d) hm2
      rw [le_div_iff₀ hm2r] at ha
      rw [Fin.sum_univ_eq_sum_range (fun j => |z - d - (j : ℝ)|) m2] at hs
      nlinarith)
  rwa [pexp_const] at this

lemma capPhi_ge_neg {m1 m2 : ℕ} (hm1 : 0 < m1) (hm2 : 0 < m2) (r z : ℝ) :
    -(P.p * z) ≤ P.capPhi m1 m2 r z := by
  have hm2r : (0 : ℝ) < m2 := by exact_mod_cast hm2
  have hp := P.p_nonneg
  have := P.capPhi_ge_of (m1 := m1) hm2 r z (fun _ => -(P.p * z)) (pint_const _) (fun d => by
      rw [le_div_iff₀ hm2r]
      have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m2)))
        (fun j _ => (show -(P.p * z) ≤ P.capT m1 r (z - d - ((j : ℕ) : ℝ)) by
          have := P.capT_ge_neg hm1 r (z - d - ((j : ℕ) : ℝ))
          have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
          have hj : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
          nlinarith))
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
      linarith)
  rwa [pexp_const] at this

lemma capPhi_ge_up (m1 : ℕ) {m2 : ℕ} (hm2 : 0 < m2) (r z : ℝ) :
    P.h2 * (z - r - m2 - P.mu2) ≤ P.capPhi m1 m2 r z := by
  have hm2r : (0 : ℝ) < m2 := by exact_mod_cast hm2
  have hμ := P.mu2_nonneg
  have hh := P.h2_nonneg
  have hg : PInt P.mu2 (fun d : ℕ => P.h2 * (z - r - m2 - d)) :=
    ((pint_const _).sub hμ pint_nat).const_mul _
  have := P.capPhi_ge_of (m1 := m1) hm2 r z (fun d : ℕ => P.h2 * (z - r - m2 - d)) hg (fun d => by
      rw [le_div_iff₀ hm2r]
      have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m2)))
        (fun j _ => (show P.h2 * (z - r - m2 - d) ≤ P.capT m1 r (z - d - ((j : ℕ) : ℝ)) by
          have := P.capT_ge_up m1 r (z - d - ((j : ℕ) : ℝ))
          have hj : ((j : ℕ) : ℝ) ≤ m2 := by exact_mod_cast j.isLt.le
          nlinarith))
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
      linarith)
  have e : pexp P.mu2 (fun d : ℕ => P.h2 * (z - r - m2 - d)) = P.h2 * (z - r - m2 - P.mu2) := by
    rw [pexp_const_mul, pexp_sub hμ (pint_const _) pint_nat, pexp_const, pexp_nat]
  rwa [e] at this

lemma exists_int_min_capPhi {m1 m2 : ℕ} (hm1 : 0 < m1) (hm2 : 0 < m2) (hh2 : 0 < P.h2)
    (hp : 0 < P.p) (r : ℤ) : ∃ z : ℤ, ∀ z' : ℤ, P.capPhi m1 m2 r z ≤ P.capPhi m1 m2 r z' := by
  set M := P.capPhi m1 m2 r r with hM
  have hM0 : 0 ≤ M := by
    have := P.capPhi_ge_lower hm1 hm2 (r : ℝ) (r : ℝ)
    have hnn : 0 ≤ P.capPhi m1 m2 r r := by
      unfold capPhi
      refine pexp_nonneg P.mu2_nonneg (fun d => div_nonneg (Finset.sum_nonneg (fun j _ => ?_))
        (Nat.cast_nonneg _))
      unfold capT
      have := P.latAvg_G0_nonneg m1 (min (r : ℝ) ((r : ℝ) - d - ((j : ℕ) : ℝ)))
      have : 0 ≤ P.h2 * (((r : ℝ) - d - ((j : ℕ) : ℝ)) - min (r : ℝ) ((r : ℝ) - d - ((j : ℕ) : ℝ))) :=
        mul_nonneg P.h2_nonneg (by linarith [min_le_right (r : ℝ) ((r : ℝ) - d - ((j : ℕ) : ℝ))])
      linarith
    exact hnn
  set L : ℤ := ⌊-M / P.p⌋ with hL
  set U : ℤ := ⌈M / P.h2 + r + m2 + P.mu2⌉ with hU
  have hrL : L ≤ r := by
    have := P.capPhi_ge_neg hm1 hm2 (r : ℝ) (r : ℝ)
    have h1 : -M / P.p ≤ (r : ℝ) := by rw [div_le_iff₀ hp]; linarith
    exact Int.floor_le_iff.mpr (by linarith)
  have hrU : r ≤ U := by
    have := P.mu2_nonneg
    have h1 : (r : ℝ) ≤ M / P.h2 + r + m2 + P.mu2 := by
      have : 0 ≤ M / P.h2 := div_nonneg hM0 hh2.le
      have : (0 : ℝ) ≤ m2 := Nat.cast_nonneg _
      linarith
    have h2 : (r : ℝ) ≤ (U : ℝ) := h1.trans (Int.le_ceil _)
    exact_mod_cast h2
  obtain ⟨z0, hz0, hmin⟩ := (Finset.Icc L U).exists_min_image (fun z : ℤ => P.capPhi m1 m2 r z)
    ⟨r, Finset.mem_Icc.mpr ⟨hrL, hrU⟩⟩
  have hz0M : P.capPhi m1 m2 r z0 ≤ M := hmin r (Finset.mem_Icc.mpr ⟨hrL, hrU⟩)
  refine ⟨z0, fun z' => ?_⟩
  by_cases hz' : z' ∈ Finset.Icc L U
  · exact hmin z' hz'
  · rw [Finset.mem_Icc, not_and_or] at hz'
    rcases hz' with h | h
    · push_neg at h
      have h1 : (z' : ℝ) < -M / P.p := by
        have : (z' : ℝ) + 1 ≤ L := by exact_mod_cast h
        have := Int.floor_le (-M / P.p)
        linarith
      have h2 : M < -(P.p * z') := by
        rw [lt_div_iff₀ hp] at h1; linarith
      have := P.capPhi_ge_neg hm1 hm2 (r : ℝ) (z' : ℝ)
      linarith
    · push_neg at h
      have h1 : M / P.h2 + r + m2 + P.mu2 < (z' : ℝ) := by
        have : (U : ℝ) < z' := by exact_mod_cast h
        have := Int.le_ceil (M / P.h2 + r + m2 + P.mu2)
        linarith
      have h2 : M < P.h2 * (z' - r - m2 - P.mu2) := by
        have : M / P.h2 < z' - r - m2 - P.mu2 := by linarith
        rwa [div_lt_iff₀ hh2, mul_comm] at this
      have := P.capPhi_ge_up m1 hm2 (r : ℝ) (z' : ℝ)
      linarith

end Params

namespace Params

variable (P : Params)

lemma exists_formula_le_capPhi (m1 m2 : ℕ+) (z' r : ℤ) :
    ∃ c : ℤ × ℤ × ℕ+ × ℕ+, P.classicalFormula c.1 c.2.1 c.2.2.1 c.2.2.2
      ≤ P.k1 / ((m1 : ℕ) : ℝ) + P.k2 / ((m2 : ℕ) : ℝ) + P.capPhi m1 m2 r z' := by
  have hm1 := m1.pos
  have hm2 := m2.pos
  have hμ := P.mu2_nonneg
  have hm2r : (0 : ℝ) < ((m2 : ℕ) : ℝ) := by exact_mod_cast hm2
  have hm1r : (0 : ℝ) < ((m1 : ℕ) : ℝ) := by exact_mod_cast hm1
  set s := (range (m1 : ℕ)).filter (fun b => 0 < grpSize m1 m2 b) with hs
  set w : ℕ → ℝ := fun b => ((grpSize m1 m2 b : ℕ) : ℝ) / ((m2 : ℕ) : ℝ) with hw
  set X := P.k1 / ((m1 : ℕ) : ℝ) + P.k2 / ((m2 : ℕ) : ℝ) + P.capPhi m1 m2 r z' with hX

  have hsum_w : ∑ b ∈ s, w b = 1 := by
    rw [hs, Finset.sum_filter]
    have : ∀ b ∈ range (m1 : ℕ), (if 0 < grpSize m1 m2 b then w b else 0) = w b := by
      intro b _
      split_ifs with h
      · rfl
      · simp [hw, Nat.eq_zero_of_not_pos h]
    rw [Finset.sum_congr rfl this, hw, ← sum_div', grpSize_sum hm1, div_self hm2r.ne']

  have hcap : ∑ b ∈ s, (∑ t ∈ range (grpSize m1 m2 b), pexp P.mu2 (fun d : ℕ =>
        P.capT m1 r ((z' : ℝ) - d - ((b + (m1 : ℕ) * t : ℕ) : ℝ)))) / ((m2 : ℕ) : ℝ)
      = P.capPhi m1 m2 r z' := by
    rw [← sum_div']
    have hfilt : ∑ b ∈ s, ∑ t ∈ range (grpSize m1 m2 b), pexp P.mu2 (fun d : ℕ =>
          P.capT m1 r ((z' : ℝ) - d - ((b + (m1 : ℕ) * t : ℕ) : ℝ)))
        = ∑ b ∈ range (m1 : ℕ), ∑ t ∈ range (grpSize m1 m2 b), pexp P.mu2 (fun d : ℕ =>
          P.capT m1 r ((z' : ℝ) - d - ((b + (m1 : ℕ) * t : ℕ) : ℝ))) := by
      rw [hs, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      split_ifs with h
      · rfl
      · simp [Nat.eq_zero_of_not_pos h]
    rw [hfilt, ← sum_range_regroup hm1 (m2 : ℕ)
      (fun j => pexp P.mu2 (fun d : ℕ => P.capT m1 r ((z' : ℝ) - d - (j : ℝ))))]
    unfold capPhi
    rw [pexp_div_const, pexp_finset_sum hμ _ (fun j _ => P.pint_capT m1 r _ _),
      Fin.sum_univ_eq_sum_range (fun j => pexp P.mu2 (fun d : ℕ => P.capT m1 r ((z' : ℝ) - d - (j : ℝ))))]

  have hweighted : ∑ b ∈ s, w b * P.grpCost m1 m2 z' r b ≤ X := by
    have hterm : ∀ b ∈ s, w b * P.grpCost m1 m2 z' r b
        = w b * (P.k1 / ((m1 : ℕ) : ℝ)) + P.k2 / (((m1 : ℕ) : ℝ) * ((m2 : ℕ) : ℝ))
          + (∑ t ∈ range (grpSize m1 m2 b), pexp P.mu2 (fun d : ℕ =>
              P.capT m1 r ((z' : ℝ) - d - ((b + (m1 : ℕ) * t : ℕ) : ℝ)))) / ((m2 : ℕ) : ℝ) := by
      intro b hb
      have hg := (Finset.mem_filter.mp hb).2
      have := P.grpCost_eq (m1 := m1) (m2 := m2) z' r hg
      rw [hw]
      field_simp
      field_simp at this
      linarith
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, hsum_w, hcap, Finset.sum_const, nsmul_eq_mul]
    have hcard : (s.card : ℝ) ≤ ((m1 : ℕ) : ℝ) := by
      have : s.card ≤ (m1 : ℕ) := (Finset.card_filter_le _ _).trans (by simp)
      exact_mod_cast this
    have hk2 := P.k2_nonneg
    have : (s.card : ℝ) * (P.k2 / (((m1 : ℕ) : ℝ) * ((m2 : ℕ) : ℝ))) ≤ P.k2 / ((m2 : ℕ) : ℝ) := by
      rw [show P.k2 / ((m2 : ℕ) : ℝ) = ((m1 : ℕ) : ℝ) * (P.k2 / (((m1 : ℕ) : ℝ) * ((m2 : ℕ) : ℝ)))
        by field_simp]
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    rw [hX]
    linarith

  have hne : s.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm1,
    grpSize_pos_zero hm1 hm2⟩⟩
  have hle : ∑ b ∈ s, w b * P.grpCost m1 m2 z' r b ≤ ∑ b ∈ s, w b * X := by
    rw [← Finset.sum_mul, hsum_w, one_mul]; exact hweighted
  obtain ⟨b, hb, hbX⟩ := Finset.exists_le_of_sum_le hne hle
  have hwpos : 0 < w b := by
    rw [hw]; have := (Finset.mem_filter.mp hb).2; positivity
  have hcb : P.grpCost m1 m2 z' r b ≤ X := le_of_mul_le_mul_left hbX hwpos
  exact ⟨((r - (m1 : ℕ)), (r - (m1 : ℕ) + grpEll m1 m2 z' r b), m1,
    Nat.toPNat' (grpSize m1 m2 b)), hcb⟩

lemma exists_capPhi_le_Vjoint {m1 m2 : ℕ} (hm1 : 0 < m1) (hm2 : 0 < m2) (hh1 : 0 < P.h1)
    (hh2 : 0 < P.h2) (hp : 0 < P.p) :
    ∃ r z : ℤ, (∀ n : ℤ, P.psi m1 r ≤ P.psi m1 n) ∧ P.capPhi m1 m2 r z ≤ P.Vjoint m1 m2 := by
  obtain ⟨r, hr⟩ := P.exists_int_min_global hm1 hh1
  obtain ⟨z0, hz0⟩ := P.exists_int_min_capPhi hm1 hm2 hh2 hp r
  refine ⟨r, z0, hr, ?_⟩
  have := P.Vjoint_feasible_nonempty m2
  unfold Vjoint
  refine le_ciInf (fun zx => ?_)
  have h1 := P.capPhi_le_jointObj (Z := ⌈zx.1.1⌉) (fun n _ => hr n) (Int.le_ceil zx.1.1) zx.2
  obtain ⟨z', -, h2⟩ := P.capPhi_ge_int m1 m2 r zx.1.1
  exact (hz0 z').trans (h2.trans h1)

def rBound (m : ℕ) : ℝ :=
  (P.H0 + (P.h1 + P.h2 + P.p) * P.mu1 + (P.h1 + P.h2 + P.p) * m + (P.h1 + P.h2) * (m + P.mu1)) / P.h1
    + (P.H0 + (P.h1 + P.h2 + P.p) * P.mu1 + (P.h1 + P.h2 + P.p) * m) / (P.p + P.h2)

lemma rBound_mono (hh1 : 0 < P.h1) (hp : 0 < P.p) {m n : ℕ} (h : m ≤ n) : P.rBound m ≤ P.rBound n := by
  unfold rBound
  have hmn : (m : ℝ) ≤ n := by exact_mod_cast h
  have hc : 0 ≤ P.h1 + P.h2 + P.p := add_nonneg P.a_nonneg P.p_nonneg
  have ha := P.a_nonneg
  have hph : 0 < P.p + P.h2 := by linarith [P.h2_nonneg]
  have e1 : (P.H0 + (P.h1 + P.h2 + P.p) * P.mu1 + (P.h1 + P.h2 + P.p) * m + (P.h1 + P.h2) * (m + P.mu1))
      ≤ (P.H0 + (P.h1 + P.h2 + P.p) * P.mu1 + (P.h1 + P.h2 + P.p) * n + (P.h1 + P.h2) * (n + P.mu1)) := by
    nlinarith
  have e2 : (P.H0 + (P.h1 + P.h2 + P.p) * P.mu1 + (P.h1 + P.h2 + P.p) * m)
      ≤ (P.H0 + (P.h1 + P.h2 + P.p) * P.mu1 + (P.h1 + P.h2 + P.p) * n) := by nlinarith
  have := div_le_div_of_nonneg_right e1 hh1.le
  have := div_le_div_of_nonneg_right e2 hph.le
  linarith

lemma rBound_nonneg (hh1 : 0 < P.h1) (hp : 0 < P.p) (m : ℕ) : 0 ≤ P.rBound m := by
  unfold rBound
  have hc : 0 ≤ P.h1 + P.h2 + P.p := add_nonneg P.a_nonneg P.p_nonneg
  have := P.H0_nonneg; have := P.mu1_nonneg; have := P.a_nonneg
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hph : 0 < P.p + P.h2 := by linarith [P.h2_nonneg]
  apply add_nonneg <;> apply div_nonneg <;> try positivity
  all_goals nlinarith

lemma abs_r_le {m : ℕ} (hm : 0 < m) (hh1 : 0 < P.h1) (hp : 0 < P.p) {r : ℤ}
    (hr : ∀ n : ℤ, P.psi m r ≤ P.psi m n) : |(r : ℝ)| ≤ P.rBound m := by
  have hc : 0 ≤ P.h1 + P.h2 + P.p := add_nonneg P.a_nonneg P.p_nonneg
  have hph : 0 < P.p + P.h2 := by linarith [P.h2_nonneg]
  have h0 : P.psi m r ≤ P.psi m ((0 : ℤ) : ℝ) := hr 0
  push_cast at h0
  have hpsi0 : P.psi m 0 ≤ P.H0 + (P.h1 + P.h2 + P.p) * P.mu1 + (P.h1 + P.h2 + P.p) * m := by
    unfold psi
    have := P.latAvg_G0_abs_le m 0
    have := le_abs_self (latAvg m P.G0 0)
    simp only [abs_zero, zero_add, mul_zero, sub_zero] at *
    linarith
  have hpsi0' : 0 ≤ P.psi m 0 := by
    unfold psi; simp only [mul_zero, sub_zero]; exact P.latAvg_G0_nonneg m 0
  have hup := P.psi_ge_up hm (r : ℝ)
  have hlo := P.psi_ge hm (r : ℝ)
  have hb := P.rBound_nonneg hh1 hp m
  unfold rBound at hb ⊢
  set D := P.H0 + (P.h1 + P.h2 + P.p) * P.mu1 + (P.h1 + P.h2 + P.p) * m with hD
  have hA : (r : ℝ) ≤ (D + (P.h1 + P.h2) * (m + P.mu1)) / P.h1 := by
    rw [le_div_iff₀ hh1]; nlinarith
  have hB : -(r : ℝ) ≤ D / (P.p + P.h2) := by
    rw [le_div_iff₀ hph]; nlinarith
  have hA0 : 0 ≤ (D + (P.h1 + P.h2) * (m + P.mu1)) / P.h1 := by
    apply div_nonneg _ hh1.le
    have := P.mu1_nonneg; have := P.a_nonneg; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  have hB0 : 0 ≤ D / (P.p + P.h2) := div_nonneg (by linarith) hph.le
  rw [abs_le]
  constructor <;> linarith

theorem formula_attained (hh1 : 0 < P.h1) (hh2 : 0 < P.h2) (hp : 0 < P.p) :
    ∃ c : ℤ × ℤ × ℕ+ × ℕ+, P.classicalFormula c.1 c.2.1 c.2.2.1 c.2.2.2 ≤ P.Jjoint P.k1 P.k2 := by
  set a := min (P.h1 + P.h2) P.p with ha
  set b := min P.h2 P.p with hb
  set K := (P.h1 + P.h2) * P.mu1 with hK
  have ha0 : 0 < a := lt_min (by linarith [P.h1_nonneg]) hp
  have hb0 : 0 < b := lt_min hh2 hp
  have hK0 : 0 ≤ K := mul_nonneg P.a_nonneg P.mu1_nonneg
  have hk1 := P.k1_nonneg
  have hk2 := P.k2_nonneg
  set val : ℕ+ × ℕ+ → ℝ := fun m =>
    P.k1 / ((m.1 : ℕ) : ℝ) + P.k2 / ((m.2 : ℕ) : ℝ) + P.Vjoint m.1 m.2 with hval
  have hVle : ∀ m : ℕ+ × ℕ+, P.Vjoint m.1 m.2 ≤ val m := fun m => by
    simp only [hval]
    have : 0 ≤ P.k1 / ((m.1 : ℕ) : ℝ) := by positivity
    have : 0 ≤ P.k2 / ((m.2 : ℕ) : ℝ) := by positivity
    linarith

  have hV : ∀ m : ℕ+ × ℕ+, a * ((((m.1 : ℕ) : ℝ) - 1) / 4) - K ≤ P.Vjoint m.1 m.2 ∧
      b * ((((m.2 : ℕ) : ℝ) - 1) / 4) - P.h2 * P.rBound m.1 ≤ P.Vjoint m.1 m.2 := by
    intro m
    obtain ⟨r, z, hr, hrz⟩ := P.exists_capPhi_le_Vjoint m.1.pos m.2.pos hh1 hh2 hp
    have h1 := P.capPhi_ge_lower (m1 := m.1) (m2 := m.2) m.1.pos m.2.pos (r : ℝ) (z : ℝ)
    have h2 := P.capPhi_ge_m2 (m1 := m.1) (m2 := m.2) m.1.pos m.2.pos (r : ℝ) (z : ℝ)
    have h3 := P.abs_r_le m.1.pos hh1 hp hr
    have : P.h2 * |(r : ℝ)| ≤ P.h2 * P.rBound m.1 := mul_le_mul_of_nonneg_left h3 hh2.le
    exact ⟨by linarith, by linarith⟩
  have hB0 : 0 ≤ val (1, 1) := by
    have := (hV (1, 1)).1
    have := hVle (1, 1)
    have hv := P.Vjoint_nonneg ((1 : ℕ+) : ℕ) ((1 : ℕ+) : ℕ)
    linarith
  set B := val (1, 1) with hBdef
  set N1 : ℕ := ⌈4 * (B + K) / a + 1⌉₊ with hN1
  set N2 : ℕ := ⌈4 * (B + P.h2 * P.rBound N1) / b + 1⌉₊ with hN2
  set S : Finset (ℕ+ × ℕ+) := (Finset.range (N1 + 1) ×ˢ Finset.range (N2 + 1)).image
    (fun q : ℕ × ℕ => (Nat.toPNat' q.1, Nat.toPNat' q.2)) with hS
  have hmemS : ∀ m : ℕ+ × ℕ+, (m.1 : ℕ) ≤ N1 → (m.2 : ℕ) ≤ N2 → m ∈ S := by
    intro m h1 h2
    refine Finset.mem_image.mpr ⟨((m.1 : ℕ), (m.2 : ℕ)), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, ?_⟩
    simp
  have hN1pos : 1 ≤ N1 := by
    rw [hN1]
    have : (1 : ℝ) ≤ 4 * (B + K) / a + 1 := by
      have : 0 ≤ 4 * (B + K) / a := div_nonneg (by linarith) ha0.le
      linarith
    exact Nat.one_le_iff_ne_zero.mpr (by
      intro h0
      have := Nat.ceil_eq_zero.mp h0
      linarith)
  have hN2pos : 1 ≤ N2 := by
    rw [hN2]
    have hr0 := P.rBound_nonneg hh1 hp N1
    have : (1 : ℝ) ≤ 4 * (B + P.h2 * P.rBound N1) / b + 1 := by
      have : 0 ≤ 4 * (B + P.h2 * P.rBound N1) / b :=
        div_nonneg (by nlinarith [P.h2_nonneg]) hb0.le
      linarith
    exact Nat.one_le_iff_ne_zero.mpr (by
      intro h0
      have := Nat.ceil_eq_zero.mp h0
      linarith)
  have h11 : ((1 : ℕ+), (1 : ℕ+)) ∈ S := hmemS _ (by simpa using hN1pos) (by simpa using hN2pos)
  obtain ⟨m0, _, hmin⟩ := S.exists_min_image val ⟨_, h11⟩
  have hm0B : val m0 ≤ B := hmin _ h11
  have hall : ∀ m : ℕ+ × ℕ+, val m0 ≤ val m := by
    intro m
    by_cases hm : m ∈ S
    · exact hmin m hm
    · by_contra hlt
      push_neg at hlt
      have hVm : P.Vjoint m.1 m.2 < B := lt_of_le_of_lt (hVle m) (lt_of_lt_of_le hlt hm0B)
      obtain ⟨hv1, hv2⟩ := hV m
      have hm1 : (m.1 : ℕ) ≤ N1 := by
        have h1 : (((m.1 : ℕ) : ℝ)) < 4 * (B + K) / a + 1 := by
          have : a * ((((m.1 : ℕ) : ℝ) - 1) / 4) < B + K := by linarith
          have : (((m.1 : ℕ) : ℝ) - 1) < 4 * (B + K) / a := by
            rw [lt_div_iff₀ ha0]; nlinarith
          linarith
        have := Nat.le_ceil (4 * (B + K) / a + 1)
        have h2 : ((m.1 : ℕ) : ℝ) < (N1 : ℝ) := lt_of_lt_of_le h1 this
        exact_mod_cast h2.le
      have hm2 : (m.2 : ℕ) ≤ N2 := by
        have hRB := P.rBound_mono hh1 hp hm1
        have h1 : (((m.2 : ℕ) : ℝ)) < 4 * (B + P.h2 * P.rBound N1) / b + 1 := by
          have : b * ((((m.2 : ℕ) : ℝ) - 1) / 4) < B + P.h2 * P.rBound N1 := by
            have : P.h2 * P.rBound m.1 ≤ P.h2 * P.rBound N1 := mul_le_mul_of_nonneg_left hRB hh2.le
            linarith
          have : (((m.2 : ℕ) : ℝ) - 1) < 4 * (B + P.h2 * P.rBound N1) / b := by
            rw [lt_div_iff₀ hb0]; nlinarith
          linarith
        have := Nat.le_ceil (4 * (B + P.h2 * P.rBound N1) / b + 1)
        have h2 : ((m.2 : ℕ) : ℝ) < (N2 : ℝ) := lt_of_lt_of_le h1 this
        exact_mod_cast h2.le
      exact hm (hmemS m hm1 hm2)
  have hJ : val m0 ≤ P.Jjoint P.k1 P.k2 := by
    unfold Jjoint
    exact le_ciInf hall
  obtain ⟨r, z, -, hrz⟩ := P.exists_capPhi_le_Vjoint m0.1.pos m0.2.pos hh1 hh2 hp
  obtain ⟨c, hc⟩ := P.exists_formula_le_capPhi m0.1 m0.2 z r
  refine ⟨c, ?_⟩
  have : P.k1 / ((m0.1 : ℕ) : ℝ) + P.k2 / ((m0.2 : ℕ) : ℝ) + P.capPhi m0.1 m0.2 r z ≤ val m0 := by
    simp only [hval]; linarith
  linarith

end Params

end TwoStageRnQ

namespace TwoStageRnQ

theorem _root_.solution (P : Params) (hlam : 0 < P.lam) (hh1 : 0 < P.h1) (hh2 : 0 < P.h2)
    (hp : 0 < P.p) (S : DemandSpace P) :
    ∃ c : ClassicalControls, c.1.2.2.2.2 = 0 ∧
      classicalLotCost P S c ≤ ENNReal.ofReal (P.Jjoint P.k1 P.k2) := by
  obtain ⟨c, hc⟩ := P.formula_attained hh1 hh2 hp
  refine ⟨⟨(c.1, c.2.1, c.2.2.1, c.2.2.2, 0), c.2.2.1.pos⟩, rfl, ?_⟩
  rw [(TwoStageRnQ.exact_cost_classical P hlam S c.1 c.2.1 c.2.2.1 c.2.2.2).1]
  exact ENNReal.ofReal_le_ofReal hc

end TwoStageRnQ
