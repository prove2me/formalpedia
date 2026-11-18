-- Prove2me | solution 1 for TwoStageRnQ.Ltwo_le_LBsp
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T00:27:15.092743+00:00
-- url     : https://prove2.me/submissions/23742b55-0586-448c-b016-3a56f7c730fa

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
import Mathlib.Data.Real.Pointwise
import Mathlib.Analysis.Normed.Ring.InfiniteSum

open Finset Filter Topology

noncomputable section

namespace TwoStageRnQ

/-! ## Poisson weights -/

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

/-! ## Expectations of functions with linear growth -/

/-- `f` grows at most linearly. -/
def LinGrowth (f : ℕ → ℝ) : Prop := ∃ A B : ℝ, ∀ n : ℕ, |f n| ≤ A + B * n

lemma LinGrowth.summable {μ : ℝ} (hμ : 0 ≤ μ) {f : ℕ → ℝ} (hf : LinGrowth f) :
    Summable (fun n => poisW μ n * f n) := by
  obtain ⟨A, B, h⟩ := hf
  refine Summable.of_norm_bounded
    (((summable_poisW μ).mul_left A).add ((summable_poisW_mul_nat μ).mul_left B)) (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (poisW_nonneg hμ n)]
  have := mul_le_mul_of_nonneg_left (h n) (poisW_nonneg hμ n)
  linarith [show poisW μ n * (A + B * n) = A * poisW μ n + B * (poisW μ n * n) by ring]

lemma linGrowth_const (c : ℝ) : LinGrowth (fun _ => c) := ⟨|c|, 0, fun n => by simp⟩

lemma linGrowth_nat : LinGrowth (fun n => (n : ℝ)) :=
  ⟨0, 1, fun n => by rw [abs_of_nonneg (Nat.cast_nonneg n)]; simp⟩

lemma LinGrowth.add {f g : ℕ → ℝ} (hf : LinGrowth f) (hg : LinGrowth g) :
    LinGrowth (fun n => f n + g n) := by
  obtain ⟨A, B, hf⟩ := hf; obtain ⟨C, D, hg⟩ := hg
  exact ⟨A + C, B + D, fun n => by
    have := abs_add_le (f n) (g n); have := hf n; have := hg n; nlinarith⟩

lemma LinGrowth.neg {f : ℕ → ℝ} (hf : LinGrowth f) : LinGrowth (fun n => -f n) := by
  obtain ⟨A, B, hf⟩ := hf; exact ⟨A, B, fun n => by rw [abs_neg]; exact hf n⟩

lemma LinGrowth.sub {f g : ℕ → ℝ} (hf : LinGrowth f) (hg : LinGrowth g) :
    LinGrowth (fun n => f n - g n) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

lemma LinGrowth.const_mul {f : ℕ → ℝ} (hf : LinGrowth f) (c : ℝ) :
    LinGrowth (fun n => c * f n) := by
  obtain ⟨A, B, hf⟩ := hf
  refine ⟨|c| * A, |c| * B, fun n => ?_⟩
  rw [abs_mul]
  have := mul_le_mul_of_nonneg_left (hf n) (abs_nonneg c)
  linarith [show |c| * (A + B * n) = |c| * A + |c| * B * n by ring]

lemma LinGrowth.of_le {f g : ℕ → ℝ} (hg : LinGrowth g) (h : ∀ n, |f n| ≤ |g n|) :
    LinGrowth f := by
  obtain ⟨A, B, hg⟩ := hg; exact ⟨A, B, fun n => (h n).trans (hg n)⟩

lemma LinGrowth.sum {ι : Type*} (s : Finset ι) {f : ι → ℕ → ℝ} (hf : ∀ i ∈ s, LinGrowth (f i)) :
    LinGrowth (fun n => ∑ i ∈ s, f i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using linGrowth_const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (mem_insert_self a s)).add (ih (fun i hi => hf i (mem_insert_of_mem hi)))

lemma LinGrowth.div_const {f : ℕ → ℝ} (hf : LinGrowth f) (c : ℝ) :
    LinGrowth (fun n => f n / c) := by
  simpa [div_eq_inv_mul] using hf.const_mul c⁻¹

/-- A function `n ↦ F(y - n)` with `F` Lipschitz-type growth `|F x| ≤ A + B|x|` grows linearly. -/
lemma linGrowth_comp {F : ℝ → ℝ} {A B : ℝ} (hB : 0 ≤ B) (hF : ∀ x, |F x| ≤ A + B * |x|)
    (g : ℕ → ℝ) (hg : LinGrowth g) : LinGrowth (fun n => F (g n)) := by
  obtain ⟨C, D, hg⟩ := hg
  refine ⟨A + B * C, B * D, fun n => ?_⟩
  have := mul_le_mul_of_nonneg_left (hg n) hB
  linarith [hF (g n)]

/-! ## Poisson-integrable functions and the expectation calculus -/

/-- `f` is integrable against the Poisson(`μ`) weights. -/
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

/-- Domination by an affine function of `|g|` and `n`. -/
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

/-! ## The loss `φ` -/

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

/-- Moving left by `δ ≥ 0` raises `φ_{a,b}` by at most `b δ`. -/
lemma phi_left_slope {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {u v : ℝ} (huv : u ≤ v) :
    phi a b u ≤ phi a b v + b * (v - u) := by
  unfold phi
  rcases le_total 0 u with hu | hu <;> rcases le_total 0 v with hv | hv
  · rw [max_eq_left hu, max_eq_left hv, max_eq_right (by linarith : -u ≤ 0),
      max_eq_right (by linarith : -v ≤ 0)]; nlinarith
  · have hu0 : u = 0 := by linarith
    have hv0 : v = 0 := by linarith
    subst hu0; subst hv0; simp
  · rw [max_eq_right hu, max_eq_left hv, max_eq_left (by linarith : 0 ≤ -u),
      max_eq_right (by linarith : -v ≤ 0)]; nlinarith
  · rw [max_eq_right hu, max_eq_right hv, max_eq_left (by linarith : 0 ≤ -u),
      max_eq_left (by linarith : 0 ≤ -v)]; nlinarith

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

/-- Jensen for `φ`: `φ(y - μ) ≤ 𝔼 φ(y - D)`. -/
lemma phi_jensen {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {μ : ℝ} (hμ : 0 ≤ μ) (y : ℝ) :
    phi a b (y - μ) ≤ pexp μ (fun n => phi a b (y - n)) := by
  have hL := (phi_linGrowth ha hb y).pint hμ
  have hlin : PInt μ (fun n : ℕ => y - n) := (pint_const y).sub hμ pint_nat
  have e1 : pexp μ (fun n : ℕ => a * (y - n)) = a * (y - μ) := by
    rw [pexp_const_mul, pexp_sub hμ (pint_const y) pint_nat, pexp_const, pexp_nat]
  have e2 : pexp μ (fun n : ℕ => -(b * (y - n))) = -(b * (y - μ)) := by
    have : (fun n : ℕ => -(b * (y - n))) = fun n : ℕ => (-b) * (y - n) := by ext n; ring
    rw [this, pexp_const_mul, pexp_sub hμ (pint_const y) pint_nat, pexp_const, pexp_nat]
    ring
  rw [phi_eq_max ha hb]
  apply max_le
  · rw [← e1]; exact pexp_mono hμ (hlin.const_mul a) hL (fun n => phi_ge_left ha hb _)
  · rw [← e2]; exact pexp_mono hμ (hlin.const_mul b).neg hL (fun n => phi_ge_right ha hb _)

/-! ## Parameters and the downstream cost -/

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

lemma lossUp_nonneg (x : ℝ) : 0 ≤ P.lossUp x :=
  pexp_nonneg P.mu2_nonneg (fun _ => phi_nonneg P.h2_nonneg P.p_nonneg _)

lemma G0_nonneg (x : ℝ) : 0 ≤ P.G0 x := add_nonneg P.H0_nonneg (P.lossDown_nonneg x)

lemma H0_le_G0 (x : ℝ) : P.H0 ≤ P.G0 x := le_add_of_nonneg_right (P.lossDown_nonneg x)

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

lemma lossDown_left_slope {u v : ℝ} (h : v ≤ u) : P.lossDown v ≤ P.lossDown u + P.p * (u - v) := by
  unfold lossDown
  have hu := (phi_linGrowth P.a_nonneg P.p_nonneg u).pint P.mu1_nonneg
  have hv := (phi_linGrowth P.a_nonneg P.p_nonneg v).pint P.mu1_nonneg
  have key := pexp_mono P.mu1_nonneg hv (hu.add P.mu1_nonneg (pint_const (P.p * (u - v))))
    (fun n => by
      have := phi_left_slope P.a_nonneg P.p_nonneg (show v - n ≤ u - n by linarith)
      linarith)
  rwa [pexp_add P.mu1_nonneg hu (pint_const _), pexp_const] at key

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

lemma G0_left_slope {u v : ℝ} (h : v ≤ u) : P.G0 v ≤ P.G0 u + P.p * (u - v) := by
  unfold G0; linarith [P.lossDown_left_slope h]

lemma G0_convex {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x y : ℝ) :
    P.G0 (θ * x + (1 - θ) * y) ≤ θ * P.G0 x + (1 - θ) * P.G0 y := by
  unfold G0; nlinarith [P.lossDown_convex h0 h1 x y]

lemma G0_abs_le (x : ℝ) : |P.G0 x| ≤ P.H0 + (P.h1 + P.h2 + P.p) * (|x| + P.mu1) := by
  rw [abs_of_nonneg (P.G0_nonneg x)]; unfold G0; linarith [P.lossDown_le x]

end Params

/-! ## Lattice averages -/

lemma latAvg_nonneg {j : ℕ} {F : ℝ → ℝ} (hF : ∀ x, 0 ≤ F x) (x : ℝ) : 0 ≤ latAvg j F x := by
  unfold latAvg; exact div_nonneg (Finset.sum_nonneg (fun v _ => hF _)) (Nat.cast_nonneg j)

lemma latAvg_add_const {j : ℕ} (hj : 0 < j) (F : ℝ → ℝ) (c x : ℝ) :
    latAvg j (fun y => c + F y) x = c + latAvg j F x := by
  unfold latAvg
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : (j : ℝ) ≠ 0 := by positivity
  field_simp

lemma latAvg_mono {j : ℕ} {F G : ℝ → ℝ} (h : ∀ x, F x ≤ G x) (x : ℝ) :
    latAvg j F x ≤ latAvg j G x := by
  unfold latAvg
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun v _ => h _)) (Nat.cast_nonneg j)

/-- Left-slope bound transfers to lattice averages. -/
lemma latAvg_left_slope {j : ℕ} {F : ℝ → ℝ} {b : ℝ}
    (hF : ∀ u v, v ≤ u → F v ≤ F u + b * (u - v)) (hj : 0 < j) {u v : ℝ} (h : v ≤ u) :
    latAvg j F v ≤ latAvg j F u + b * (u - v) := by
  unfold latAvg
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  rw [div_add' _ _ _ hjr.ne', div_le_div_iff_of_pos_right hjr]
  calc ∑ x ∈ range j, F (v - x) ≤ ∑ x ∈ range j, (F (u - x) + b * (u - v)) :=
        Finset.sum_le_sum (fun x _ => by
          have := hF (u - x) (v - x) (by linarith)
          rwa [show u - x - (v - x) = u - v by ring] at this)
    _ = ∑ x ∈ range j, F (u - x) + b * (u - v) * j := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

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

/-- `𝓛_m G₀ = H₀ + 𝓛_m P`. -/
lemma latAvg_G0 {m : ℕ} (hm : 0 < m) (x : ℝ) :
    latAvg m P.G0 x = P.H0 + latAvg m P.lossDown x := by
  have : P.G0 = fun y => P.H0 + P.lossDown y := rfl
  rw [this, latAvg_add_const hm]

lemma latAvg_G0_nonneg (m : ℕ) (x : ℝ) : 0 ≤ latAvg m P.G0 x := latAvg_nonneg P.G0_nonneg x

lemma latAvg_G0_left_slope {m : ℕ} (hm : 0 < m) {u v : ℝ} (h : v ≤ u) :
    latAvg m P.G0 v ≤ latAvg m P.G0 u + P.p * (u - v) :=
  latAvg_left_slope (fun u v h => P.G0_left_slope h) hm h

lemma latAvg_G0_convex (m : ℕ) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x y : ℝ) :
    latAvg m P.G0 (θ * x + (1 - θ) * y) ≤ θ * latAvg m P.G0 x + (1 - θ) * latAvg m P.G0 y :=
  latAvg_convex (fun θ h0 h1 x y => P.G0_convex h0 h1 x y) h0 h1 x y

lemma latAvg_G0_abs_le (m : ℕ) (x : ℝ) :
    |latAvg m P.G0 x| ≤ (P.H0 + (P.h1 + P.h2 + P.p) * P.mu1) + (P.h1 + P.h2 + P.p) * (|x| + m) := by
  have hc : 0 ≤ P.h1 + P.h2 + P.p := add_nonneg P.a_nonneg P.p_nonneg
  have := latAvg_abs_le (j := m) (F := P.G0) (A := P.H0 + (P.h1 + P.h2 + P.p) * P.mu1) hc
    (fun x => by have := P.G0_abs_le x; linarith) x
  linarith

lemma G0_sub_abs_le (v c : ℝ) :
    |P.G0 (v - c)| ≤ (P.H0 + (P.h1 + P.h2 + P.p) * (P.mu1 + |c|)) + (P.h1 + P.h2 + P.p) * |v| := by
  have hc : 0 ≤ P.h1 + P.h2 + P.p := add_nonneg P.a_nonneg P.p_nonneg
  have := P.G0_abs_le (v - c)
  have : |v - c| ≤ |v| + |c| := abs_sub _ _
  nlinarith

/-- A decision process integrable against `D₂` keeps `𝓛_m G₀` integrable. -/
lemma pint_latAvg_G0 (m : ℕ) {f : ℕ → ℝ} (hf : PInt P.mu2 f) :
    PInt P.mu2 (fun n => latAvg m P.G0 (f n)) := by
  refine PInt.of_affine P.mu2_nonneg hf (A := (P.H0 + (P.h1 + P.h2 + P.p) * P.mu1)
    + (P.h1 + P.h2 + P.p) * m) (B := P.h1 + P.h2 + P.p) (C := 0) (fun n => ?_)
  have := P.latAvg_G0_abs_le m (f n); linarith

lemma lossUp_eq (x : ℝ) : P.lossUp x = pexp P.mu2 (fun d => phi P.h2 P.p (x - d)) := rfl

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

lemma Vjoint_bddBelow (m1 m2 : ℕ) :
    BddBelow (Set.range fun zx : {zx : ℝ × (ℕ → Fin m2 → ℝ) // P.JointFeasible m2 zx.1 zx.2} =>
      P.jointObj m1 m2 zx.1.1 zx.1.2) :=
  ⟨0, by rintro _ ⟨zx, rfl⟩; exact P.jointObj_nonneg zx.2⟩

lemma Vjoint_nonneg (m1 m2 : ℕ) : 0 ≤ P.Vjoint m1 m2 :=
  Real.iInf_nonneg (fun zx => P.jointObj_nonneg zx.2)

lemma Vjoint_le {m1 m2 : ℕ} {z : ℝ} {x : ℕ → Fin m2 → ℝ} (hx : P.JointFeasible m2 z x) :
    P.Vjoint m1 m2 ≤ P.jointObj m1 m2 z x :=
  ciInf_le (P.Vjoint_bddBelow m1 m2) ⟨(z, x), hx⟩

end Params

/-- The capped choice `min s Y` costs at most the separate stage costs (pointwise form of the
stagewise bound). -/
lemma cap_bound {Gm : ℝ → ℝ} {p h2 : ℝ} (hp : 0 ≤ p) (hh : 0 ≤ h2)
    (hG : ∀ u v, v ≤ u → Gm v ≤ Gm u + p * (u - v)) (s Y : ℝ) :
    Gm (min s Y) + h2 * (Y - min s Y) ≤ Gm s + phi h2 p (Y - s) := by
  unfold phi
  rcases le_total s Y with h | h
  · rw [min_eq_left h, max_eq_left (by linarith : (0 : ℝ) ≤ Y - s),
      max_eq_right (by linarith : -(Y - s) ≤ 0)]
    linarith
  · rw [min_eq_right h, max_eq_right (by linarith : Y - s ≤ 0),
      max_eq_left (by linarith : (0 : ℝ) ≤ -(Y - s))]
    have := hG s Y h
    nlinarith

lemma abs_min_le_add (a b : ℝ) : |min a b| ≤ |a| + |b| :=
  (abs_min_le_max_abs_abs).trans (max_le (by linarith [abs_nonneg b]) (by linarith [abs_nonneg a]))

lemma abs_sub_nat_le (z : ℝ) (d : ℕ) (c : ℝ) : |z - d - c| ≤ |z| + |c| + d := by
  have h1 := abs_sub (z - d) c
  have h2 := abs_sub_nat z d
  linarith

namespace Params

variable (P : Params)

/-- Stagewise bound for fixed placements `s, y`. -/
lemma Vjoint_le_stagewise {m1 m2 : ℕ} (hm1 : 0 < m1) (hm2 : 0 < m2) (s y : ℝ) :
    P.Vjoint m1 m2 ≤ P.H0 + latAvg m1 P.lossDown s + latAvg m2 P.lossUp y := by
  have hμ := P.mu2_nonneg
  set z := s + y with hz
  set x : ℕ → Fin m2 → ℝ := fun d j => min s (z - d - ((j : ℕ) : ℝ)) with hxdef
  have hxint : ∀ j : Fin m2, PInt P.mu2 (fun d => x d j) := fun j =>
    PInt.of_affine hμ (pint_const 0) (A := |s| + |z| + |((j : ℕ) : ℝ)|) (B := 0) (C := 1)
      (fun d => by
        have := abs_min_le_add s (z - d - ((j : ℕ) : ℝ))
        have := abs_sub_nat_le z d ((j : ℕ) : ℝ)
        simp only [hxdef]; nlinarith)
  have hfeas : P.JointFeasible m2 z x := ⟨fun d j => min_le_right _ _, fun j => hxint j⟩
  refine (P.Vjoint_le (m1 := m1) hfeas).trans ?_
  unfold jointObj
  have hm2r : (0 : ℝ) < m2 := by exact_mod_cast hm2
  -- integrability of the two integrands
  have hL : PInt P.mu2 (fun d : ℕ => (∑ j : Fin m2, (latAvg m1 P.G0 (x d j)
      + P.h2 * (z - d - ((j : ℕ) : ℝ) - x d j))) / m2) := by
    refine PInt.div_const (PInt.sum hμ _ (fun j _ => ?_)) _
    refine (P.pint_latAvg_G0 m1 (hxint j)).add hμ ?_
    exact ((((pint_const z).sub hμ pint_nat).sub hμ (pint_const _)).sub hμ (hxint j)).const_mul _
  have hphi : ∀ j : Fin m2,
      PInt P.mu2 (fun d : ℕ => phi P.h2 P.p ((y - ((j : ℕ) : ℝ)) - d)) := fun j =>
    (phi_linGrowth P.h2_nonneg P.p_nonneg _).pint hμ
  have hR : PInt P.mu2 (fun d : ℕ => latAvg m1 P.G0 s
      + (∑ j : Fin m2, phi P.h2 P.p ((y - ((j : ℕ) : ℝ)) - d)) / m2) :=
    (pint_const _).add hμ (PInt.div_const (PInt.sum hμ _ (fun j _ => hphi j)) _)
  calc pexp P.mu2 (fun d : ℕ => (∑ j : Fin m2, (latAvg m1 P.G0 (x d j)
          + P.h2 * (z - d - ((j : ℕ) : ℝ) - x d j))) / m2)
        ≤ pexp P.mu2 (fun d : ℕ => latAvg m1 P.G0 s
          + (∑ j : Fin m2, phi P.h2 P.p ((y - ((j : ℕ) : ℝ)) - d)) / m2) := by
        refine pexp_mono hμ hL hR (fun d => ?_)
        rw [div_le_iff₀ hm2r, add_mul, div_mul_cancel₀ _ hm2r.ne']
        have hc : latAvg m1 P.G0 s * m2 = ∑ _j : Fin m2, latAvg m1 P.G0 s := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
        rw [hc, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum (fun j _ => ?_)
        have := cap_bound P.p_nonneg P.h2_nonneg
          (fun u v h => P.latAvg_G0_left_slope hm1 h) s (z - d - ((j : ℕ) : ℝ))
        have harg : z - d - ((j : ℕ) : ℝ) - s = (y - ((j : ℕ) : ℝ)) - d := by rw [hz]; ring
        rw [harg] at this
        simpa [hxdef] using this
    _ = latAvg m1 P.G0 s + (∑ j : Fin m2, P.lossUp (y - ((j : ℕ) : ℝ))) / m2 := by
        rw [pexp_add hμ (pint_const _) (PInt.div_const (PInt.sum hμ _ (fun j _ => hphi j)) _),
          pexp_const, pexp_div_const, pexp_finset_sum hμ _ (fun j _ => hphi j)]
        rfl
    _ = P.H0 + latAvg m1 P.lossDown s + latAvg m2 P.lossUp y := by
        rw [P.latAvg_G0 hm1]
        unfold latAvg
        rw [Fin.sum_univ_eq_sum_range (fun j => P.lossUp (y - (j : ℝ))) m2]

lemma Vjoint_feasible_nonempty (m2 : ℕ) :
    Nonempty {zx : ℝ × (ℕ → Fin m2 → ℝ) // P.JointFeasible m2 zx.1 zx.2} :=
  ⟨⟨(0, fun d j => -(d : ℝ) - ((j : ℕ) : ℝ)), fun d j => by simp,
    fun j => ((pint_nat.neg).sub P.mu2_nonneg (pint_const _))⟩⟩

lemma latInf_bddBelow {j : ℕ} {F : ℝ → ℝ} (hF : ∀ x, 0 ≤ F x) :
    BddBelow (Set.range fun x => latAvg j F x) :=
  ⟨0, by rintro _ ⟨x, rfl⟩; exact latAvg_nonneg hF x⟩

lemma latInf_nonneg {j : ℕ} {F : ℝ → ℝ} (hF : ∀ x, 0 ≤ F x) : 0 ≤ latInf j F :=
  Real.iInf_nonneg (fun x => latAvg_nonneg hF x)

lemma Vjoint_le_latInf {m1 m2 : ℕ} (hm1 : 0 < m1) (hm2 : 0 < m2) :
    P.Vjoint m1 m2 ≤ P.H0 + latInf m1 P.lossDown + latInf m2 P.lossUp := by
  have h1 : ∀ s y : ℝ, P.Vjoint m1 m2 - P.H0 - latAvg m2 P.lossUp y ≤ latAvg m1 P.lossDown s :=
    fun s y => by linarith [P.Vjoint_le_stagewise hm1 hm2 s y]
  have h2 : ∀ y : ℝ, P.Vjoint m1 m2 - P.H0 - latInf m1 P.lossDown ≤ latAvg m2 P.lossUp y := by
    intro y
    have : P.Vjoint m1 m2 - P.H0 - latAvg m2 P.lossUp y ≤ latInf m1 P.lossDown :=
      le_ciInf (fun s => h1 s y)
    linarith
  have : P.Vjoint m1 m2 - P.H0 - latInf m1 P.lossDown ≤ latInf m2 P.lossUp := le_ciInf h2
  linarith

lemma cycCost_bddBelow {F : ℝ → ℝ} (hF : ∀ x, 0 ≤ F x) {k : ℝ} (hk : 0 ≤ k) :
    BddBelow (Set.range fun j : ℕ+ => k / ((j : ℕ) : ℝ) + latInf j F) :=
  ⟨0, by rintro _ ⟨j, rfl⟩; exact add_nonneg (div_nonneg hk (Nat.cast_nonneg _)) (latInf_nonneg hF)⟩

lemma Jjoint_bddBelow {c1 c2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) :
    BddBelow (Set.range fun m : ℕ+ × ℕ+ =>
      c1 / ((m.1 : ℕ) : ℝ) + c2 / ((m.2 : ℕ) : ℝ) + P.Vjoint m.1 m.2) :=
  ⟨0, by
    rintro _ ⟨m, rfl⟩
    exact add_nonneg (add_nonneg (div_nonneg hc1 (Nat.cast_nonneg _))
      (div_nonneg hc2 (Nat.cast_nonneg _))) (P.Vjoint_nonneg _ _)⟩

lemma Jjoint_le {c1 c2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (m1 m2 : ℕ+) :
    P.Jjoint c1 c2 ≤ c1 / ((m1 : ℕ) : ℝ) + c2 / ((m2 : ℕ) : ℝ) + P.Vjoint m1 m2 :=
  ciInf_le (P.Jjoint_bddBelow hc1 hc2) (m1, m2)

lemma Jjoint_le_B {c1 c2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) :
    P.Jjoint c1 c2 ≤ P.B1 c1 + P.B2 c2 := by
  have h0 : ∀ m1 m2 : ℕ+, P.Jjoint c1 c2 ≤ P.H0 + (c1 / ((m1 : ℕ) : ℝ) + latInf m1 P.lossDown)
      + (c2 / ((m2 : ℕ) : ℝ) + latInf m2 P.lossUp) := fun m1 m2 => by
    have := P.Jjoint_le hc1 hc2 m1 m2
    have := P.Vjoint_le_latInf (m1 := m1) (m2 := m2) m1.pos m2.pos
    linarith
  have h1 : ∀ m2 : ℕ+, P.Jjoint c1 c2 - P.H0 - (c2 / ((m2 : ℕ) : ℝ) + latInf m2 P.lossUp)
      ≤ cycCost P.lossDown c1 := fun m2 =>
    le_ciInf (fun m1 => by linarith [h0 m1 m2])
  have h2 : P.Jjoint c1 c2 - P.H0 - cycCost P.lossDown c1 ≤ cycCost P.lossUp c2 :=
    le_ciInf (fun m2 => by linarith [h1 m2])
  unfold B1 B2
  linarith

end Params

theorem stagewise_upper_bound_pf (P : Params) :
    (∀ m1 m2 : ℕ+, P.Vjoint m1 m2 ≤ P.H0 + latInf m1 P.lossDown + latInf m2 P.lossUp) ∧
    ∀ c1 c2 : ℝ, 0 ≤ c1 → 0 ≤ c2 → P.Jjoint c1 c2 ≤ P.B1 c1 + P.B2 c2 :=
  ⟨fun m1 m2 => P.Vjoint_le_latInf m1.pos m2.pos, fun _ _ hc1 hc2 => P.Jjoint_le_B hc1 hc2⟩

end TwoStageRnQ

open Finset Filter Topology

noncomputable section

namespace TwoStageRnQ

/-! ## Single-stage cycle costs: monotonicity, scaling, shifts -/

lemma latInf_mono {j : ℕ} {F G : ℝ → ℝ} (hF : ∀ x, 0 ≤ F x) (h : ∀ x, F x ≤ G x) :
    latInf j F ≤ latInf j G :=
  ciInf_mono (Params.latInf_bddBelow hF) (fun x => latAvg_mono h x)

lemma cycCost_mono {F G : ℝ → ℝ} (hF : ∀ x, 0 ≤ F x) (h : ∀ x, F x ≤ G x) {k : ℝ} (hk : 0 ≤ k) :
    cycCost F k ≤ cycCost G k :=
  ciInf_mono (Params.cycCost_bddBelow hF hk) (fun j => by linarith [latInf_mono (j := j) hF h])

lemma latInf_half {j : ℕ} (F : ℝ → ℝ) : latInf j (fun x => (1 / 2) * F x) = (1 / 2) * latInf j F := by
  unfold latInf
  rw [Real.mul_iInf_of_nonneg (by norm_num)]
  congr 1; funext x
  unfold latAvg; rw [← Finset.mul_sum]; ring

lemma cycCost_half (F : ℝ → ℝ) (k : ℝ) :
    cycCost (fun x => (1 / 2) * F x) k = (1 / 2) * cycCost F (2 * k) := by
  unfold cycCost
  rw [Real.mul_iInf_of_nonneg (by norm_num)]
  congr 1; funext j
  rw [latInf_half]; ring

lemma latInf_shift {j : ℕ} (F : ℝ → ℝ) (a : ℝ) : latInf j (fun x => F (x - a)) = latInf j F := by
  unfold latInf
  have : (fun x : ℝ => latAvg j (fun y => F (y - a)) x) = fun x => latAvg j F ((Equiv.subRight a) x) := by
    funext x; unfold latAvg; congr 1; refine Finset.sum_congr rfl (fun v _ => ?_)
    simp only [Equiv.subRight_apply]; ring_nf
  rw [this, Equiv.iInf_comp (g := fun y => latAvg j F y)]

lemma cycCost_shift (F : ℝ → ℝ) (a k : ℝ) : cycCost (fun x => F (x - a)) k = cycCost F k := by
  unfold cycCost; simp_rw [latInf_shift]

namespace Params

variable (P : Params)

/-! ## Equal allocation (eq. (D.19)) -/

lemma allocF1_half_ge (x : ℝ) : (1 / 2) * P.lossDown x ≤ P.allocF1 (1 / 2) (1 / 2) x := by
  have hμ := P.mu1_nonneg
  have hpos1 : 0 ≤ P.h1 + 1 / 2 * P.h2 := by have := P.h1_nonneg; have := P.h2_nonneg; positivity
  have hpos2 : 0 ≤ 1 / 2 * P.p := by have := P.p_nonneg; positivity
  unfold lossDown allocF1
  rw [← pexp_const_mul]
  refine pexp_mono hμ (((phi_linGrowth P.a_nonneg P.p_nonneg x).pint hμ).const_mul _)
    ((phi_linGrowth hpos1 hpos2 x).pint hμ) (fun d => ?_)
  unfold phi
  have := P.h1_nonneg; have := P.h2_nonneg; have := P.p_nonneg
  have h1 := le_max_right (x - d) 0
  have h2 := le_max_right (-(x - d)) 0
  nlinarith

lemma summable_double (x : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Summable (Function.uncurry fun (d1 d2 : ℕ) =>
      poisW P.mu1 d1 * (poisW P.mu2 d2 * phi a b (x - d1 - d2))) := by
  have h1 := summable_poisW P.mu1
  have h2 := summable_poisW P.mu2
  have h1n := summable_poisW_mul_nat P.mu1
  have h2n := summable_poisW_mul_nat P.mu2
  have w1 := poisW_nonneg P.mu1_nonneg
  have w2 := poisW_nonneg P.mu2_nonneg
  have hA := Summable.mul_of_nonneg h1 h2 w1 w2
  have hB := Summable.mul_of_nonneg h1n h2 (fun n => mul_nonneg (w1 n) (Nat.cast_nonneg n)) w2
  have hC := Summable.mul_of_nonneg h1 h2n w1 (fun n => mul_nonneg (w2 n) (Nat.cast_nonneg n))
  have hS := ((hA.mul_left ((a + b) * |x|)).add (hB.mul_left (a + b))).add (hC.mul_left (a + b))
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hS
  · obtain ⟨d1, d2⟩ := p
    exact mul_nonneg (w1 _) (mul_nonneg (w2 _) (phi_nonneg ha hb _))
  · obtain ⟨d1, d2⟩ := p
    show poisW P.mu1 d1 * (poisW P.mu2 d2 * phi a b (x - d1 - d2))
      ≤ (a + b) * |x| * (poisW P.mu1 d1 * poisW P.mu2 d2)
        + (a + b) * (poisW P.mu1 d1 * d1 * poisW P.mu2 d2)
        + (a + b) * (poisW P.mu1 d1 * (poisW P.mu2 d2 * d2))
    have hφ := phi_abs_le ha hb (x - d1 - d2)
    have habs : |x - d1 - d2| ≤ |x| + d1 + d2 := by
      have := abs_sub_nat (x - d1) d2; have := abs_sub_nat x d1; linarith
    have hφ' : phi a b (x - d1 - d2) ≤ (a + b) * (|x| + d1 + d2) :=
      (le_abs_self _).trans (hφ.trans (mul_le_mul_of_nonneg_left habs (add_nonneg ha hb)))
    have hw : 0 ≤ poisW P.mu1 d1 * poisW P.mu2 d2 := mul_nonneg (w1 d1) (w2 d2)
    have := mul_le_mul_of_nonneg_left hφ' hw
    have e : poisW P.mu1 d1 * (poisW P.mu2 d2 * phi a b (x - d1 - d2))
        = poisW P.mu1 d1 * poisW P.mu2 d2 * phi a b (x - d1 - d2) := by ring
    rw [e]
    refine this.trans (le_of_eq ?_)
    ring

lemma allocF2_half_ge (x : ℝ) :
    (1 / 2) * P.lossUp (x - P.mu1) ≤ P.allocF2 (1 / 2) (1 / 2) x := by
  have hμ1 := P.mu1_nonneg
  have hμ2 := P.mu2_nonneg
  set a' : ℝ := (1 - 1 / 2) * P.h2 with ha'
  set b' : ℝ := (1 - 1 / 2) * P.p with hb'
  have ha : 0 ≤ a' := by have := P.h2_nonneg; rw [ha']; positivity
  have hb : 0 ≤ b' := by have := P.p_nonneg; rw [hb']; positivity
  have hin : ∀ d2 : ℕ, poisW P.mu2 d2 * phi a' b' (x - P.mu1 - d2)
      ≤ ∑' d1 : ℕ, poisW P.mu1 d1 * (poisW P.mu2 d2 * phi a' b' (x - d1 - d2)) := by
    intro d2
    have e1 : (fun d1 : ℕ => poisW P.mu1 d1 * (poisW P.mu2 d2 * phi a' b' (x - d1 - d2)))
        = fun d1 : ℕ => poisW P.mu2 d2 * (poisW P.mu1 d1 * phi a' b' ((x - d2) - d1)) := by
      funext d1; rw [show x - (d1 : ℝ) - d2 = (x - d2) - d1 by ring]; ring
    rw [e1, tsum_mul_left]
    refine mul_le_mul_of_nonneg_left ?_ (poisW_nonneg hμ2 d2)
    have := phi_jensen ha hb hμ1 (x - d2)
    rw [show x - P.mu1 - d2 = (x - d2) - P.mu1 by ring]
    exact this
  have hsd := P.summable_double x ha hb
  unfold allocF2 pexp
  have e2 : (fun d1 : ℕ => poisW P.mu1 d1 * ∑' d2 : ℕ, poisW P.mu2 d2 * phi a' b' (x - d1 - d2))
      = fun d1 : ℕ => ∑' d2 : ℕ, poisW P.mu1 d1 * (poisW P.mu2 d2 * phi a' b' (x - d1 - d2)) := by
    funext d1; rw [tsum_mul_left]
  rw [e2, ← hsd.tsum_comm]
  unfold lossUp pexp
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun d2 => ?_) ?_ hsd.prod_symm.prod
  · have := hin d2
    have e : phi a' b' (x - P.mu1 - d2) = (1 / 2) * phi P.h2 P.p (x - P.mu1 - d2) := by
      rw [ha', hb']; unfold phi; ring
    rw [e] at this
    linarith
  · exact ((((phi_linGrowth P.h2_nonneg P.p_nonneg (x - P.mu1)).pint hμ2).summable hμ2).mul_left _)

lemma cycCost_le_zero {F : ℝ → ℝ} (hF : ∀ x, 0 ≤ F x) {k : ℝ} (hk : 0 ≤ k) :
    cycCost F k ≤ k + F 0 := by
  have h1 : cycCost F k ≤ k / ((1 : ℕ+) : ℕ) + latInf ((1 : ℕ+) : ℕ) F :=
    ciInf_le (Params.cycCost_bddBelow hF hk) 1
  have h2 : latInf 1 F ≤ latAvg 1 F 0 := ciInf_le (Params.latInf_bddBelow hF) 0
  have h3 : latAvg 1 F 0 = F 0 := by unfold latAvg; simp
  simp at h1
  linarith

lemma allocF1_nonneg {η ζ : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (hζ : ζ ∈ Set.Icc (0 : ℝ) 1) (x : ℝ) :
    0 ≤ P.allocF1 η ζ x := by
  have := P.h1_nonneg; have := P.h2_nonneg; have := P.p_nonneg
  exact pexp_nonneg P.mu1_nonneg (fun d => phi_nonneg (by nlinarith [hη.1]) (by nlinarith [hζ.1]) _)

lemma allocF2_nonneg {η ζ : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (hζ : ζ ∈ Set.Icc (0 : ℝ) 1) (x : ℝ) :
    0 ≤ P.allocF2 η ζ x := by
  have := P.h2_nonneg; have := P.p_nonneg
  have ha : 0 ≤ (1 - η) * P.h2 := mul_nonneg (by linarith [hη.2]) P.h2_nonneg
  have hb : 0 ≤ (1 - ζ) * P.p := mul_nonneg (by linarith [hζ.2]) P.p_nonneg
  exact pexp_nonneg P.mu1_nonneg (fun d1 => pexp_nonneg P.mu2_nonneg (fun d2 => phi_nonneg ha hb _))

lemma allocF1_zero_le {η ζ : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (hζ : ζ ∈ Set.Icc (0 : ℝ) 1) :
    P.allocF1 η ζ 0 ≤ 2 * (P.h1 + P.h2 + P.p) * P.mu1 := by
  have hμ := P.mu1_nonneg
  have := P.h1_nonneg; have := P.h2_nonneg; have := P.p_nonneg
  have ha : 0 ≤ P.h1 + η * P.h2 := by nlinarith [hη.1]
  have hb : 0 ≤ ζ * P.p := by nlinarith [hζ.1]
  unfold allocF1
  have hbound : PInt P.mu1 (fun d : ℕ => 2 * (P.h1 + P.h2 + P.p) * (d : ℝ)) := pint_nat.const_mul _
  refine (pexp_mono hμ ((phi_linGrowth ha hb 0).pint hμ) hbound (fun d => ?_)).trans
    (le_of_eq (by rw [pexp_const_mul, pexp_nat]))
  refine (le_abs_self _).trans ((phi_abs_le ha hb _).trans ?_)
  rw [zero_sub, abs_neg, abs_of_nonneg (Nat.cast_nonneg d)]
  have hd := Nat.cast_nonneg (α := ℝ) d
  have : P.h1 + η * P.h2 + ζ * P.p ≤ 2 * (P.h1 + P.h2 + P.p) := by nlinarith [hη.2, hζ.2]
  nlinarith

lemma allocF2_zero_le {η ζ : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (hζ : ζ ∈ Set.Icc (0 : ℝ) 1) :
    P.allocF2 η ζ 0 ≤ 2 * (P.h1 + P.h2 + P.p) * (P.mu1 + P.mu2) := by
  have hμ1 := P.mu1_nonneg; have hμ2 := P.mu2_nonneg
  have := P.h1_nonneg; have := P.h2_nonneg; have := P.p_nonneg
  have ha : 0 ≤ (1 - η) * P.h2 := mul_nonneg (by linarith [hη.2]) P.h2_nonneg
  have hb : 0 ≤ (1 - ζ) * P.p := mul_nonneg (by linarith [hζ.2]) P.p_nonneg
  set C := 2 * (P.h1 + P.h2 + P.p) with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have hcoef : (1 - η) * P.h2 + (1 - ζ) * P.p ≤ C := by
    rw [hC]; nlinarith [hη.1, hζ.1]
  have inner : ∀ d1 : ℕ, pexp P.mu2 (fun d2 : ℕ => phi ((1 - η) * P.h2) ((1 - ζ) * P.p)
      ((0 : ℝ) - d1 - d2)) ≤ C * ((d1 : ℝ) + P.mu2) := by
    intro d1
    have hb2 : PInt P.mu2 (fun d2 : ℕ => C * ((d1 : ℝ) + d2)) :=
      ((pint_const _).add hμ2 pint_nat).const_mul _
    refine (pexp_mono hμ2 ((phi_linGrowth ha hb _).pint hμ2) hb2 (fun d2 => ?_)).trans
      (le_of_eq (by rw [pexp_const_mul, pexp_add hμ2 (pint_const _) pint_nat, pexp_const, pexp_nat]))
    refine (le_abs_self _).trans ((phi_abs_le ha hb _).trans ?_)
    have hd1 := Nat.cast_nonneg (α := ℝ) d1; have hd2 := Nat.cast_nonneg (α := ℝ) d2
    rw [show (0 : ℝ) - d1 - d2 = -((d1 : ℝ) + d2) by ring, abs_neg, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right hcoef (by positivity)
  unfold allocF2
  have hb1 : PInt P.mu1 (fun d1 : ℕ => C * ((d1 : ℝ) + P.mu2)) :=
    (pint_nat.add hμ1 (pint_const _)).const_mul _
  have hinner_int : PInt P.mu1 (fun d1 : ℕ => pexp P.mu2 (fun d2 : ℕ =>
      phi ((1 - η) * P.h2) ((1 - ζ) * P.p) ((0 : ℝ) - d1 - d2))) := by
    refine PInt.of_abs_le hμ1 hb1 (fun d1 => ?_)
    rw [abs_of_nonneg (pexp_nonneg hμ2 (fun _ => phi_nonneg ha hb _))]
    exact inner d1
  refine (pexp_mono hμ1 hinner_int hb1 inner).trans (le_of_eq ?_)
  rw [pexp_const_mul, pexp_add hμ1 pint_nat (pint_const _), pexp_nat, pexp_const]

lemma allocBound_term_le {c1 c2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (q : {q : ℝ × ℝ // q.1 ∈ Set.Icc (0 : ℝ) 1 ∧ q.2 ∈ Set.Icc (0 : ℝ) 1}) :
    q.1.1 * P.H0 + cycCost (P.allocF1 q.1.1 q.1.2) c1 + cycCost (P.allocF2 q.1.1 q.1.2) c2
      ≤ P.H0 + c1 + c2 + 4 * (P.h1 + P.h2 + P.p) * (P.mu1 + P.mu2) := by
  have h1 := cycCost_le_zero (P.allocF1_nonneg q.2.1 q.2.2) hc1
  have h2 := cycCost_le_zero (P.allocF2_nonneg q.2.1 q.2.2) hc2
  have h3 := P.allocF1_zero_le q.2.1 q.2.2
  have h4 := P.allocF2_zero_le q.2.1 q.2.2
  have h5 : q.1.1 * P.H0 ≤ P.H0 := by
    have := P.H0_nonneg; nlinarith [q.2.1.2]
  have := P.mu2_nonneg; have := P.mu1_nonneg
  have := P.h1_nonneg; have := P.h2_nonneg; have := P.p_nonneg
  nlinarith

lemma alloc_family_bddAbove {c1 c2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) :
    BddAbove (Set.range fun q : {q : ℝ × ℝ // q.1 ∈ Set.Icc (0 : ℝ) 1 ∧ q.2 ∈ Set.Icc (0 : ℝ) 1} =>
      (q.1.1 * P.H0 + cycCost (P.allocF1 q.1.1 q.1.2) c1 + cycCost (P.allocF2 q.1.1 q.1.2) c2)) :=
  ⟨_, by rintro _ ⟨q, rfl⟩; exact P.allocBound_term_le hc1 hc2 q⟩

lemma allocBound_le {c1 c2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) :
    P.allocBound c1 c2 ≤ P.H0 + c1 + c2 + 4 * (P.h1 + P.h2 + P.p) * (P.mu1 + P.mu2) := by
  haveI : Nonempty {q : ℝ × ℝ // q.1 ∈ Set.Icc (0 : ℝ) 1 ∧ q.2 ∈ Set.Icc (0 : ℝ) 1} :=
    ⟨⟨(0, 0), ⟨le_refl 0, zero_le_one⟩, ⟨le_refl 0, zero_le_one⟩⟩⟩
  exact ciSup_le (fun q => P.allocBound_term_le hc1 hc2 q)

end Params

theorem equal_allocation_pf (P : Params) (c1 c2 : ℝ) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) :
    (P.B1 (2 * c1) + P.B2 (2 * c2)) / 2 ≤ P.allocBound c1 c2 := by
  have hq : ((1 / 2 : ℝ), (1 / 2 : ℝ)).1 ∈ Set.Icc (0 : ℝ) 1 ∧
      ((1 / 2 : ℝ), (1 / 2 : ℝ)).2 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> constructor <;> norm_num
  have hle := le_ciSup (P.alloc_family_bddAbove hc1 hc2) ⟨((1 / 2 : ℝ), (1 / 2 : ℝ)), hq⟩
  simp only at hle
  have h1 : (1 / 2) * cycCost P.lossDown (2 * c1) ≤ cycCost (P.allocF1 (1 / 2) (1 / 2)) c1 := by
    rw [← cycCost_half]
    exact cycCost_mono (fun x => by have := P.lossDown_nonneg x; positivity)
      (fun x => P.allocF1_half_ge x) hc1
  have h2 : (1 / 2) * cycCost P.lossUp (2 * c2) ≤ cycCost (P.allocF2 (1 / 2) (1 / 2)) c2 := by
    rw [← cycCost_shift P.lossUp P.mu1, ← cycCost_half]
    exact cycCost_mono (fun x => by have := P.lossUp_nonneg (x - P.mu1); positivity)
      (fun x => P.allocF2_half_ge x) hc2
  unfold Params.B1 Params.B2
  unfold Params.allocBound
  linarith

theorem Ltwo_le_LBsp_pf (P : Params) : P.Ltwo ≤ P.LBsp := by
  have hk1 := P.k1_nonneg
  have hk2 := P.k2_nonneg
  have hV0 : 0 ≤ P.V0 := Real.iInf_nonneg (fun ry => pexp_nonneg P.mu2_nonneg (fun d =>
    add_nonneg (P.G0_nonneg _) (mul_nonneg P.h2_nonneg (le_max_right _ _))))
  have hbdd : BddAbove (Set.range fun u : Set.Ioc (0 : ℝ) 1 =>
      ((1 - (u : ℝ)) * P.V0 + (u : ℝ) * P.allocBound (P.k1 / u) (P.k2 / u))) := by
    refine ⟨P.V0 + (P.H0 + P.k1 + P.k2 + 4 * (P.h1 + P.h2 + P.p) * (P.mu1 + P.mu2)), ?_⟩
    rintro _ ⟨u, rfl⟩
    have hu0 : 0 < (u : ℝ) := u.2.1
    have hu1 : (u : ℝ) ≤ 1 := u.2.2
    have hb := P.allocBound_le (div_nonneg hk1 hu0.le) (div_nonneg hk2 hu0.le)
    have hcst : 0 ≤ P.H0 + 4 * (P.h1 + P.h2 + P.p) * (P.mu1 + P.mu2) := by
      have := P.H0_nonneg; have := P.mu1_nonneg; have := P.mu2_nonneg
      have := P.h1_nonneg; have := P.h2_nonneg; have := P.p_nonneg; positivity
    have e1 : (u : ℝ) * (P.k1 / u) = P.k1 := by field_simp
    have e2 : (u : ℝ) * (P.k2 / u) = P.k2 := by field_simp
    have := mul_le_mul_of_nonneg_left hb hu0.le
    simp only
    nlinarith
  have hu1 : (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := ⟨one_pos, le_refl 1⟩
  have hu2 : (1 / 2 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have l1 := le_ciSup hbdd ⟨1, hu1⟩
  have l2 := le_ciSup hbdd ⟨1 / 2, hu2⟩
  simp only at l1 l2
  rw [div_one, div_one] at l1
  rw [show P.k1 / (1 / 2) = 2 * P.k1 by field_simp, show P.k2 / (1 / 2) = 2 * P.k2 by field_simp]
    at l2
  have a1 := equal_allocation_pf P P.k1 P.k2 hk1 hk2
  have a2 := equal_allocation_pf P (2 * P.k1) (2 * P.k2) (by positivity) (by positivity)
  rw [show 2 * (2 * P.k1) = 4 * P.k1 by ring, show 2 * (2 * P.k2) = 4 * P.k2 by ring] at a2
  unfold Params.Ltwo Params.LBsp
  apply max_le <;> linarith

end TwoStageRnQ

open TwoStageRnQ

theorem solution (P : Params) :
    P.Ltwo ≤ P.LBsp :=
  TwoStageRnQ.Ltwo_le_LBsp_pf P
