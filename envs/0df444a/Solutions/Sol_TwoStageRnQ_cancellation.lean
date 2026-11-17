-- Prove2me | solution 1 for TwoStageRnQ.cancellation
-- status  : ACCEPTED   (prove)
-- author  : @beatlesmania
-- created : 2026-11-17T00:27:12.295062+00:00
-- url     : https://prove2.me/submissions/c50901d5-ba0f-4773-ad8f-e421443e6ba3

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

/-! ## Even and odd positions -/

lemma sum_range_even_odd (f : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ range m, f i = ∑ i ∈ range ((m + 1) / 2), f (2 * i) + ∑ i ∈ range (m / 2), f (2 * i + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
    · have e1 : (2 * k + 1) / 2 = k := by omega
      have e2 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
      have e3 : 2 * k / 2 = k := by omega
      rw [e1, e2, e3, Finset.sum_range_succ]; ring
    · have e1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
      have e2 : (2 * k + 1 + 1 + 1) / 2 = k + 1 := by omega
      have e3 : (2 * k + 1) / 2 = k := by omega
      rw [e1, e2, e3, Finset.sum_range_succ (fun i => f (2 * i + 1))]; ring

/-- Number of positions of parity `a ∈ {0,1}` in `{0,…,m-1}`. -/
def parCount (m a : ℕ) : ℕ := if a = 0 then (m + 1) / 2 else m / 2

lemma parCount_add (m : ℕ) : parCount m 0 + parCount m 1 = m := by
  simp [parCount]; omega

lemma two_mul_add_lt {m a i : ℕ} (ha : a < 2) (hi : i < parCount m a) : 2 * i + a < m := by
  unfold parCount at hi
  split_ifs at hi with h <;> omega

/-- Averages over `{0,…,m-1}` split into the even and odd positions, weighted by their shares. -/
lemma avg_even_odd (f : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ range m, f i) / m
      = ∑ a ∈ range 2, ((parCount m a : ℝ) / m) *
          ((∑ i ∈ range (parCount m a), f (2 * i + a)) / (parCount m a : ℝ)) := by
  rw [sum_range_even_odd f m]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, parCount]
  simp only [if_true, one_ne_zero, if_false, add_zero]
  have key : ∀ (S : ℕ) (A : ℝ), (S = 0 → A = 0) → ((S : ℝ) / m) * (A / S) = A / m := by
    intro S A hA
    rcases Nat.eq_zero_or_pos S with h | h
    · simp [h, hA h]
    · have : (S : ℝ) ≠ 0 := by positivity
      field_simp
  rw [key _ _ (fun h => by simp [h]), key _ _ (fun h => by simp [h]), add_div]

/-- Even positions `2j'` of `{0,…,m-1}`. -/
def evIdx {m : ℕ} (j : Fin ((m + 1) / 2)) : Fin m := ⟨2 * (j : ℕ), by omega⟩

/-- Odd positions `2j'+1` of `{0,…,m-1}`. -/
def odIdx {m : ℕ} (j : Fin (m / 2)) : Fin m := ⟨2 * (j : ℕ) + 1, by omega⟩

lemma evIdx_val {m : ℕ} (j : Fin ((m + 1) / 2)) : (((evIdx j : Fin m) : ℕ) : ℝ) = 2 * ((j : ℕ) : ℝ) + 0 := by
  simp [evIdx]

lemma odIdx_val {m : ℕ} (j : Fin (m / 2)) : (((odIdx j : Fin m) : ℕ) : ℝ) = 2 * ((j : ℕ) : ℝ) + 1 := by
  simp [odIdx]

lemma card_even_odd (m : ℕ) : (((m + 1) / 2 : ℕ) : ℝ) + ((m / 2 : ℕ) : ℝ) = m := by
  have : (m + 1) / 2 + m / 2 = m := by omega
  exact_mod_cast this

/-- Averages over `Fin m` split into the even and odd positions, weighted by their shares. -/
lemma avg_fin_even_odd {m : ℕ} (F : Fin m → ℝ) :
    (∑ j, F j) / m
      = ((((m + 1) / 2 : ℕ) : ℝ) / m) * ((∑ j, F (evIdx j)) / (((m + 1) / 2 : ℕ) : ℝ))
        + (((m / 2 : ℕ) : ℝ) / m) * ((∑ j, F (odIdx j)) / ((m / 2 : ℕ) : ℝ)) := by
  set F' : ℕ → ℝ := fun n => if h : n < m then F ⟨n, h⟩ else 0 with hF'
  have h0 : ∑ j, F j = ∑ i ∈ range m, F' i := by
    rw [← Fin.sum_univ_eq_sum_range F' m]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [hF', j.isLt]
  have hE : ∑ j : Fin ((m + 1) / 2), F (evIdx j) = ∑ i ∈ range ((m + 1) / 2), F' (2 * i) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => F' (2 * i)) ((m + 1) / 2)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have : 2 * (j : ℕ) < m := by have := j.isLt; omega
    simp [hF', this, evIdx]
  have hO : ∑ j : Fin (m / 2), F (odIdx j) = ∑ i ∈ range (m / 2), F' (2 * i + 1) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => F' (2 * i + 1)) (m / 2)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have : 2 * (j : ℕ) + 1 < m := by have := j.isLt; omega
    simp [hF', this, odIdx]
  rw [h0, hE, hO, sum_range_even_odd F' m]
  have key : ∀ (S : ℕ) (A : ℝ), (S = 0 → A = 0) → ((S : ℝ) / m) * (A / S) = A / m := by
    intro S A hA
    rcases Nat.eq_zero_or_pos S with h | h
    · simp [h, hA h]
    · have : (S : ℝ) ≠ 0 := by positivity
      field_simp
  rw [key _ _ (fun h => by simp [h]), key _ _ (fun h => by simp [h]), add_div]

lemma share_mul_div_le {S m : ℕ} (hm : 0 < m) {c : ℝ} (hc : 0 ≤ c) :
    ((S : ℝ) / m) * (c / S) ≤ c / m := by
  rcases Nat.eq_zero_or_pos S with h | h
  · simp [h]; positivity
  · have : (S : ℝ) ≠ 0 := by positivity
    have : ((S : ℝ) / m) * (c / S) = c / m := by field_simp
    rw [this]

namespace Params

variable (P : Params)

/-- Generalized joint objective: uniform cycle positions with values `ξ₁ : Fin m₁ → ℝ`
(downstream) and `ξ₂ : Fin m₂ → ℝ` (upstream). -/
def gInt (m1 m2 : ℕ) (ξ1 : Fin m1 → ℝ) (ξ2 : Fin m2 → ℝ) (z : ℝ) (x : ℕ → Fin m2 → ℝ)
    (d : ℕ) : ℝ :=
  (∑ j : Fin m2, ((∑ i : Fin m1, P.G0 (x d j - ξ1 i)) / m1
      + P.h2 * (z - d - ξ2 j - x d j))) / m2

def gObj (m1 m2 : ℕ) (ξ1 : Fin m1 → ℝ) (ξ2 : Fin m2 → ℝ) (z : ℝ) (x : ℕ → Fin m2 → ℝ) : ℝ :=
  pexp P.mu2 (P.gInt m1 m2 ξ1 ξ2 z x)

def gFeas {m2 : ℕ} (ξ2 : Fin m2 → ℝ) (z : ℝ) (x : ℕ → Fin m2 → ℝ) : Prop :=
  (∀ d j, x d j ≤ z - d - ξ2 j) ∧ ∀ j, PInt P.mu2 (fun d => x d j)

lemma pint_gInt {m1 m2 : ℕ} (ξ1 : Fin m1 → ℝ) (ξ2 : Fin m2 → ℝ) (z : ℝ) {x : ℕ → Fin m2 → ℝ}
    (hx : ∀ j, PInt P.mu2 (fun d => x d j)) : PInt P.mu2 (P.gInt m1 m2 ξ1 ξ2 z x) := by
  have hμ := P.mu2_nonneg
  unfold gInt
  refine PInt.div_const (PInt.sum hμ _ (fun j _ => ?_)) _
  refine (PInt.div_const (PInt.sum hμ _ (fun i _ => ?_)) _).add hμ ?_
  · exact PInt.of_affine hμ (hx j) (A := P.H0 + (P.h1 + P.h2 + P.p) * (P.mu1 + |ξ1 i|))
      (B := P.h1 + P.h2 + P.p) (C := 0) (fun d => by
        have := P.G0_sub_abs_le (x d j) (ξ1 i); linarith)
  · exact ((((pint_const z).sub hμ pint_nat).sub hμ (pint_const _)).sub hμ (hx j)).const_mul _

lemma gObj_nonneg {m1 m2 : ℕ} {ξ1 : Fin m1 → ℝ} {ξ2 : Fin m2 → ℝ} {z : ℝ}
    {x : ℕ → Fin m2 → ℝ} (hx : P.gFeas ξ2 z x) : 0 ≤ P.gObj m1 m2 ξ1 ξ2 z x := by
  unfold gObj gInt
  refine pexp_nonneg P.mu2_nonneg (fun d => div_nonneg (Finset.sum_nonneg (fun j _ => ?_))
    (Nat.cast_nonneg _))
  have := hx.1 d j
  exact add_nonneg (div_nonneg (Finset.sum_nonneg (fun i _ => P.G0_nonneg _)) (Nat.cast_nonneg _))
    (mul_nonneg P.h2_nonneg (by linarith))

lemma jointObj_eq_gObj (m1 m2 : ℕ) (z : ℝ) (x : ℕ → Fin m2 → ℝ) :
    P.jointObj m1 m2 z x
      = P.gObj m1 m2 (fun i => ((i : ℕ) : ℝ)) (fun j => ((j : ℕ) : ℝ)) z x := by
  unfold jointObj gObj gInt latAvg
  refine pexp_congr (fun d => ?_)
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  congr 2
  exact (Fin.sum_univ_eq_sum_range (fun i => P.G0 (x d j - i)) m1).symm

lemma jointFeasible_iff (m2 : ℕ) (z : ℝ) (x : ℕ → Fin m2 → ℝ) :
    P.JointFeasible m2 z x ↔ P.gFeas (fun j => ((j : ℕ) : ℝ)) z x := Iff.rfl

/-- Midpoint convexity across the scales `0, 1, 2` (Lemma D.1, eq. (D.6), with the parity
offsets removed by shifting). -/
lemma two_scale {S1 S2 : ℕ} (hS1 : 0 < S1) (hS2 : 0 < S2) (c1 c2 : ℝ) {z : ℝ}
    {x : ℕ → Fin S2 → ℝ} (hx : P.gFeas (fun j => 2 * ((j : ℕ) : ℝ) + c2) z x) :
    2 * P.Vjoint S1 S2 - P.V0
      ≤ P.gObj S1 S2 (fun i => 2 * ((i : ℕ) : ℝ) + c1) (fun j => 2 * ((j : ℕ) : ℝ) + c2) z x := by
  have hμ := P.mu2_nonneg
  set obj2 := P.gObj S1 S2 (fun i => 2 * ((i : ℕ) : ℝ) + c1) (fun j => 2 * ((j : ℕ) : ℝ) + c2) z x
  suffices h : ∀ ry : ℝ × ℝ, 2 * P.Vjoint S1 S2 - obj2 ≤ pexp P.mu2 (fun d =>
      P.G0 (ry.1 - max (-(ry.2 - (d : ℝ))) 0) + P.h2 * max (ry.2 - (d : ℝ)) 0) by
    have := le_ciInf h
    unfold V0
    linarith
  rintro ⟨r, y⟩
  -- the zero-scale decision
  set x0 : ℕ → ℝ := fun d => min r (r + y - d) with hx0
  have hx0eq : ∀ d : ℕ, r - max (-(y - (d : ℝ))) 0 = x0 d := by
    intro d; simp only [hx0]
    rcases le_total (y - (d : ℝ)) 0 with h | h
    · rw [max_eq_left (by linarith), min_eq_right (by linarith)]; ring
    · rw [max_eq_right (by linarith), min_eq_left (by linarith)]; ring
  have hx0pos : ∀ d : ℕ, max (y - (d : ℝ)) 0 = r + y - d - x0 d := by
    intro d; simp only [hx0]
    rcases le_total (y - (d : ℝ)) 0 with h | h
    · rw [max_eq_right h, min_eq_right (by linarith)]; ring
    · rw [max_eq_left h, min_eq_left (by linarith)]; ring
  have hx0int : PInt P.mu2 x0 := PInt.of_affine hμ (pint_const 0) (A := |r| + |r + y|) (B := 0)
    (C := 1) (fun d => by
      have := abs_min_le_add r (r + y - d)
      have := abs_sub_nat_le (r + y) d 0
      simp only [hx0]; simp at this; nlinarith [abs_nonneg (r + y - (d : ℝ))])
  -- the midpoint decision at scale one
  set z1 := ((z - c1 - c2) + (r + y)) / 2 with hz1
  set x1 : ℕ → Fin S2 → ℝ := fun d j => ((x d j - c1) + x0 d) / 2 with hx1
  have hx1int : ∀ j, PInt P.mu2 (fun d => x1 d j) := fun j =>
    (((hx.2 j).sub hμ (pint_const c1)).add hμ hx0int).div_const 2
  have hfeas1 : P.JointFeasible S2 z1 x1 := by
    refine ⟨fun d j => ?_, hx1int⟩
    have h1 := hx.1 d j
    have h2 : x0 d ≤ r + y - d := min_le_right _ _
    simp only [hx1, hz1]
    linarith
  have hV := P.Vjoint_le (m1 := S1) hfeas1
  rw [P.jointObj_eq_gObj] at hV
  set g0 : ℕ → ℝ := fun d => P.G0 (x0 d) + P.h2 * (r + y - d - x0 d) with hg0
  have hg0int : PInt P.mu2 g0 :=
    (PInt.of_affine hμ hx0int (A := P.H0 + (P.h1 + P.h2 + P.p) * P.mu1)
        (B := P.h1 + P.h2 + P.p) (C := 0) (fun d => by
          have := P.G0_abs_le (x0 d); linarith)).add hμ
      ((((pint_const (r + y)).sub hμ pint_nat).sub hμ hx0int).const_mul _)
  have hS1r : (0 : ℝ) < S1 := by exact_mod_cast hS1
  have hS2r : (0 : ℝ) < S2 := by exact_mod_cast hS2
  have hpt : ∀ d : ℕ, P.gInt S1 S2 (fun i => ((i : ℕ) : ℝ)) (fun j => ((j : ℕ) : ℝ)) z1 x1 d
      ≤ (1 / 2) * P.gInt S1 S2 (fun i => 2 * ((i : ℕ) : ℝ) + c1)
          (fun j => 2 * ((j : ℕ) : ℝ) + c2) z x d + (1 / 2) * g0 d := by
    intro d
    have hj : ∀ j : Fin S2,
        (∑ i : Fin S1, P.G0 (x1 d j - ((i : ℕ) : ℝ))) / S1
            + P.h2 * (z1 - d - ((j : ℕ) : ℝ) - x1 d j)
          ≤ (1 / 2) * ((∑ i : Fin S1, P.G0 (x d j - (2 * ((i : ℕ) : ℝ) + c1))) / S1
              + P.h2 * (z - d - (2 * ((j : ℕ) : ℝ) + c2) - x d j)) + (1 / 2) * g0 d := by
      intro j
      have hi : ∀ i : Fin S1, P.G0 (x1 d j - ((i : ℕ) : ℝ))
          ≤ (1 / 2) * P.G0 (x d j - (2 * ((i : ℕ) : ℝ) + c1)) + (1 - 1 / 2) * P.G0 (x0 d) := by
        intro i
        have := P.G0_convex (θ := 1 / 2) (by norm_num) (by norm_num)
          (x d j - (2 * ((i : ℕ) : ℝ) + c1)) (x0 d)
        convert this using 2
        simp only [hx1]; ring
      have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin S1))) => hi i)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul] at hsum
      have h1 : (∑ i : Fin S1, P.G0 (x1 d j - ((i : ℕ) : ℝ))) / S1
          ≤ (1 / 2) * ((∑ i : Fin S1, P.G0 (x d j - (2 * ((i : ℕ) : ℝ) + c1))) / S1)
            + (1 / 2) * P.G0 (x0 d) := by
        rw [div_le_iff₀ hS1r]
        refine hsum.trans (le_of_eq ?_)
        field_simp
        ring
      have h2 : P.h2 * (z1 - d - ((j : ℕ) : ℝ) - x1 d j)
          = (1 / 2) * (P.h2 * (z - d - (2 * ((j : ℕ) : ℝ) + c2) - x d j))
            + (1 / 2) * (P.h2 * (r + y - d - x0 d)) := by
        simp only [hz1, hx1]; ring
      simp only [hg0]
      linarith
    unfold gInt
    rw [div_le_iff₀ hS2r]
    have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin S2))) => hj j)
    refine hs.trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
    try ring
  have hint1 := P.pint_gInt (fun i : Fin S1 => ((i : ℕ) : ℝ)) (fun j : Fin S2 => ((j : ℕ) : ℝ)) z1 hx1int
  have hint2 := P.pint_gInt (fun i : Fin S1 => 2 * ((i : ℕ) : ℝ) + c1)
    (fun j : Fin S2 => 2 * ((j : ℕ) : ℝ) + c2) z hx.2
  have hmono := pexp_mono hμ hint1 ((hint2.const_mul (1 / 2)).add hμ (hg0int.const_mul (1 / 2))) hpt
  rw [pexp_add hμ (hint2.const_mul (1 / 2)) (hg0int.const_mul (1 / 2)), pexp_const_mul,
    pexp_const_mul] at hmono
  have hV0 : pexp P.mu2 (fun d => P.G0 ((r, y).1 - max (-((r, y).2 - (d : ℝ))) 0)
      + P.h2 * max ((r, y).2 - (d : ℝ)) 0) = pexp P.mu2 g0 :=
    pexp_congr (fun d => by simp only [hg0]; rw [hx0eq d, hx0pos d])
  rw [hV0]
  have hobj2 : obj2 = pexp P.mu2 (P.gInt S1 S2 (fun i => 2 * ((i : ℕ) : ℝ) + c1)
      (fun j => 2 * ((j : ℕ) : ℝ) + c2) z x) := rfl
  unfold gObj at hV
  linarith

/-- Restriction of a decision to the even positions. -/
def evDec {m2 : ℕ} (x : ℕ → Fin m2 → ℝ) : ℕ → Fin ((m2 + 1) / 2) → ℝ := fun d j => x d (evIdx j)

/-- Restriction of a decision to the odd positions. -/
def odDec {m2 : ℕ} (x : ℕ → Fin m2 → ℝ) : ℕ → Fin (m2 / 2) → ℝ := fun d j => x d (odIdx j)

/-- Conditioning on the even/odd labels of both cycle positions (eq. (D.22)). -/
lemma gInt_split (m1 m2 : ℕ) (hm1 : 0 < m1) (z : ℝ) (x : ℕ → Fin m2 → ℝ) (d : ℕ) :
    P.gInt m1 m2 (fun i => ((i : ℕ) : ℝ)) (fun j => ((j : ℕ) : ℝ)) z x d
      = ((((m1 + 1) / 2 : ℕ) : ℝ) / m1) * ((((m2 + 1) / 2 : ℕ) : ℝ) / m2) *
          P.gInt ((m1 + 1) / 2) ((m2 + 1) / 2) (fun i => 2 * ((i : ℕ) : ℝ) + 0)
            (fun j => 2 * ((j : ℕ) : ℝ) + 0) z (evDec x) d
        + ((((m1 + 1) / 2 : ℕ) : ℝ) / m1) * (((m2 / 2 : ℕ) : ℝ) / m2) *
          P.gInt ((m1 + 1) / 2) (m2 / 2) (fun i => 2 * ((i : ℕ) : ℝ) + 0)
            (fun j => 2 * ((j : ℕ) : ℝ) + 1) z (odDec x) d
        + (((m1 / 2 : ℕ) : ℝ) / m1) * ((((m2 + 1) / 2 : ℕ) : ℝ) / m2) *
          P.gInt (m1 / 2) ((m2 + 1) / 2) (fun i => 2 * ((i : ℕ) : ℝ) + 1)
            (fun j => 2 * ((j : ℕ) : ℝ) + 0) z (evDec x) d
        + (((m1 / 2 : ℕ) : ℝ) / m1) * (((m2 / 2 : ℕ) : ℝ) / m2) *
          P.gInt (m1 / 2) (m2 / 2) (fun i => 2 * ((i : ℕ) : ℝ) + 1)
            (fun j => 2 * ((j : ℕ) : ℝ) + 1) z (odDec x) d := by
  have hm1r : (m1 : ℝ) ≠ 0 := by positivity
  have hw : ((((m1 + 1) / 2 : ℕ) : ℝ)) / m1 + (((m1 / 2 : ℕ) : ℝ)) / m1 = 1 := by
    rw [← add_div, card_even_odd m1, div_self hm1r]
  have hrow : ∀ (v T : ℝ), (∑ i : Fin m1, P.G0 (v - ((i : ℕ) : ℝ))) / m1 + T
      = ((((m1 + 1) / 2 : ℕ) : ℝ) / m1) * ((∑ i : Fin ((m1 + 1) / 2),
            P.G0 (v - (2 * ((i : ℕ) : ℝ) + 0))) / (((m1 + 1) / 2 : ℕ) : ℝ) + T)
        + (((m1 / 2 : ℕ) : ℝ) / m1) * ((∑ i : Fin (m1 / 2),
            P.G0 (v - (2 * ((i : ℕ) : ℝ) + 1))) / ((m1 / 2 : ℕ) : ℝ) + T) := by
    intro v T
    rw [avg_fin_even_odd (fun i : Fin m1 => P.G0 (v - ((i : ℕ) : ℝ)))]
    simp only [evIdx_val, odIdx_val]
    linear_combination (-T) * hw
  unfold gInt
  rw [avg_fin_even_odd]
  simp only [evDec, odDec, evIdx_val, odIdx_val]
  have hblk : ∀ (k : ℕ) (J : Fin k → Fin m2) (o : Fin k → ℝ),
      ∑ j : Fin k, ((∑ i : Fin m1, P.G0 (x d (J j) - ((i : ℕ) : ℝ))) / m1
          + P.h2 * (z - d - o j - x d (J j)))
        = ((((m1 + 1) / 2 : ℕ) : ℝ) / m1) * ∑ j : Fin k, ((∑ i : Fin ((m1 + 1) / 2),
              P.G0 (x d (J j) - (2 * ((i : ℕ) : ℝ) + 0))) / (((m1 + 1) / 2 : ℕ) : ℝ)
              + P.h2 * (z - d - o j - x d (J j)))
          + (((m1 / 2 : ℕ) : ℝ) / m1) * ∑ j : Fin k, ((∑ i : Fin (m1 / 2),
              P.G0 (x d (J j) - (2 * ((i : ℕ) : ℝ) + 1))) / ((m1 / 2 : ℕ) : ℝ)
              + P.h2 * (z - d - o j - x d (J j))) := by
    intro k J o
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => hrow _ _)
  rw [hblk ((m2 + 1) / 2) evIdx (fun j => 2 * ((j : ℕ) : ℝ) + 0),
    hblk (m2 / 2) odIdx (fun j => 2 * ((j : ℕ) : ℝ) + 1)]
  ring

lemma gFeas_ev {m2 : ℕ} {z : ℝ} {x : ℕ → Fin m2 → ℝ} (hx : P.JointFeasible m2 z x) :
    P.gFeas (fun j : Fin ((m2 + 1) / 2) => 2 * ((j : ℕ) : ℝ) + 0) z (evDec x) :=
  ⟨fun d j => by have := hx.1 d (evIdx j); rw [evIdx_val] at this; exact this,
    fun j => hx.2 (evIdx j)⟩

lemma gFeas_od {m2 : ℕ} {z : ℝ} {x : ℕ → Fin m2 → ℝ} (hx : P.JointFeasible m2 z x) :
    P.gFeas (fun j : Fin (m2 / 2) => 2 * ((j : ℕ) : ℝ) + 1) z (odDec x) :=
  ⟨fun d j => by have := hx.1 d (odIdx j); rw [odIdx_val] at this; exact this,
    fun j => hx.2 (odIdx j)⟩

lemma block_bound {S1 S2 m1 m2 : ℕ} {c1 c2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (o1 o2 : ℝ) {z : ℝ} {x : ℕ → Fin S2 → ℝ} (hx : P.gFeas (fun j => 2 * ((j : ℕ) : ℝ) + o2) z x) :
    ((S1 : ℝ) / m1) * ((S2 : ℝ) / m2) * (2 * P.Jjoint c1 c2 - P.V0)
        - 2 * ((S2 : ℝ) / m2) * (((S1 : ℝ) / m1) * (c1 / S1))
        - 2 * ((S1 : ℝ) / m1) * (((S2 : ℝ) / m2) * (c2 / S2))
      ≤ ((S1 : ℝ) / m1) * ((S2 : ℝ) / m2) *
        P.gObj S1 S2 (fun i => 2 * ((i : ℕ) : ℝ) + o1) (fun j => 2 * ((j : ℕ) : ℝ) + o2) z x := by
  rcases Nat.eq_zero_or_pos S1 with h1 | h1
  · simp [h1]
  rcases Nat.eq_zero_or_pos S2 with h2 | h2
  · simp [h2]
  have hJ := P.Jjoint_le hc1 hc2 ⟨S1, h1⟩ ⟨S2, h2⟩
  have hts := P.two_scale h1 h2 o1 o2 hx
  simp only [PNat.mk_coe] at hJ
  have hw : 0 ≤ ((S1 : ℝ) / m1) * ((S2 : ℝ) / m2) := by positivity
  have key : 2 * P.Jjoint c1 c2 - P.V0 - 2 * (c1 / S1) - 2 * (c2 / S2)
      ≤ P.gObj S1 S2 (fun i => 2 * ((i : ℕ) : ℝ) + o1) (fun j => 2 * ((j : ℕ) : ℝ) + o2) z x := by
    linarith
  have := mul_le_mul_of_nonneg_left key hw
  linarith [this]

lemma doubling_candidate {c1 c2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (m1 m2 : ℕ+) :
    2 * P.Jjoint c1 c2 - P.V0 ≤ 4 * c1 / ((m1 : ℕ) : ℝ) + 4 * c2 / ((m2 : ℕ) : ℝ) + P.Vjoint m1 m2 := by
  have hm1 := m1.pos
  have hm2 := m2.pos
  have hμ := P.mu2_nonneg
  haveI := P.Vjoint_feasible_nonempty m2
  suffices h : ∀ zx : {zx : ℝ × (ℕ → Fin m2 → ℝ) // P.JointFeasible m2 zx.1 zx.2},
      2 * P.Jjoint c1 c2 - P.V0 - 4 * c1 / ((m1 : ℕ) : ℝ) - 4 * c2 / ((m2 : ℕ) : ℝ)
        ≤ P.jointObj m1 m2 zx.1.1 zx.1.2 by
    have := le_ciInf h
    unfold Vjoint
    linarith
  rintro ⟨⟨z, x⟩, hx⟩
  simp only
  rw [P.jointObj_eq_gObj]
  unfold gObj
  rw [pexp_congr (P.gInt_split m1 m2 hm1 z x)]
  have i1 := P.pint_gInt (fun i : Fin ((m1 + 1) / 2) => 2 * ((i : ℕ) : ℝ) + 0)
    (fun j : Fin ((m2 + 1) / 2) => 2 * ((j : ℕ) : ℝ) + 0) z (P.gFeas_ev hx).2
  have i2 := P.pint_gInt (fun i : Fin ((m1 + 1) / 2) => 2 * ((i : ℕ) : ℝ) + 0)
    (fun j : Fin (m2 / 2) => 2 * ((j : ℕ) : ℝ) + 1) z (P.gFeas_od hx).2
  have i3 := P.pint_gInt (fun i : Fin (m1 / 2) => 2 * ((i : ℕ) : ℝ) + 1)
    (fun j : Fin ((m2 + 1) / 2) => 2 * ((j : ℕ) : ℝ) + 0) z (P.gFeas_ev hx).2
  have i4 := P.pint_gInt (fun i : Fin (m1 / 2) => 2 * ((i : ℕ) : ℝ) + 1)
    (fun j : Fin (m2 / 2) => 2 * ((j : ℕ) : ℝ) + 1) z (P.gFeas_od hx).2
  rw [pexp_add hμ (((i1.const_mul _).add hμ (i2.const_mul _)).add hμ (i3.const_mul _))
      (i4.const_mul _),
    pexp_add hμ ((i1.const_mul _).add hμ (i2.const_mul _)) (i3.const_mul _),
    pexp_add hμ (i1.const_mul _) (i2.const_mul _),
    pexp_const_mul, pexp_const_mul, pexp_const_mul, pexp_const_mul]
  have b1 := P.block_bound (S1 := (m1 + 1) / 2) (m1 := m1) (m2 := m2) hc1 hc2 0 0 (P.gFeas_ev hx)
  have b2 := P.block_bound (S1 := (m1 + 1) / 2) (m1 := m1) (m2 := m2) hc1 hc2 0 1 (P.gFeas_od hx)
  have b3 := P.block_bound (S1 := m1 / 2) (m1 := m1) (m2 := m2) hc1 hc2 1 0 (P.gFeas_ev hx)
  have b4 := P.block_bound (S1 := m1 / 2) (m1 := m1) (m2 := m2) hc1 hc2 1 1 (P.gFeas_od hx)
  unfold gObj at b1 b2 b3 b4
  have s1 := share_mul_div_le (S := (m1 + 1) / 2) hm1 hc1
  have s2 := share_mul_div_le (S := m1 / 2) hm1 hc1
  have s3 := share_mul_div_le (S := (m2 + 1) / 2) hm2 hc2
  have s4 := share_mul_div_le (S := m2 / 2) hm2 hc2
  have hm1r : ((m1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hm2r : ((m2 : ℕ) : ℝ) ≠ 0 := by positivity
  have ha : (((m1 + 1) / 2 : ℕ) : ℝ) / m1 + ((m1 / 2 : ℕ) : ℝ) / m1 = 1 := by
    rw [← add_div, card_even_odd, div_self hm1r]
  have hb : (((m2 + 1) / 2 : ℕ) : ℝ) / m2 + ((m2 / 2 : ℕ) : ℝ) / m2 = 1 := by
    rw [← add_div, card_even_odd, div_self hm2r]
  set a0 : ℝ := (((m1 + 1) / 2 : ℕ) : ℝ) / m1 with ha0
  set a1 : ℝ := ((m1 / 2 : ℕ) : ℝ) / m1 with ha1
  set b0 : ℝ := (((m2 + 1) / 2 : ℕ) : ℝ) / m2 with hb0
  set b1' : ℝ := ((m2 / 2 : ℕ) : ℝ) / m2 with hb1
  set u0 : ℝ := a0 * (c1 / (((m1 + 1) / 2 : ℕ) : ℝ)) with hu0
  set u1 : ℝ := a1 * (c1 / ((m1 / 2 : ℕ) : ℝ)) with hu1
  set v0 : ℝ := b0 * (c2 / (((m2 + 1) / 2 : ℕ) : ℝ)) with hv0
  set v1 : ℝ := b1' * (c2 / ((m2 / 2 : ℕ) : ℝ)) with hv1
  set W := 2 * P.Jjoint c1 c2 - P.V0 with hW
  have eJ : a0 * b0 * W + a0 * b1' * W + a1 * b0 * W + a1 * b1' * W = W := by
    have : a0 * b0 * W + a0 * b1' * W + a1 * b0 * W + a1 * b1' * W = (a0 + a1) * (b0 + b1') * W := by
      ring
    rw [this, ha, hb]; ring
  have eu0 : b0 * u0 + b1' * u0 = u0 := by rw [← add_mul, hb, one_mul]
  have eu1 : b0 * u1 + b1' * u1 = u1 := by rw [← add_mul, hb, one_mul]
  have ev0 : a0 * v0 + a1 * v0 = v0 := by rw [← add_mul, ha, one_mul]
  have ev1 : a0 * v1 + a1 * v1 = v1 := by rw [← add_mul, ha, one_mul]
  have e4c1 : 4 * c1 / ((m1 : ℕ) : ℝ) = 2 * (c1 / ((m1 : ℕ) : ℝ)) + 2 * (c1 / ((m1 : ℕ) : ℝ)) := by ring
  have e4c2 : 4 * c2 / ((m2 : ℕ) : ℝ) = 2 * (c2 / ((m2 : ℕ) : ℝ)) + 2 * (c2 / ((m2 : ℕ) : ℝ)) := by ring
  rw [e4c1, e4c2]
  linarith [b1, b2, b3, b4, s1, s2, s3, s4, eJ, eu0, eu1, ev0, ev1]

lemma Jjoint_concave {c1 c2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) :
    2 / 3 * P.Jjoint c1 c2 + 1 / 3 * P.Jjoint (4 * c1) (4 * c2) ≤ P.Jjoint (2 * c1) (2 * c2) := by
  have h4c1 : 0 ≤ 4 * c1 := by linarith
  have h4c2 : 0 ≤ 4 * c2 := by linarith
  refine le_ciInf (fun m => ?_)
  have := P.Jjoint_le hc1 hc2 m.1 m.2
  have := P.Jjoint_le h4c1 h4c2 m.1 m.2
  have e : 2 * c1 / ((m.1 : ℕ) : ℝ) + 2 * c2 / ((m.2 : ℕ) : ℝ) + P.Vjoint m.1 m.2
      = 2 / 3 * (c1 / ((m.1 : ℕ) : ℝ) + c2 / ((m.2 : ℕ) : ℝ) + P.Vjoint m.1 m.2)
        + 1 / 3 * (4 * c1 / ((m.1 : ℕ) : ℝ) + 4 * c2 / ((m.2 : ℕ) : ℝ) + P.Vjoint m.1 m.2) := by
    ring
  rw [e]
  linarith

end Params

end TwoStageRnQ

namespace TwoStageRnQ

theorem joint_doubling_pf (P : Params) (c1 c2 : ℝ) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) :
    2 * P.Jjoint c1 c2 - P.V0 ≤ P.Jjoint (4 * c1) (4 * c2) ∧
      4 / 3 * P.Jjoint c1 c2 - P.V0 / 3 ≤ P.Jjoint (2 * c1) (2 * c2) := by
  have h4 : 2 * P.Jjoint c1 c2 - P.V0 ≤ P.Jjoint (4 * c1) (4 * c2) :=
    le_ciInf (fun m => P.doubling_candidate hc1 hc2 m.1 m.2)
  refine ⟨h4, ?_⟩
  have := P.Jjoint_concave hc1 hc2
  linarith

theorem cancellation_pf (P : Params) : 3 / 5 * P.Jjoint P.k1 P.k2 ≤ P.Ltwo := by
  have hk1 := P.k1_nonneg
  have hk2 := P.k2_nonneg
  have h2 := P.Jjoint_le_B (c1 := 2 * P.k1) (c2 := 2 * P.k2) (by positivity) (by positivity)
  have h4 := P.Jjoint_le_B (c1 := 4 * P.k1) (c2 := 4 * P.k2) (by positivity) (by positivity)
  obtain ⟨d4, d2⟩ := joint_doubling_pf P P.k1 P.k2 hk1 hk2
  have hL1 : (P.B1 (2 * P.k1) + P.B2 (2 * P.k2)) / 2 ≤ P.Ltwo := le_max_left _ _
  have hL2 : P.V0 / 2 + (P.B1 (4 * P.k1) + P.B2 (4 * P.k2)) / 4 ≤ P.Ltwo := le_max_right _ _
  linarith

end TwoStageRnQ

open TwoStageRnQ

theorem solution (P : Params) :
    3 / 5 * P.Jjoint P.k1 P.k2 ≤ P.Ltwo :=
  TwoStageRnQ.cancellation_pf P
