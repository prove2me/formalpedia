-- Prove2me | solution 1 for TwoStageRnQ.V0_le_Jjoint
-- status  : ACCEPTED   (prove)
-- author  : @beatlesmania
-- created : 2026-11-17T00:27:11.22417+00:00
-- url     : https://prove2.me/submissions/61438849-bef1-4f21-9026-f88cb4690644

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

lemma sum_div' {ι : Type*} (s : Finset ι) (f : ι → ℝ) (a : ℝ) :
    (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a := by
  simp only [div_eq_mul_inv, Finset.sum_mul]

/-! ## Piecewise linearity between consecutive integers -/

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

/-- `ψ(v) = 𝓛_m G₀(v) - h₂ v`. -/
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

/-- An integer minimizer of `ψ` over the integers `≤ Z` (Appendix D.5). -/
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

/-- Integrand of the capped joint cost. -/
def capT (m1 : ℕ) (r Y : ℝ) : ℝ := latAvg m1 P.G0 (min r Y) + P.h2 * (Y - min r Y)

/-- Capped joint cost `Φ_r(z)`. -/
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

/-- Number of upstream positions `j < m₂` with `j ≡ b (mod m₁)`. -/
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

/-- Reorder-point difference of the policy built from the remainder group `b` (eq. (D.12)). -/
def grpEll (m1 m2 : ℕ) (z' r : ℤ) (b : ℕ) : ℤ :=
  z' - r - b - m1 * ((grpSize m1 m2 b : ℤ) - 1)

/-- The classical candidate built from the remainder group `b` (eq. (D.10)). -/
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

lemma classicalFormula_nonneg (R1 R2 : ℤ) (Q n : ℕ+) : 0 ≤ P.classicalFormula R1 R2 Q n := by
  unfold classicalFormula invCost
  have := P.k1_nonneg; have := P.k2_nonneg
  refine add_nonneg (add_nonneg (by positivity) (by positivity)) ?_
  refine div_nonneg (Finset.sum_nonneg (fun j _ => pexp_nonneg P.mu2_nonneg (fun d => ?_)))
    (Nat.cast_nonneg _)
  exact add_nonneg (P.latAvg_G0_nonneg _ _) (mul_nonneg P.h2_nonneg (le_max_right _ _))

lemma formula_bddBelow :
    BddBelow (Set.range fun c : ℤ × ℤ × ℕ+ × ℕ+ => P.classicalFormula c.1 c.2.1 c.2.2.1 c.2.2.2) :=
  ⟨0, by rintro _ ⟨c, rfl⟩; exact P.classicalFormula_nonneg _ _ _ _⟩

/-- Weighted remainder-group identity and the resulting policy bound (Lemma D.2). -/
lemma formula_le_capPhi (m1 m2 : ℕ+) (z' r : ℤ) :
    (⨅ c : ℤ × ℤ × ℕ+ × ℕ+, P.classicalFormula c.1 c.2.1 c.2.2.1 c.2.2.2)
      ≤ P.k1 / ((m1 : ℕ) : ℝ) + P.k2 / ((m2 : ℕ) : ℝ) + P.capPhi m1 m2 r z' := by
  have hm1 := m1.pos
  have hm2 := m2.pos
  have hμ := P.mu2_nonneg
  have hm2r : (0 : ℝ) < ((m2 : ℕ) : ℝ) := by exact_mod_cast hm2
  have hm1r : (0 : ℝ) < ((m1 : ℕ) : ℝ) := by exact_mod_cast hm1
  set s := (range (m1 : ℕ)).filter (fun b => 0 < grpSize m1 m2 b) with hs
  set w : ℕ → ℝ := fun b => ((grpSize m1 m2 b : ℕ) : ℝ) / ((m2 : ℕ) : ℝ) with hw
  set X := P.k1 / ((m1 : ℕ) : ℝ) + P.k2 / ((m2 : ℕ) : ℝ) + P.capPhi m1 m2 r z' with hX
  -- total weight
  have hsum_w : ∑ b ∈ s, w b = 1 := by
    rw [hs, Finset.sum_filter]
    have : ∀ b ∈ range (m1 : ℕ), (if 0 < grpSize m1 m2 b then w b else 0) = w b := by
      intro b _
      split_ifs with h
      · rfl
      · simp [hw, Nat.eq_zero_of_not_pos h]
    rw [Finset.sum_congr rfl this, hw, ← sum_div', grpSize_sum hm1, div_self hm2r.ne']
  -- the capped cost regrouped
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
  -- weighted sum of the candidate costs
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
  -- some candidate is no worse than the weighted average
  have hne : s.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm1,
    grpSize_pos_zero hm1 hm2⟩⟩
  have hle : ∑ b ∈ s, w b * P.grpCost m1 m2 z' r b ≤ ∑ b ∈ s, w b * X := by
    rw [← Finset.sum_mul, hsum_w, one_mul]; exact hweighted
  obtain ⟨b, hb, hbX⟩ := Finset.exists_le_of_sum_le hne hle
  have hwpos : 0 < w b := by
    rw [hw]; have := (Finset.mem_filter.mp hb).2; positivity
  have hcb : P.grpCost m1 m2 z' r b ≤ X := le_of_mul_le_mul_left hbX hwpos
  refine (ciInf_le P.formula_bddBelow ((r - (m1 : ℕ)), (r - (m1 : ℕ) + grpEll m1 m2 z' r b), m1,
    Nat.toPNat' (grpSize m1 m2 b))).trans ?_
  exact hcb

lemma formula_le_candidate (m1 m2 : ℕ+) {z : ℝ} {x : ℕ → Fin m2 → ℝ}
    (hx : P.JointFeasible m2 z x) :
    (⨅ c : ℤ × ℤ × ℕ+ × ℕ+, P.classicalFormula c.1 c.2.1 c.2.2.1 c.2.2.2)
      ≤ P.k1 / ((m1 : ℕ) : ℝ) + P.k2 / ((m2 : ℕ) : ℝ) + P.jointObj m1 m2 z x := by
  obtain ⟨r, -, hmin⟩ := P.exists_int_min m1.pos ⌈z⌉
  have h1 := P.capPhi_le_jointObj hmin (Int.le_ceil z) hx
  obtain ⟨z', -, h2⟩ := P.capPhi_ge_int m1 m2 r z
  have h3 := P.formula_le_capPhi m1 m2 z' r
  linarith

end Params

theorem formula_policy_bound_pf (P : Params) :
    (⨅ c : ℤ × ℤ × ℕ+ × ℕ+, P.classicalFormula c.1 c.2.1 c.2.2.1 c.2.2.2)
      ≤ P.Jjoint P.k1 P.k2 := by
  refine le_ciInf (fun m => ?_)
  haveI := P.Vjoint_feasible_nonempty m.2
  have h : ∀ zx : {zx : ℝ × (ℕ → Fin m.2 → ℝ) // P.JointFeasible m.2 zx.1 zx.2},
      (⨅ c : ℤ × ℤ × ℕ+ × ℕ+, P.classicalFormula c.1 c.2.1 c.2.2.1 c.2.2.2)
        - P.k1 / ((m.1 : ℕ) : ℝ) - P.k2 / ((m.2 : ℕ) : ℝ) ≤ P.jointObj m.1 m.2 zx.1.1 zx.1.2 :=
    fun zx => by have := P.formula_le_candidate m.1 m.2 zx.2; linarith
  have := le_ciInf h
  unfold Params.Vjoint
  linarith

end TwoStageRnQ

open Finset Filter Topology

noncomputable section

namespace TwoStageRnQ

namespace Params

variable (P : Params)

/-! ## The zero-setup value is below every joint value (eq. (22), Lemma D.1) -/

lemma latAvg_one (F : ℝ → ℝ) (x : ℝ) : latAvg 1 F x = F x := by
  unfold latAvg; simp

lemma V0_bddBelow :
    BddBelow (Set.range fun ry : ℝ × ℝ => pexp P.mu2 (fun d =>
      P.G0 (ry.1 - max (-(ry.2 - (d : ℝ))) 0) + P.h2 * max (ry.2 - (d : ℝ)) 0)) :=
  ⟨0, by
    rintro _ ⟨ry, rfl⟩
    exact pexp_nonneg P.mu2_nonneg (fun d =>
      add_nonneg (P.G0_nonneg _) (mul_nonneg P.h2_nonneg (le_max_right _ _)))⟩

/-- A single conditional problem (fixed cycle positions) costs at least `V₀`. -/
lemma V0_le_single {z' : ℝ} {x' : ℕ → ℝ} (hx : ∀ d : ℕ, x' d ≤ z' - d) (hxi : PInt P.mu2 x') :
    P.V0 ≤ pexp P.mu2 (fun d => P.G0 (x' d) + P.h2 * (z' - d - x' d)) := by
  have hμ := P.mu2_nonneg
  obtain ⟨r, -, hmin⟩ := P.exists_int_min (m := 1) one_pos ⌈z'⌉
  set y : ℝ := z' - r with hy
  refine (ciInf_le P.V0_bddBelow ((r : ℝ), y)).trans ?_
  have hmin' : PInt P.mu2 (fun d : ℕ => min (r : ℝ) (z' - d)) :=
    PInt.of_affine hμ (pint_const 0) (A := |(r : ℝ)| + |z'|) (B := 0) (C := 1) (fun d => by
      have := abs_min_le_add (r : ℝ) (z' - d)
      have := abs_sub_nat z' d
      simp; nlinarith)
  have hL : PInt P.mu2 (fun d : ℕ => P.G0 ((r, y).1 - max (-((r, y).2 - (d : ℝ))) 0)
      + P.h2 * max ((r, y).2 - (d : ℝ)) 0) := by
    have e : ∀ d : ℕ, P.G0 ((r, y).1 - max (-((r, y).2 - (d : ℝ))) 0)
        + P.h2 * max ((r, y).2 - (d : ℝ)) 0 = P.capT 1 r (z' - d) := by
      intro d
      have := P.capT_eq 1 r (y - d)
      rw [latAvg_one] at this
      simp only
      rw [this]
      congr 1; rw [hy]; ring
    have h1 := P.pint_capT 1 r z' 0
    simp only [sub_zero] at h1
    exact PInt.of_abs_le hμ h1.abs (fun d => by rw [e d])
  refine pexp_mono hμ hL ?_ (fun d => ?_)
  · exact (PInt.of_affine hμ hxi (A := P.H0 + (P.h1 + P.h2 + P.p) * P.mu1)
      (B := P.h1 + P.h2 + P.p) (C := 0) (fun d => by have := P.G0_abs_le (x' d); linarith)).add hμ
      ((((pint_const z').sub hμ pint_nat).sub hμ hxi).const_mul _)
  · have hY : z' - d ≤ (⌈z'⌉ : ℝ) := by
      have := Int.le_ceil z'; have := Nat.cast_nonneg (α := ℝ) d; linarith
    have hc := P.psi_cap 1 hmin hY (hx d)
    unfold psi at hc
    rw [latAvg_one, latAvg_one] at hc
    have hcap := P.capT_eq 1 r (y - d)
    rw [latAvg_one] at hcap
    simp only
    rw [hcap]
    unfold capT
    rw [latAvg_one]
    have : (r : ℝ) + (y - d) = z' - d := by rw [hy]; ring
    rw [this]
    nlinarith

lemma V0_le_jointObj {m1 m2 : ℕ} (hm1 : 0 < m1) (hm2 : 0 < m2) {z : ℝ} {x : ℕ → Fin m2 → ℝ}
    (hx : P.JointFeasible m2 z x) : P.V0 ≤ P.jointObj m1 m2 z x := by
  have hμ := P.mu2_nonneg
  have hm1r : (0 : ℝ) < m1 := by exact_mod_cast hm1
  have hm2r : (0 : ℝ) < m2 := by exact_mod_cast hm2
  -- the (i,j) conditional integrands
  set f : Fin m2 → ℕ → ℕ → ℝ := fun j i d =>
    P.G0 (x d j - i) + P.h2 * (z - d - ((j : ℕ) : ℝ) - x d j) with hf
  have hfint : ∀ j i, PInt P.mu2 (f j i) := fun j i =>
    (PInt.of_affine hμ (show PInt P.mu2 (fun d => x d j) from hx.2 j) (A := P.H0 + (P.h1 + P.h2 + P.p) * (P.mu1 + |(i : ℝ)|))
      (B := P.h1 + P.h2 + P.p) (C := 0) (fun d => by
        have := P.G0_sub_abs_le (x d j) (i : ℝ); linarith)).add hμ
      (((((pint_const z).sub hμ pint_nat).sub hμ (pint_const _)).sub hμ (show PInt P.mu2 (fun d => x d j) from hx.2 j)).const_mul _)
  have hV0f : ∀ j i, P.V0 ≤ pexp P.mu2 (f j i) := by
    intro j i
    have := P.V0_le_single (z' := z - ((j : ℕ) : ℝ) - i) (x' := fun d => x d j - i)
      (fun d => by have := hx.1 d j; linarith) ((show PInt P.mu2 (fun d => x d j) from hx.2 j).sub hμ (pint_const _))
    refine this.trans (le_of_eq (pexp_congr (fun d => ?_)))
    simp only [hf]; ring_nf
  -- rewrite the joint objective as an average of conditional objectives
  have hrow : ∀ d : ℕ, (∑ j : Fin m2, (latAvg m1 P.G0 (x d j)
      + P.h2 * (z - d - ((j : ℕ) : ℝ) - x d j))) / m2
      = (∑ j : Fin m2, (∑ i ∈ range m1, f j i d) / m1) / m2 := by
    intro d
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    unfold latAvg
    simp only [hf]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, add_div]
    field_simp
  unfold jointObj
  rw [pexp_congr hrow, pexp_div_const,
    pexp_finset_sum hμ _ (fun j _ => PInt.div_const (PInt.sum hμ _ (fun i _ => hfint j i)) _)]
  rw [le_div_iff₀ hm2r]
  have : P.V0 * m2 = ∑ _j : Fin m2, P.V0 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  rw [this]
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [pexp_div_const, pexp_finset_sum hμ _ (fun i _ => hfint j i), le_div_iff₀ hm1r]
  have : P.V0 * m1 = ∑ _i ∈ range m1, P.V0 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  rw [this]
  exact Finset.sum_le_sum (fun i _ => hV0f j i)

lemma V0_le_Vjoint {m1 m2 : ℕ} (hm1 : 0 < m1) (hm2 : 0 < m2) : P.V0 ≤ P.Vjoint m1 m2 := by
  haveI := P.Vjoint_feasible_nonempty m2
  exact le_ciInf (fun zx => P.V0_le_jointObj hm1 hm2 zx.2)

end Params

theorem V0_le_Jjoint_pf (P : Params) (c1 c2 : ℝ) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) :
    P.V0 ≤ P.Jjoint c1 c2 :=
  le_ciInf (fun m => by
    have := P.V0_le_Vjoint m.1.pos m.2.pos
    have : 0 ≤ c1 / ((m.1 : ℕ) : ℝ) := div_nonneg hc1 (Nat.cast_nonneg _)
    have : 0 ≤ c2 / ((m.2 : ℕ) : ℝ) := div_nonneg hc2 (Nat.cast_nonneg _)
    linarith)

end TwoStageRnQ

open TwoStageRnQ

theorem solution (P : Params) (c1 c2 : ℝ) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) :
    P.V0 ≤ P.Jjoint c1 c2 :=
  TwoStageRnQ.V0_le_Jjoint_pf P c1 c2 hc1 hc2
