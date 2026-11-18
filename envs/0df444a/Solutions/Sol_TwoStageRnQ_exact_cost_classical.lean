-- Prove2me | solution 1 for TwoStageRnQ.exact_cost_classical
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T00:27:15.700302+00:00
-- url     : https://prove2.me/submissions/bc1d95ab-2011-4590-8f65-7f6803cbda1e

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
import Definitions.Def_TwoStageRnQ_Model
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Card
import Definitions.Def_TwoStageRnQ_Model
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

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

lemma pexp_const_mul (μ c : ℝ) (f : ℕ → ℝ) : pexp μ (fun n => c * f n) = c * pexp μ f := by
  unfold pexp
  simp_rw [mul_left_comm _ c]
  exact tsum_mul_left

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

lemma G0_abs_le (x : ℝ) : |P.G0 x| ≤ P.H0 + (P.h1 + P.h2 + P.p) * (|x| + P.mu1) := by
  rw [abs_of_nonneg (P.G0_nonneg x)]; unfold G0; linarith [P.lossDown_le x]

end Params

lemma latAvg_add_const {j : ℕ} (hj : 0 < j) (F : ℝ → ℝ) (c x : ℝ) :
    latAvg j (fun y => c + F y) x = c + latAvg j F x := by
  unfold latAvg
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : (j : ℝ) ≠ 0 := by positivity
  field_simp

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

lemma latAvg_G0 {m : ℕ} (hm : 0 < m) (x : ℝ) :
    latAvg m P.G0 x = P.H0 + latAvg m P.lossDown x := by
  have : P.G0 = fun y => P.H0 + P.lossDown y := rfl
  rw [this, latAvg_add_const hm]

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

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

lemma ncard_Ioc_int (a b : ℤ) : (Set.Ioc a b).ncard = (b - a).toNat := by
  rw [← Finset.coe_Ioc, Set.ncard_coe_finset, Int.card_Ioc]

lemma jumpCount_le_toNat {f : ℝ → ℤ} {T : ℝ} (φ : ℝ → ℤ) (a b : ℤ)
    (hmem : ∀ t, t ∈ Set.Ioc 0 T → (∀ s < t, f s < f t) → a < φ t ∧ φ t ≤ b)
    (hφ : ∀ t₁ t₂, t₁ ∈ Set.Ioc 0 T → t₂ ∈ Set.Ioc 0 T → f t₁ < f t₂ → φ t₁ < φ t₂) :
    jumpCount f T ≤ (b - a).toNat := by
  unfold jumpCount
  rw [← ncard_Ioc_int a b]
  refine Set.ncard_le_ncard_of_injOn φ (fun t ht => ?_) (fun t₁ h₁ t₂ h₂ heq => ?_)
    (Set.finite_Ioc a b)
  · exact hmem t ht.1 ht.2
  · rcases lt_trichotomy t₁ t₂ with h | h | h
    · exact absurd heq (ne_of_lt (hφ t₁ t₂ h₁.1 h₂.1 (h₂.2 t₁ h)))
    · exact h
    · exact absurd heq.symm (ne_of_lt (hφ t₂ t₁ h₂.1 h₁.1 (h₁.2 t₂ h)))

lemma jumpCount_le_real {f : ℝ → ℤ} {T : ℝ} (φ : ℝ → ℤ) (a b : ℤ) (hab : a ≤ b)
    (hmem : ∀ t, t ∈ Set.Ioc 0 T → (∀ s < t, f s < f t) → a < φ t ∧ φ t ≤ b)
    (hφ : ∀ t₁ t₂, t₁ ∈ Set.Ioc 0 T → t₂ ∈ Set.Ioc 0 T → f t₁ < f t₂ → φ t₁ < φ t₂) :
    (jumpCount f T : ℝ) ≤ ((b - a : ℤ) : ℝ) := by
  have h := jumpCount_le_toNat φ a b hmem hφ
  have h' : ((jumpCount f T : ℕ) : ℤ) ≤ b - a := by
    have := Int.toNat_of_nonneg (sub_nonneg.mpr hab)
    omega
  exact_mod_cast h'

lemma jumpCount_mul_le {g : ℝ → ℤ} (hg : Monotone g) (q : ℤ) (hq : 0 < q) {T : ℝ} (hT : 0 ≤ T) :
    (jumpCount (fun t => q * g t) T : ℝ) ≤ ((g T - g 0 : ℤ) : ℝ) := by
  refine jumpCount_le_real g (g 0) (g T) (hg hT) (fun t ht hj => ?_) (fun t₁ t₂ _ _ h => ?_)
  · refine ⟨?_, hg ht.2⟩
    have := hj 0 ht.1
    exact lt_of_mul_lt_mul_left this hq.le
  · exact lt_of_mul_lt_mul_left h hq.le

lemma longRunCost_mono {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) (cI : ℝ → Ω → ℝ)
    {Z Z' : ℝ → Ω → ℝ} (h : ∀ T, 0 ≤ T → ∀ ω, Z T ω ≤ Z' T ω) :
    longRunCost ν cI Z ≤ longRunCost ν cI Z' := by
  unfold longRunCost
  refine Filter.limsup_le_limsup ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
  gcongr with ω
  exact h T hT ω

end TwoStageRnQ

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace DemandSpace

variable {P : Params} (S : DemandSpace P)

lemma N_meas (t : ℝ) : Measurable (S.N t) :=
  (S.N_adapted t).mono (S.𝓕.le t) le_rfl

lemma N_meas_le {v u : ℝ} (h : v ≤ u) : Measurable[S.𝓕 u] (S.N v) :=
  (S.N_adapted v).mono (S.𝓕.mono h) le_rfl

lemma incr_nonneg {v t : ℝ} (h : v ≤ t) (ω : S.Ω) : 0 ≤ S.N t ω - S.N v ω :=
  sub_nonneg.mpr (S.N_mono ω h)

lemma indep_set {v t : ℝ} (hv : 0 ≤ v) (h : v ≤ t) {A : Set S.Ω} (hA : MeasurableSet[S.𝓕 v] A)
    (k : ℤ) :
    S.ν (A ∩ {ω | S.N t ω - S.N v ω = k}) = S.ν A * S.ν {ω | S.N t ω - S.N v ω = k} := by
  have hI := (Indep_iff _ _ S.ν).mp (S.N_indep v t hv h)
  have hk : MeasurableSet[MeasurableSpace.comap (fun ω => S.N t ω - S.N v ω) inferInstance]
      {ω | S.N t ω - S.N v ω = k} := ⟨{k}, measurableSet_singleton k, rfl⟩
  rw [Set.inter_comm, hI _ _ hk hA, mul_comm]

lemma lintegral_comp {X : S.Ω → ℤ} (hX : Measurable X) (g : ℤ → ℝ≥0∞) :
    ∫⁻ ω, g (X ω) ∂S.ν = ∑' a : ℤ, S.ν (X ⁻¹' {a}) * g a := by
  rw [← lintegral_map (measurable_of_countable g) hX, lintegral_countable']
  refine tsum_congr (fun a => ?_)
  rw [Measure.map_apply hX (measurableSet_singleton a), mul_comm]

lemma lintegral_comp' {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    {X : S.Ω → α} (hX : Measurable X) (g : α → ℝ≥0∞) :
    ∫⁻ ω, g (X ω) ∂S.ν = ∑' a : α, S.ν (X ⁻¹' {a}) * g a := by
  rw [← lintegral_map (measurable_of_countable g) hX, lintegral_countable']
  refine tsum_congr (fun a => ?_)
  rw [Measure.map_apply hX (measurableSet_singleton a), mul_comm]

lemma lintegral_incr {v t : ℝ} (hv : 0 ≤ v) (h : v ≤ t) {X : S.Ω → ℤ} (hX : Measurable[S.𝓕 v] X)
    (g : ℤ → ℕ → ℝ≥0∞) :
    ∫⁻ ω, g (X ω) (S.N t ω - S.N v ω).toNat ∂S.ν
      = ∑' a : ℤ, S.ν (X ⁻¹' {a}) *
          ∑' d : ℕ, ENNReal.ofReal (poisW (P.lam * (t - v)) d) * g a d := by
  have hXm : Measurable X := hX.mono (S.𝓕.le v) le_rfl
  set Y : S.Ω → ℤ × ℕ := fun ω => (X ω, (S.N t ω - S.N v ω).toNat) with hY
  have hYm : Measurable Y :=
    hXm.prodMk ((measurable_of_countable (fun z : ℤ => z.toNat)).comp
      ((S.N_meas t).sub (S.N_meas v)))
  have h1 : ∫⁻ ω, g (X ω) (S.N t ω - S.N v ω).toNat ∂S.ν = ∫⁻ p, g p.1 p.2 ∂(S.ν.map Y) := by
    rw [lintegral_map (measurable_of_countable (fun p : ℤ × ℕ => g p.1 p.2)) hYm]
  rw [h1, lintegral_countable']
  have h2 : ∀ p : ℤ × ℕ, (S.ν.map Y) {p}
      = S.ν (X ⁻¹' {p.1}) * ENNReal.ofReal (poisW (P.lam * (t - v)) p.2) := by
    intro p
    rw [Measure.map_apply hYm (measurableSet_singleton p)]
    have hpre : Y ⁻¹' {p} = X ⁻¹' {p.1} ∩ {ω | S.N t ω - S.N v ω = ((p.2 : ℕ) : ℤ)} := by
      ext ω
      simp only [hY, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
        Set.mem_setOf_eq, Prod.ext_iff]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rw [← h2, Int.toNat_of_nonneg (S.incr_nonneg h ω)]
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [h2]; simp⟩
    rw [hpre, S.indep_set hv h (hX (measurableSet_singleton _)), S.N_law v t h]
  simp_rw [h2]
  rw [ENNReal.tsum_prod (f := fun a d => g a d *
    (S.ν (X ⁻¹' {a}) * ENNReal.ofReal (poisW (P.lam * (t - v)) d)))]
  refine tsum_congr (fun a => ?_)
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr (fun d => ?_)
  ring

lemma lintegral_incr_val {v t : ℝ} (h : v ≤ t) :
    ∫⁻ ω, ENNReal.ofReal ((S.N t ω - S.N v ω : ℤ) : ℝ) ∂S.ν = ENNReal.ofReal (P.lam * (t - v)) := by
  have hμ : 0 ≤ P.lam * (t - v) := mul_nonneg P.lam_nonneg (by linarith)
  set Y : S.Ω → ℕ := fun ω => (S.N t ω - S.N v ω).toNat with hY
  have hYm : Measurable Y := by
    have h1 := (measurable_of_countable (fun z : ℤ => z.toNat)).comp ((S.N_meas t).sub (S.N_meas v))
    exact h1
  have e : ∀ ω, ENNReal.ofReal ((S.N t ω - S.N v ω : ℤ) : ℝ)
      = (fun k : ℕ => ENNReal.ofReal (k : ℝ)) (Y ω) := by
    intro ω
    simp only [hY]
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (S.incr_nonneg h ω)]
  rw [lintegral_congr e, S.lintegral_comp' hYm (fun k : ℕ => ENNReal.ofReal (k : ℝ))]
  have hY1 : ∀ k : ℕ, S.ν (Y ⁻¹' {k}) = ENNReal.ofReal (poisW (P.lam * (t - v)) k) := by
    intro k
    have : Y ⁻¹' {k} = {ω | S.N t ω - S.N v ω = (k : ℤ)} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, hY]
      constructor
      · intro hk; rw [← hk, Int.toNat_of_nonneg (S.incr_nonneg h ω)]
      · intro hk; rw [hk]; simp
    rw [this, S.N_law v t h k]
  simp_rw [hY1]
  have hs : Summable (fun d : ℕ => poisW (P.lam * (t - v)) d * (d : ℝ)) :=
    summable_poisW_mul_nat _
  conv_rhs => rw [← tsum_poisW_mul_nat (P.lam * (t - v))]
  rw [ENNReal.ofReal_tsum_of_nonneg
    (fun d => mul_nonneg (poisW_nonneg hμ d) (Nat.cast_nonneg d)) hs]
  refine tsum_congr (fun d => ?_)
  rw [ENNReal.ofReal_mul (poisW_nonneg hμ d)]

section Residue

variable (m : ℕ)

def resLaw (x : ℝ) (r : ℤ) : ℝ≥0∞ := S.ν {ω | S.N x ω % (m : ℤ) = r}

lemma res_meas (x : ℝ) : Measurable[S.𝓕 x] (fun ω => S.N x ω % (m : ℤ)) :=
  (measurable_of_countable (fun z : ℤ => z % (m : ℤ))).comp (S.N_adapted x)

lemma res_meas' (x : ℝ) : Measurable (fun ω => S.N x ω % (m : ℤ)) :=
  (S.res_meas m x).mono (S.𝓕.le x) le_rfl

lemma resLaw_eq_zero (hm : 0 < m) (x : ℝ) {r : ℤ} (hr : r ∉ Finset.Ico (0 : ℤ) m) :
    S.resLaw m x r = 0 := by
  have : {ω | S.N x ω % (m : ℤ) = r} = ∅ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    apply hr
    rw [Finset.mem_Ico, ← h]
    exact ⟨Int.emod_nonneg _ (by exact_mod_cast hm.ne'),
      Int.emod_lt_of_pos _ (by exact_mod_cast hm)⟩
  unfold resLaw; rw [this, measure_empty]

lemma tsum_res (hm : 0 < m) (x : ℝ) (g : ℤ → ℝ≥0∞) :
    ∑' a : ℤ, S.ν ((fun ω => S.N x ω % (m : ℤ)) ⁻¹' {a}) * g a
      = ∑ a ∈ Finset.Ico (0 : ℤ) m, S.resLaw m x a * g a := by
  rw [tsum_eq_sum (s := Finset.Ico (0 : ℤ) m)]
  · rfl
  · intro a ha
    have := S.resLaw_eq_zero m hm x ha
    unfold resLaw at this
    simp only [Set.preimage, Set.mem_singleton_iff] at *
    rw [this, zero_mul]

lemma resLaw_sum (hm : 0 < m) (x : ℝ) : ∑ a ∈ Finset.Ico (0 : ℤ) m, S.resLaw m x a = 1 := by
  have h := S.lintegral_comp (S.res_meas' m x) (fun _ => 1)
  rw [lintegral_const, measure_univ, one_mul, S.tsum_res m hm x] at h
  simpa using h.symm

lemma resLaw_ne_top (x : ℝ) (r : ℤ) : S.resLaw m x r ≠ ⊤ :=
  measure_ne_top _ _

def kern (μ : ℝ) (a r : ℤ) : ℝ := ∑' d : ℕ, if (a + d) % (m : ℤ) = r then poisW μ d else 0

lemma kern_summable {μ : ℝ} (hμ : 0 ≤ μ) (a r : ℤ) :
    Summable (fun d : ℕ => if (a + d) % (m : ℤ) = r then poisW μ d else 0) :=
  (summable_poisW μ).of_nonneg_of_le (fun d => by split_ifs <;> simp [poisW_nonneg hμ d])
    (fun d => by split_ifs <;> simp [poisW_nonneg hμ d])

lemma kern_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (a r : ℤ) : 0 ≤ kern m μ a r :=
  tsum_nonneg (fun d => by split_ifs <;> simp [poisW_nonneg hμ d])

lemma kern_ge {μ : ℝ} (hμ : 0 ≤ μ) (hm : 0 < m) {a r : ℤ} (hr : r ∈ Finset.Ico (0 : ℤ) m) :
    poisW μ ((r - a) % (m : ℤ)).toNat ≤ kern m μ a r := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  set d0 : ℕ := ((r - a) % (m : ℤ)).toNat
  have hd0 : ((d0 : ℕ) : ℤ) = (r - a) % (m : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ hm'.ne')
  have hc : (a + (d0 : ℤ)) % (m : ℤ) = r := by
    rw [hd0, Int.add_emod_emod, add_sub_cancel]
    rw [Finset.mem_Ico] at hr
    exact Int.emod_eq_of_lt hr.1 hr.2
  have := (kern_summable m hμ a r).le_tsum d0 (fun d _ => by split_ifs <;> simp [poisW_nonneg hμ d])
  simp only [hc, if_true] at this
  exact this

lemma kern_row {μ : ℝ} (hμ : 0 ≤ μ) (hm : 0 < m) (a : ℤ) :
    ∑ r ∈ Finset.Ico (0 : ℤ) m, kern m μ a r = 1 := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  unfold kern
  rw [← Summable.tsum_finsetSum (fun r _ => kern_summable m hμ a r)]
  have : ∀ d : ℕ, ∑ r ∈ Finset.Ico (0 : ℤ) m, (if (a + d) % (m : ℤ) = r then poisW μ d else 0)
      = poisW μ d := by
    intro d
    rw [Finset.sum_ite_eq]
    rw [if_pos (Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ hm'.ne', Int.emod_lt_of_pos _ hm'⟩)]
  simp_rw [this]
  exact tsum_poisW μ

lemma kern_col {μ : ℝ} (hμ : 0 ≤ μ) (hm : 0 < m) {r : ℤ} (hr : r ∈ Finset.Ico (0 : ℤ) m) :
    ∑ a ∈ Finset.Ico (0 : ℤ) m, kern m μ a r = 1 := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  unfold kern
  rw [← Summable.tsum_finsetSum (fun a _ => kern_summable m hμ a r)]
  have : ∀ d : ℕ, ∑ a ∈ Finset.Ico (0 : ℤ) m, (if (a + d) % (m : ℤ) = r then poisW μ d else 0)
      = poisW μ d := by
    intro d
    have hmem : (r - d) % (m : ℤ) ∈ Finset.Ico (0 : ℤ) m :=
      Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ hm'.ne', Int.emod_lt_of_pos _ hm'⟩
    rw [Finset.sum_eq_single_of_mem _ hmem]
    · rw [if_pos]
      rw [Int.emod_add_emod, sub_add_cancel]
      rw [Finset.mem_Ico] at hr
      exact Int.emod_eq_of_lt hr.1 hr.2
    · intro b hb hne
      rw [if_neg]
      intro hc
      apply hne
      rw [Finset.mem_Ico] at hb hr
      have h1 : b % (m : ℤ) = b := Int.emod_eq_of_lt hb.1 hb.2
      have hmod : (b + d) ≡ r [ZMOD (m : ℤ)] := by
        unfold Int.ModEq; rw [hc]; exact (Int.emod_eq_of_lt hr.1 hr.2).symm
      have h2 := hmod.sub_right (d : ℤ)
      simp only [add_sub_cancel_right] at h2
      unfold Int.ModEq at h2
      rw [← h1, h2]
  simp_rw [this]
  exact tsum_poisW μ

lemma resLaw_step (hm : 0 < m) {x : ℝ} (hx1 : 1 ≤ x) (r : ℤ) :
    (S.resLaw m x r).toReal
      = ∑ a ∈ Finset.Ico (0 : ℤ) m, (S.resLaw m (x - 1) a).toReal * kern m P.lam a r := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hl := P.lam_nonneg
  have hx : x - 1 ≤ x := by linarith
  set g : ℤ → ℕ → ℝ≥0∞ := fun a d => if (a + d) % (m : ℤ) = r then 1 else 0 with hg
  have hpt : ∀ ω, Set.indicator {ω | S.N x ω % (m : ℤ) = r} 1 ω
      = g (S.N (x - 1) ω % (m : ℤ)) (S.N x ω - S.N (x - 1) ω).toNat := by
    intro ω
    have e : (S.N (x - 1) ω % (m : ℤ) + ((S.N x ω - S.N (x - 1) ω).toNat : ℤ)) % (m : ℤ)
        = S.N x ω % (m : ℤ) := by
      rw [Int.toNat_of_nonneg (S.incr_nonneg hx ω), Int.emod_add_emod]; ring_nf
    simp only [Set.indicator_apply, Set.mem_setOf_eq, hg, e, Pi.one_apply]
  have hint : S.resLaw m x r = ∫⁻ ω, g (S.N (x - 1) ω % (m : ℤ))
      (S.N x ω - S.N (x - 1) ω).toNat ∂S.ν := by
    simp_rw [← hpt]
    rw [lintegral_indicator_one]
    · rfl
    · exact (S.res_meas' m x) (measurableSet_singleton r)
  rw [hint, S.lintegral_incr (by linarith) hx (S.res_meas m (x - 1)) g, S.tsum_res m hm (x - 1)]
  have hk : ∀ a : ℤ, ∑' d : ℕ, ENNReal.ofReal (poisW (P.lam * (x - (x - 1))) d) * g a d
      = ENNReal.ofReal (kern m P.lam a r) := by
    intro a
    have e1 : P.lam * (x - (x - 1)) = P.lam := by ring
    rw [e1]
    unfold kern
    rw [ENNReal.ofReal_tsum_of_nonneg (fun d => by split_ifs <;> simp [poisW_nonneg hl d])
      (kern_summable m hl a r)]
    refine tsum_congr (fun d => ?_)
    simp only [hg]
    split_ifs <;> simp
  simp_rw [hk]
  rw [ENNReal.toReal_sum (fun a _ => ENNReal.mul_ne_top (S.resLaw_ne_top m _ a)
    ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (kern_nonneg m hl a r)]

lemma contraction {s : Finset ℤ} (K : ℤ → ℤ → ℝ) (ε : ℝ)
    (hK : ∀ a ∈ s, ∀ r ∈ s, ε ≤ K a r)
    (hrow : ∀ a ∈ s, ∑ r ∈ s, K a r = 1) (hcol : ∀ r ∈ s, ∑ a ∈ s, K a r = 1)
    (p : ℤ → ℝ) (hp : ∑ a ∈ s, p a = 1) (u : ℝ) (hu : (s.card : ℝ) * u = 1) :
    ∑ r ∈ s, |∑ a ∈ s, p a * K a r - u| ≤ (1 - s.card * ε) * ∑ a ∈ s, |p a - u| := by
  have hsum0 : ∑ a ∈ s, (p a - u) = 0 := by
    rw [Finset.sum_sub_distrib, hp, Finset.sum_const, nsmul_eq_mul, hu, sub_self]
  have key : ∀ r ∈ s, ∑ a ∈ s, p a * K a r - u = ∑ a ∈ s, (p a - u) * (K a r - ε) := by
    intro r hr
    have e1 : ∑ a ∈ s, (p a - u) * (K a r - ε)
        = ∑ a ∈ s, p a * K a r - u * ∑ a ∈ s, K a r - ε * ∑ a ∈ s, (p a - u) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun a _ => by ring)
    rw [e1, hcol r hr, hsum0]; ring
  have hb : ∀ r ∈ s, |∑ a ∈ s, p a * K a r - u| ≤ ∑ a ∈ s, |p a - u| * (K a r - ε) := by
    intro r hr
    rw [key r hr]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl (fun a ha => ?_)))
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hK a ha r hr))]
  calc ∑ r ∈ s, |∑ a ∈ s, p a * K a r - u|
      ≤ ∑ r ∈ s, ∑ a ∈ s, |p a - u| * (K a r - ε) := Finset.sum_le_sum hb
    _ = ∑ a ∈ s, |p a - u| * (∑ r ∈ s, K a r - s.card * ε) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    _ = (1 - s.card * ε) * ∑ a ∈ s, |p a - u| := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a ha => ?_)
        rw [hrow a ha]; ring

theorem resLaw_close (hlam : 0 < P.lam) (hm : 0 < m) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∀ (k : ℕ) (x : ℝ), (k : ℝ) ≤ x →
      ∑ a ∈ Finset.Ico (0 : ℤ) m, |(S.resLaw m x a).toReal - 1 / m| ≤ θ ^ k * 2 := by
  have hl := P.lam_nonneg
  set s : Finset ℤ := Finset.Ico (0 : ℤ) m with hs
  have hcard : (s.card : ℝ) = m := by simp [hs]
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  set ε : ℝ := (Finset.range m).inf' (Finset.nonempty_range_iff.mpr hm.ne') (fun j => poisW P.lam j)
    with hε
  have hεpos : 0 < ε := by
    rw [hε, Finset.lt_inf'_iff]
    intro j _
    unfold poisW
    positivity
  have hK : ∀ a ∈ s, ∀ r ∈ s, ε ≤ kern m P.lam a r := by
    intro a _ r hr
    refine le_trans ?_ (kern_ge m hl hm hr)
    have hm' : (0 : ℤ) < m := by exact_mod_cast hm
    have hlt : ((r - a) % (m : ℤ)).toNat < m := by
      have h1 := Int.emod_lt_of_pos (r - a) hm'
      have h0 := Int.emod_nonneg (r - a) hm'.ne'
      omega
    exact Finset.inf'_le _ (Finset.mem_range.mpr hlt)
  have hrow : ∀ a ∈ s, ∑ r ∈ s, kern m P.lam a r = 1 := fun a _ => kern_row m hl hm a
  have hcol : ∀ r ∈ s, ∑ a ∈ s, kern m P.lam a r = 1 := fun r hr => kern_col m hl hm hr
  set θ : ℝ := 1 - s.card * ε with hθ
  have hθ1 : θ < 1 := by rw [hθ, hcard]; nlinarith
  have hθ0 : 0 ≤ θ := by
    have h0 : (0 : ℤ) ∈ s := by simp [hs, hm]
    have := hrow 0 h0
    have hle : ∑ r ∈ s, ε ≤ ∑ r ∈ s, kern m P.lam 0 r := Finset.sum_le_sum (fun r hr => hK 0 h0 r hr)
    rw [Finset.sum_const, nsmul_eq_mul, this] at hle
    rw [hθ]; linarith
  set D : ℝ → ℝ := fun y => ∑ a ∈ s, |(S.resLaw m y a).toReal - 1 / m| with hD
  have hp : ∀ y, ∑ a ∈ s, (S.resLaw m y a).toReal = 1 := by
    intro y
    rw [← ENNReal.toReal_sum (fun a _ => S.resLaw_ne_top m y a), S.resLaw_sum m hm y]
    simp
  have hu : (s.card : ℝ) * (1 / m) = 1 := by rw [hcard]; field_simp
  have hstep : ∀ y, 1 ≤ y → D y ≤ θ * D (y - 1) := by
    intro y hy
    have := contraction (kern m P.lam) ε hK hrow hcol (fun a => (S.resLaw m (y - 1) a).toReal)
      (hp (y - 1)) (1 / m) hu
    simp only [hD]
    have e : ∀ r ∈ s, (S.resLaw m y r).toReal
        = ∑ a ∈ s, (S.resLaw m (y - 1) a).toReal * kern m P.lam a r :=
      fun r _ => S.resLaw_step m hm hy r
    rw [Finset.sum_congr rfl (fun r hr => by rw [e r hr])]
    exact this
  have hD2 : ∀ y, D y ≤ 2 := by
    intro y
    simp only [hD]
    calc ∑ a ∈ s, |(S.resLaw m y a).toReal - 1 / m|
        ≤ ∑ a ∈ s, ((S.resLaw m y a).toReal + 1 / m) :=
          Finset.sum_le_sum (fun a _ => by
            have := ENNReal.toReal_nonneg (a := S.resLaw m y a)
            rw [abs_le]; constructor <;> nlinarith [one_div_pos.mpr hmr])
      _ = 2 := by rw [Finset.sum_add_distrib, hp y, Finset.sum_const, nsmul_eq_mul, hu]; norm_num
  refine ⟨θ, hθ0, hθ1, fun k => ?_⟩
  induction k with
  | zero => intro x _; rw [pow_zero, one_mul]; exact hD2 x
  | succ k ih =>
    intro x hx
    push_cast at hx
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h2 := ih (x - 1) (by linarith)
    calc D x ≤ θ * D (x - 1) := hstep x (by linarith)
      _ ≤ θ * (θ ^ k * 2) := mul_le_mul_of_nonneg_left h2 hθ0
      _ = θ ^ (k + 1) * 2 := by ring

theorem resLaw_tendsto (hlam : 0 < P.lam) (hm : 0 < m) {r : ℤ} (hr : r ∈ Finset.Ico (0 : ℤ) m) :
    Tendsto (fun x : ℝ => (S.resLaw m x r).toReal) atTop (𝓝 (1 / m)) := by
  obtain ⟨θ, hθ0, hθ1, hc⟩ := S.resLaw_close m hlam hm
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hlim : Tendsto (fun k : ℕ => θ ^ k * 2) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).mul_const 2
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  refine ⟨k, fun x hx => ?_⟩
  rw [Real.dist_eq]
  have h1 := hc k x hx
  have h2 : |(S.resLaw m x r).toReal - 1 / m|
      ≤ ∑ a ∈ Finset.Ico (0 : ℤ) m, |(S.resLaw m x a).toReal - 1 / m| :=
    Finset.single_le_sum (f := fun a => |(S.resLaw m x a).toReal - 1 / m|)
      (fun a _ => abs_nonneg _) hr
  linarith

lemma res_shift_set (hm : 0 < m) (x : ℝ) (c : ℤ) {r : ℤ} (hr : r ∈ Finset.Ico (0 : ℤ) m) :
    {ω | (S.N x ω + c) % (m : ℤ) = r} = {ω | S.N x ω % (m : ℤ) = (r - c) % (m : ℤ)} := by
  rw [Finset.mem_Ico] at hr
  have hrr : r % (m : ℤ) = r := Int.emod_eq_of_lt hr.1 hr.2
  ext ω
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    have h1 : S.N x ω + c ≡ (r - c) + c [ZMOD (m : ℤ)] := by
      unfold Int.ModEq; rw [h, sub_add_cancel, hrr]
    exact Int.ModEq.add_right_cancel' c h1
  · intro h
    have h1 : S.N x ω ≡ r - c [ZMOD (m : ℤ)] := h
    have h2 := h1.add_right c
    rw [sub_add_cancel] at h2
    unfold Int.ModEq at h2
    rw [h2, hrr]

def shLaw (x : ℝ) (c : ℤ) (a : ℤ) : ℝ≥0∞ := S.ν {ω | (S.N x ω + c) % (m : ℤ) = a}

lemma shLaw_eq (hm : 0 < m) (x : ℝ) (c : ℤ) {r : ℤ} (hr : r ∈ Finset.Ico (0 : ℤ) m) :
    S.shLaw m x c r = S.resLaw m x ((r - c) % (m : ℤ)) := by
  unfold shLaw resLaw
  rw [S.res_shift_set m hm x c hr]

lemma shLaw_ne_top (x : ℝ) (c a : ℤ) : S.shLaw m x c a ≠ ⊤ := measure_ne_top _ _

lemma shLaw_tendsto (hlam : 0 < P.lam) (hm : 0 < m) (c : ℤ) {r : ℤ}
    (hr : r ∈ Finset.Ico (0 : ℤ) m) :
    Tendsto (fun x : ℝ => (S.shLaw m x c r).toReal) atTop (𝓝 (1 / m)) := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hmem : (r - c) % (m : ℤ) ∈ Finset.Ico (0 : ℤ) m :=
    Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ hm'.ne', Int.emod_lt_of_pos _ hm'⟩
  refine (S.resLaw_tendsto m hlam hm hmem).congr (fun x => ?_)
  rw [S.shLaw_eq m hm x c hr]

lemma res_shift_meas (x : ℝ) (c : ℤ) : Measurable[S.𝓕 x] (fun ω => (S.N x ω + c) % (m : ℤ)) :=
  (measurable_of_countable (fun z : ℤ => (z + c) % (m : ℤ))).comp (S.N_adapted x)

lemma res_shift_preimage (hm : 0 < m) (x : ℝ) (c : ℤ) (a : ℤ) :
    S.ν ((fun ω => (S.N x ω + c) % (m : ℤ)) ⁻¹' {a})
      = if a ∈ Finset.Ico (0 : ℤ) m then S.shLaw m x c a else 0 := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  split_ifs with ha
  · rfl
  · have : (fun ω => (S.N x ω + c) % (m : ℤ)) ⁻¹' {a} = ∅ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro h
      apply ha
      rw [Finset.mem_Ico, ← h]
      exact ⟨Int.emod_nonneg _ hm'.ne', Int.emod_lt_of_pos _ hm'⟩
    rw [this, measure_empty]

lemma lintegral_res (hm : 0 < m) (x : ℝ) (c : ℤ) (g : ℤ → ℝ≥0∞) :
    ∫⁻ ω, g ((S.N x ω + c) % (m : ℤ)) ∂S.ν
      = ∑ a ∈ Finset.Ico (0 : ℤ) m, S.shLaw m x c a * g a := by
  have hX : Measurable (fun ω => (S.N x ω + c) % (m : ℤ)) :=
    (S.res_shift_meas m x c).mono (S.𝓕.le x) le_rfl
  rw [S.lintegral_comp hX g]
  simp_rw [S.res_shift_preimage m hm x c]
  rw [tsum_eq_sum (s := Finset.Ico (0 : ℤ) m) (fun a ha => by rw [if_neg ha, zero_mul])]
  exact Finset.sum_congr rfl (fun a ha => by rw [if_pos ha])

lemma lintegral_Y (hm : 0 < m) {L : ℝ} (hL : 0 ≤ L) {t : ℝ} (ht : L ≤ t) (c : ℤ)
    (Φ : ℤ → ℝ≥0∞) :
    ∫⁻ ω, Φ (S.N t ω - (m : ℤ) * ((S.N (t - L) ω + c) / (m : ℤ))) ∂S.ν
      = ∑ ρ ∈ Finset.Ico (0 : ℤ) m, S.shLaw m (t - L) c ρ *
          ∑' d : ℕ, ENNReal.ofReal (poisW (P.lam * L) d) * Φ (ρ - c + d) := by
  have hv : t - L ≤ t := by linarith
  have key := S.lintegral_incr (by linarith : 0 ≤ t - L) hv
    (X := fun ω => (S.N (t - L) ω + c) % (m : ℤ))
    (S.res_shift_meas m (t - L) c) (fun a (d : ℕ) => Φ (a - c + d))
  have e1 : ∫⁻ ω, Φ (S.N t ω - (m : ℤ) * ((S.N (t - L) ω + c) / (m : ℤ))) ∂S.ν
      = ∫⁻ ω, (fun a (d : ℕ) => Φ (a - c + d)) ((fun ω => (S.N (t - L) ω + c) % (m : ℤ)) ω)
          (S.N t ω - S.N (t - L) ω).toNat ∂S.ν := by
    refine lintegral_congr (fun ω => ?_)
    simp only
    congr 1
    rw [Int.toNat_of_nonneg (S.incr_nonneg hv ω)]
    have := Int.emod_add_mul_ediv (S.N (t - L) ω + c) (m : ℤ)
    linarith
  rw [e1, key]
  simp_rw [S.res_shift_preimage m hm (t - L) c]
  rw [tsum_eq_sum (s := Finset.Ico (0 : ℤ) m) (fun a ha => by rw [if_neg ha, zero_mul])]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [if_pos ha, show t - (t - L) = L by ring]

lemma lintegral_res_le (hm : 0 < m) (x : ℝ) (c : ℤ) :
    ∫⁻ ω, ENNReal.ofReal ((((S.N x ω + c) % (m : ℤ) : ℤ)) : ℝ) ∂S.ν ≤ ENNReal.ofReal m := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  calc ∫⁻ ω, ENNReal.ofReal ((((S.N x ω + c) % (m : ℤ) : ℤ)) : ℝ) ∂S.ν
      ≤ ∫⁻ _ω, ENNReal.ofReal m ∂S.ν := lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal (by
        have := Int.emod_lt_of_pos (S.N x ω + c) hm'
        have h2 : (((S.N x ω + c) % (m : ℤ) : ℤ) : ℝ) < ((m : ℤ) : ℝ) := by exact_mod_cast this
        push_cast at h2
        linarith))
    _ = ENNReal.ofReal m := by rw [lintegral_const, measure_univ, mul_one]

lemma lintegral_ordIncr (hm : 0 < m) {x y : ℝ} (hxy : x ≤ y) (c : ℤ) :
    ∫⁻ ω, ENNReal.ofReal ((((m : ℤ) * ((S.N y ω + c) / (m : ℤ) - (S.N x ω + c) / (m : ℤ)) : ℤ)
      : ℝ)) ∂S.ν + ∫⁻ ω, ENNReal.ofReal ((((S.N y ω + c) % (m : ℤ) : ℤ)) : ℝ) ∂S.ν
      = ENNReal.ofReal (P.lam * (y - x))
        + ∫⁻ ω, ENNReal.ofReal ((((S.N x ω + c) % (m : ℤ) : ℤ)) : ℝ) ∂S.ν := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hpt : ∀ ω, ENNReal.ofReal ((((m : ℤ) * ((S.N y ω + c) / (m : ℤ)
        - (S.N x ω + c) / (m : ℤ)) : ℤ) : ℝ))
        + ENNReal.ofReal ((((S.N y ω + c) % (m : ℤ) : ℤ)) : ℝ)
      = ENNReal.ofReal (((S.N y ω - S.N x ω : ℤ) : ℝ))
        + ENNReal.ofReal ((((S.N x ω + c) % (m : ℤ) : ℤ)) : ℝ) := by
    intro ω
    set Ny := S.N y ω
    set Nx := S.N x ω
    set Oy := (Ny + c) / (m : ℤ)
    set Ox := (Nx + c) / (m : ℤ)
    set ry := (Ny + c) % (m : ℤ)
    set rx := (Nx + c) % (m : ℤ)
    have h1 : ry + (m : ℤ) * Oy = Ny + c := Int.emod_add_mul_ediv _ _
    have h2 : rx + (m : ℤ) * Ox = Nx + c := Int.emod_add_mul_ediv _ _
    have hr1 : 0 ≤ ry := Int.emod_nonneg _ hm'.ne'
    have hr2 : 0 ≤ rx := Int.emod_nonneg _ hm'.ne'
    have hn : 0 ≤ Ny - Nx := S.incr_nonneg hxy ω
    have hOO : Ox ≤ Oy := Int.ediv_le_ediv hm' (by linarith [S.N_mono ω hxy])
    have hmo : (0 : ℤ) ≤ (m : ℤ) * (Oy - Ox) := mul_nonneg hm'.le (by linarith)
    have hz : (m : ℤ) * (Oy - Ox) + ry = (Ny - Nx) + rx := by linear_combination h1 - h2
    rw [← ENNReal.ofReal_add (by exact_mod_cast hmo) (by exact_mod_cast hr1),
      ← ENNReal.ofReal_add (by exact_mod_cast hn) (by exact_mod_cast hr2)]
    congr 1
    exact_mod_cast hz
  have hmeasA : Measurable (fun ω => ENNReal.ofReal ((((m : ℤ) * ((S.N y ω + c) / (m : ℤ)
        - (S.N x ω + c) / (m : ℤ)) : ℤ) : ℝ))) := by
    have h := (measurable_of_countable (fun p : ℤ × ℤ => ENNReal.ofReal ((((m : ℤ) * ((p.1 + c) / (m : ℤ)
        - (p.2 + c) / (m : ℤ)) : ℤ) : ℝ)))).comp ((S.N_meas y).prodMk (S.N_meas x))
    exact h
  have hmeasB : Measurable (fun ω => ENNReal.ofReal (((S.N y ω - S.N x ω : ℤ) : ℝ))) := by
    have h := (measurable_of_countable (fun p : ℤ × ℤ => ENNReal.ofReal (((p.1 - p.2 : ℤ) : ℝ)))).comp
      ((S.N_meas y).prodMk (S.N_meas x))
    exact h
  have hint := lintegral_congr (μ := S.ν) hpt
  rw [lintegral_add_left hmeasA, lintegral_add_left hmeasB, S.lintegral_incr_val hxy] at hint
  exact hint

lemma lintegral_res_val (hm : 0 < m) (x : ℝ) (c : ℤ) :
    ∫⁻ ω, ENNReal.ofReal ((((S.N x ω + c) % (m : ℤ) : ℤ)) : ℝ) ∂S.ν
      = ∑ a ∈ Finset.Ico (0 : ℤ) m, S.shLaw m x c a * ENNReal.ofReal (a : ℝ) :=
  S.lintegral_res m hm x c (fun a => ENNReal.ofReal (a : ℝ))

end Residue

lemma N_joint : Measurable (fun p : S.Ω × ℝ => S.N p.2 p.1) := by
  set g : ℕ → S.Ω × ℝ → ℤ := fun k p => S.N ((⌈p.2 * 2 ^ k⌉ : ℤ) / (2 : ℝ) ^ k) p.1 with hg
  have hgm : ∀ k, Measurable (g k) := by
    intro k
    have h1 : Measurable (fun q : S.Ω × ℤ => S.N ((q.2 : ℝ) / (2 : ℝ) ^ k) q.1) :=
      measurable_from_prod_countable_left (fun z => by exact S.N_meas ((z : ℝ) / (2 : ℝ) ^ k))
    exact h1.comp (measurable_fst.prodMk (Int.measurable_ceil.comp (measurable_snd.mul_const _)))
  refine measurable_of_tendsto_metrizable hgm (tendsto_pi_nhds.mpr (fun p => ?_))
  refine tendsto_nhds_of_eventually_eq ?_
  obtain ⟨δ, hδ, hN⟩ := S.N_rcont p.1 p.2
  have hlim : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with k hk
  have h2 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hle : p.2 ≤ (⌈p.2 * 2 ^ k⌉ : ℤ) / (2 : ℝ) ^ k := by
    rw [le_div_iff₀ h2]; exact Int.le_ceil _
  have hlt : (⌈p.2 * 2 ^ k⌉ : ℤ) / (2 : ℝ) ^ k < p.2 + δ := by
    rw [div_lt_iff₀ h2]
    have h3 := Int.ceil_lt_add_one (p.2 * 2 ^ k)
    have h4 : (1 / 2 : ℝ) ^ k * (2 : ℝ) ^ k = 1 := by
      rw [← mul_pow]; norm_num
    nlinarith
  exact hN _ hle hlt

end DemandSpace

end TwoStageRnQ

open Finset
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace Prop1

def ctrl (R1 R2 : ℤ) (Q n : ℕ+) : ClassicalControls := ⟨(R1, R2, Q, n, 0), Q.pos⟩

section Defs

variable (Q n : ℕ+) (R1 R2 : ℤ)

def cz : ℤ := (R2 - R1) + (((n : ℕ) : ℤ) - 1) * ((Q : ℕ) : ℤ)

def sz : ℤ := R1 + ((Q : ℕ) : ℤ)

def mN : ℕ := (n : ℕ) * (Q : ℕ)

def IPf (y : ℤ) : ℤ := sz Q R1 - y % ((Q : ℕ) : ℤ) - ((Q : ℕ) : ℤ) * max (y / ((Q : ℕ) : ℤ)) 0

def Wf (y : ℤ) : ℤ := ((Q : ℕ) : ℤ) * max (-(y / ((Q : ℕ) : ℤ))) 0

lemma mN_pos : 0 < mN Q n := Nat.mul_pos n.pos Q.pos

lemma mN_cast : ((mN Q n : ℕ) : ℤ) = ((n : ℕ) : ℤ) * ((Q : ℕ) : ℤ) := by
  unfold mN; push_cast; ring

lemma mN_castR : ((mN Q n : ℕ) : ℝ) = ((n : ℕ) : ℝ) * ((Q : ℕ) : ℝ) := by
  unfold mN; push_cast; ring

end Defs

section Comb

lemma cost_split (h1 h2 p x d : ℝ) :
    h1 * max x 0 + h2 * ((x + d) + max (-x) 0) + p * max (-x) 0 = phi (h1 + h2) p x + h2 * d := by
  unfold phi
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx, max_eq_right (by linarith : -x ≤ 0)]; ring
  · rw [max_eq_right hx, max_eq_left (by linarith : 0 ≤ -x)]; ring

lemma sum_Ico_int {β : Type*} [AddCommMonoid β] (M : ℕ) (f : ℤ → β) :
    ∑ a ∈ Finset.Ico (0 : ℤ) M, f a = ∑ k ∈ Finset.range M, f k := by
  refine Finset.sum_nbij' (fun a => a.toNat) (fun k => (k : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_Ico] at ha
    rw [Finset.mem_range]; omega
  · intro k hk
    rw [Finset.mem_range] at hk
    rw [Finset.mem_Ico]; omega
  · intro a ha
    rw [Finset.mem_Ico] at ha
    omega
  · intro k _
    simp
  · intro a ha
    rw [Finset.mem_Ico] at ha
    show f a = f ((a.toNat : ℕ) : ℤ)
    rw [Int.toNat_of_nonneg ha.1]

lemma sum_range_mul' {β : Type*} [AddCommMonoid β] (f : ℕ → β) (n q : ℕ) :
    ∑ k ∈ Finset.range (n * q), f k = ∑ κ ∈ Finset.range n, ∑ u ∈ Finset.range q, f (κ * q + u) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

lemma hermite (q : ℕ) (hq : 0 < q) (x : ℤ) :
    ∑ u ∈ Finset.range q, (x + u) / (q : ℤ) = x := by
  have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have step : ∀ y : ℤ, ∑ u ∈ Finset.range q, (y + 1 + u) / (q : ℤ)
      = ∑ u ∈ Finset.range q, (y + u) / (q : ℤ) + 1 := by
    intro y
    have h1 := Finset.sum_range_succ' (fun u : ℕ => (y + u) / (q : ℤ)) q
    have h2 := Finset.sum_range_succ (fun u : ℕ => (y + u) / (q : ℤ)) q
    have h3 : (y + (q : ℤ)) / (q : ℤ) = y / (q : ℤ) + 1 := by
      have := Int.add_mul_ediv_left y 1 hq'
      simpa using this
    have e : ∀ u : ℕ, (y + 1 + u) / (q : ℤ) = (y + ((u + 1 : ℕ) : ℤ)) / (q : ℤ) := by
      intro u; push_cast; ring_nf
    simp_rw [e]
    simp only [Nat.cast_zero, add_zero] at h1
    rw [h3] at h2
    linarith
  have base : ∑ u ∈ Finset.range q, ((0 : ℤ) + u) / (q : ℤ) = 0 := by
    refine Finset.sum_eq_zero (fun u hu => ?_)
    rw [Finset.mem_range] at hu
    rw [zero_add]
    exact Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast hu)
  induction x using Int.induction_on with
  | zero => exact base
  | succ i ih => rw [step, ih]
  | pred i ih =>
    have := step (-(i : ℤ) - 1)
    rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring, ih] at this
    linarith

variable (Q n : ℕ+) (R1 R2 : ℤ)

lemma decomp {β : Type*} [AddCommMonoid β] (G : ℤ → β) (d : ℤ) :
    ∑ ρ ∈ Finset.Ico (0 : ℤ) (mN Q n), G (ρ - cz Q n R1 R2 + d)
      = ∑ j ∈ Finset.range n, ∑ u ∈ Finset.range Q,
          G ((u : ℤ) - ((R2 - R1) + (j : ℤ) * ((Q : ℕ) : ℤ) - d)) := by
  rw [sum_Ico_int, mN, sum_range_mul', ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun u _ => ?_))
  rw [Finset.mem_range] at hj
  congr 1
  unfold cz
  have h1 : (((n : ℕ) - 1 - j : ℕ) : ℤ) = ((n : ℕ) : ℤ) - 1 - j := by
    have : j ≤ (n : ℕ) - 1 := by omega
    have h2 : 1 ≤ (n : ℕ) := n.pos
    push_cast [Nat.cast_sub this, Nat.cast_sub h2]
    ring
  push_cast
  rw [h1]
  ring

lemma sum_IPf {β : Type*} [AddCommMonoid β] (F : ℤ → β) (w : ℤ) :
    ∑ u ∈ Finset.range Q, F (IPf Q R1 ((u : ℤ) - w))
      = ∑ v ∈ Finset.range Q, F (sz Q R1 - max (-w) 0 - v) := by
  have hq : (0 : ℤ) < ((Q : ℕ) : ℤ) := by exact_mod_cast Q.pos
  unfold IPf
  rcases le_or_gt 0 w with hw | hw
  ·
    have hmax : ∀ u ∈ Finset.range Q, max (((u : ℤ) - w) / ((Q : ℕ) : ℤ)) 0 = 0 := by
      intro u hu
      rw [Finset.mem_range] at hu
      apply max_eq_right
      have : ((u : ℤ) - w) < 1 * ((Q : ℕ) : ℤ) := by
        have : (u : ℤ) < ((Q : ℕ) : ℤ) := by exact_mod_cast hu
        linarith
      have := Int.ediv_lt_of_lt_mul hq this
      omega
    rw [Finset.sum_congr rfl (fun u hu => by rw [hmax u hu, mul_zero, sub_zero])]
    rw [max_eq_right (by linarith : -w ≤ 0), sub_zero]
    refine Finset.sum_nbij' (fun u => (((u : ℤ) - w) % ((Q : ℕ) : ℤ)).toNat)
      (fun v => (((v : ℤ) + w) % ((Q : ℕ) : ℤ)).toNat) ?_ ?_ ?_ ?_ ?_
    · intro u _
      rw [Finset.mem_range]
      have h1 := Int.emod_lt_of_pos ((u : ℤ) - w) hq
      have h0 := Int.emod_nonneg ((u : ℤ) - w) hq.ne'
      omega
    · intro v _
      rw [Finset.mem_range]
      have h1 := Int.emod_lt_of_pos ((v : ℤ) + w) hq
      have h0 := Int.emod_nonneg ((v : ℤ) + w) hq.ne'
      omega
    · intro u hu
      rw [Finset.mem_range] at hu
      have h0 := Int.emod_nonneg ((u : ℤ) - w) hq.ne'
      rw [Int.toNat_of_nonneg h0, Int.emod_add_emod, sub_add_cancel,
        Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hu)]
      simp
    · intro v hv
      rw [Finset.mem_range] at hv
      have h0 := Int.emod_nonneg ((v : ℤ) + w) hq.ne'
      rw [Int.toNat_of_nonneg h0, Int.emod_sub_emod, add_sub_cancel_right,
        Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hv)]
      simp
    · intro u _
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hq.ne')]
  ·
    rw [max_eq_left (by linarith : 0 ≤ -w)]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    have hy : 0 ≤ (u : ℤ) - w := by have : (0 : ℤ) ≤ u := by positivity
                                    linarith
    have hpos : 0 ≤ ((u : ℤ) - w) / ((Q : ℕ) : ℤ) := Int.ediv_nonneg hy hq.le
    rw [max_eq_left hpos]
    congr 1
    have hd := Int.emod_add_mul_ediv ((u : ℤ) - w) ((Q : ℕ) : ℤ)
    linarith

lemma sum_Wf (w : ℤ) :
    ∑ u ∈ Finset.range Q, Wf Q ((u : ℤ) - w) = ((Q : ℕ) : ℤ) * max w 0 := by
  have hq : (0 : ℤ) < ((Q : ℕ) : ℤ) := by exact_mod_cast Q.pos
  unfold Wf
  rw [← Finset.mul_sum]
  congr 1
  rcases le_or_gt w 0 with hw | hw
  · rw [max_eq_right hw]
    refine Finset.sum_eq_zero (fun u _ => ?_)
    have hy : 0 ≤ (u : ℤ) - w := by have : (0 : ℤ) ≤ u := by positivity
                                    linarith
    have hpos : 0 ≤ ((u : ℤ) - w) / ((Q : ℕ) : ℤ) := Int.ediv_nonneg hy hq.le
    exact max_eq_right (by linarith)
  · rw [max_eq_left hw.le]
    have hneg : ∀ u ∈ Finset.range Q, max (-(((u : ℤ) - w) / ((Q : ℕ) : ℤ))) 0
        = -(((u : ℤ) - w) / ((Q : ℕ) : ℤ)) := by
      intro u hu
      rw [Finset.mem_range] at hu
      apply max_eq_left
      have : ((u : ℤ) - w) < 1 * ((Q : ℕ) : ℤ) := by
        have : (u : ℤ) < ((Q : ℕ) : ℤ) := by exact_mod_cast hu
        linarith
      have := Int.ediv_lt_of_lt_mul hq this
      omega
    rw [Finset.sum_congr rfl hneg, Finset.sum_neg_distrib]
    have := hermite (Q : ℕ) Q.pos (-w)
    have e : ∀ u : ℕ, ((u : ℤ) - w) / ((Q : ℕ) : ℤ) = (-w + u) / ((Q : ℕ) : ℤ) := by
      intro u; ring_nf
    simp_rw [e]
    rw [this, neg_neg]

end Comb

end Prop1

end TwoStageRnQ

open Finset
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace Prop1

open TwoStageRnQ.Prop1

section Pathwise

variable {P : Params} (S : DemandSpace P) (R1 R2 : ℤ) (Q n : ℕ+)

lemma reqCount_eq (t : ℝ) (ω : S.Ω) :
    Classical'.reqCount S (ctrl R1 R2 Q n) t ω = S.N t ω / ((Q : ℕ) : ℤ) := by
  show ⌊((S.N t ω : ℤ) : ℝ) / (((Q : ℕ)) : ℝ)⌋ = _
  rw [Int.floor_div_natCast, Int.floor_intCast]

lemma ordCount_eq (t : ℝ) (ω : S.Ω) :
    Classical'.ordCount S (ctrl R1 R2 Q n) t ω
      = (S.N t ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ) := by
  show ⌊(((S.N t ω : ℤ) : ℝ) + ((R2 - R1 : ℤ) : ℝ) - ((0 : ℕ) : ℝ)
      + (((n : ℕ) : ℝ) - 1) * ((Q : ℕ) : ℝ)) / (((n : ℕ) : ℝ) * ((Q : ℕ) : ℝ))⌋ = _
  have e1 : ((S.N t ω : ℤ) : ℝ) + ((R2 - R1 : ℤ) : ℝ) - ((0 : ℕ) : ℝ)
      + (((n : ℕ) : ℝ) - 1) * ((Q : ℕ) : ℝ) = ((S.N t ω + cz Q n R1 R2 : ℤ) : ℝ) := by
    unfold cz; push_cast; ring
  rw [e1, ← mN_castR, Int.floor_div_natCast, Int.floor_intCast]

lemma min_eq (b O : ℤ) :
    min (b / ((Q : ℕ) : ℤ)) (((n : ℕ) : ℤ) * O)
      = ((n : ℕ) : ℤ) * O + min ((b - ((mN Q n : ℕ) : ℤ) * O) / ((Q : ℕ) : ℤ)) 0 := by
  have hq : ((Q : ℕ) : ℤ) ≠ 0 := by exact_mod_cast Q.pos.ne'
  have hb : b = (b - ((mN Q n : ℕ) : ℤ) * O) + ((Q : ℕ) : ℤ) * (((n : ℕ) : ℤ) * O) := by
    rw [mN_cast]; ring
  have hA : b / ((Q : ℕ) : ℤ) = (b - ((mN Q n : ℕ) : ℤ) * O) / ((Q : ℕ) : ℤ) + ((n : ℕ) : ℤ) * O := by
    conv_lhs => rw [hb]
    exact Int.add_mul_ediv_left _ _ hq
  rw [hA]
  rcases le_total ((b - ((mN Q n : ℕ) : ℤ) * O) / ((Q : ℕ) : ℤ)) 0 with h | h
  · rw [min_eq_left (by linarith), min_eq_left h]; ring
  · rw [min_eq_right (by linarith), min_eq_right h]; ring

lemma Qmin_eq (b O : ℤ) :
    ((Q : ℕ) : ℤ) * min (b / ((Q : ℕ) : ℤ)) (((n : ℕ) : ℤ) * O)
      = b - b % ((Q : ℕ) : ℤ)
        - ((Q : ℕ) : ℤ) * max ((b - ((mN Q n : ℕ) : ℤ) * O) / ((Q : ℕ) : ℤ)) 0 := by
  have hq : ((Q : ℕ) : ℤ) ≠ 0 := by exact_mod_cast Q.pos.ne'
  have hb : b = (b - ((mN Q n : ℕ) : ℤ) * O) + ((Q : ℕ) : ℤ) * (((n : ℕ) : ℤ) * O) := by
    rw [mN_cast]; ring
  have hA : b / ((Q : ℕ) : ℤ) = (b - ((mN Q n : ℕ) : ℤ) * O) / ((Q : ℕ) : ℤ) + ((n : ℕ) : ℤ) * O := by
    conv_lhs => rw [hb]
    exact Int.add_mul_ediv_left _ _ hq
  have hd := Int.emod_add_mul_ediv b ((Q : ℕ) : ℤ)
  rw [min_eq, mN_cast] at *
  rcases le_total ((b - ((n : ℕ) : ℤ) * ((Q : ℕ) : ℤ) * O) / ((Q : ℕ) : ℤ)) 0 with h | h
  · rw [min_eq_left h, max_eq_right h]
    rw [hA] at hd
    linear_combination hd
  · rw [min_eq_right h, max_eq_left h]
    rw [hA] at hd
    linear_combination hd

lemma IL1_eq (t : ℝ) (ω : S.Ω) :
    netInv P.L1 (Classical'.x1 S (ctrl R1 R2 Q n)) (Classical'.U1 S (ctrl R1 R2 Q n)) S.N t ω
      = IPf Q R1 (S.N (t - P.L1) ω - ((mN Q n : ℕ) : ℤ)
          * ((S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)))
        - (S.N t ω - S.N (t - P.L1) ω) := by
  show R1 + ((Q : ℕ) : ℤ) + ((Q : ℕ) : ℤ) * min (Classical'.reqCount S (ctrl R1 R2 Q n) (t - P.L1) ω)
      (((n : ℕ) : ℤ) * Classical'.ordCount S (ctrl R1 R2 Q n) (t - P.L1 - P.L2) ω) - S.N t ω = _
  rw [reqCount_eq, ordCount_eq, Qmin_eq]
  unfold IPf sz
  have hd := Int.emod_add_mul_ediv (S.N (t - P.L1) ω - ((mN Q n : ℕ) : ℤ)
          * ((S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) ((Q : ℕ) : ℤ)
  have he : (S.N (t - P.L1) ω - ((mN Q n : ℕ) : ℤ)
          * ((S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) % ((Q : ℕ) : ℤ)
      = S.N (t - P.L1) ω % ((Q : ℕ) : ℤ) := by
    rw [mN_cast]
    have : S.N (t - P.L1) ω - ((n : ℕ) : ℤ) * ((Q : ℕ) : ℤ)
          * ((S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / (((n : ℕ) : ℤ) * ((Q : ℕ) : ℤ)))
        = S.N (t - P.L1) ω + ((Q : ℕ) : ℤ) * (-(((n : ℕ) : ℤ)
          * ((S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / (((n : ℕ) : ℤ) * ((Q : ℕ) : ℤ))))) := by
      ring
    rw [this, Int.add_mul_emod_self_left]
  rw [he]
  ring

lemma IL2_eq (t : ℝ) (ω : S.Ω) :
    netInv P.L2 (Classical'.x2 S (ctrl R1 R2 Q n)) (Classical'.U2 S (ctrl R1 R2 Q n)) S.N t ω
      = netInv P.L1 (Classical'.x1 S (ctrl R1 R2 Q n)) (Classical'.U1 S (ctrl R1 R2 Q n)) S.N t ω
        + (((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)
            - (S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))
          + Wf Q (S.N (t - P.L1) ω - ((mN Q n : ℕ) : ℤ)
            * ((S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)))) := by
  show R1 + ((Q : ℕ) : ℤ) + ((0 : ℕ) : ℤ) + ((n : ℕ) : ℤ) * ((Q : ℕ) : ℤ)
      * Classical'.ordCount S (ctrl R1 R2 Q n) (t - P.L2) ω - S.N t ω
    = R1 + ((Q : ℕ) : ℤ) + ((Q : ℕ) : ℤ) * min (Classical'.reqCount S (ctrl R1 R2 Q n) (t - P.L1) ω)
      (((n : ℕ) : ℤ) * Classical'.ordCount S (ctrl R1 R2 Q n) (t - P.L1 - P.L2) ω) - S.N t ω + _
  rw [reqCount_eq, ordCount_eq, ordCount_eq, min_eq]
  unfold Wf
  rw [mN_cast]
  set O1 := (S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / (((n : ℕ) : ℤ) * ((Q : ℕ) : ℤ))
  set O2 := (S.N (t - P.L2) ω + cz Q n R1 R2) / (((n : ℕ) : ℤ) * ((Q : ℕ) : ℤ))
  set z := (S.N (t - P.L1) ω - ((n : ℕ) : ℤ) * ((Q : ℕ) : ℤ) * O1) / ((Q : ℕ) : ℤ)
  rcases le_total z 0 with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]; push_cast; ring
  · rw [min_eq_right h, max_eq_right (by linarith)]; push_cast; ring

lemma cI_eq (t : ℝ) (ω : S.Ω) :
    Classical'.cI S (ctrl R1 R2 Q n) t ω
      = phi (P.h1 + P.h2) P.p (((IPf Q R1 (S.N (t - P.L1) ω - ((mN Q n : ℕ) : ℤ)
            * ((S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) : ℤ) : ℝ)
          - ((S.N t ω - S.N (t - P.L1) ω : ℤ) : ℝ))
        + P.h2 * (((((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)
            - (S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) : ℤ) : ℝ)
        + P.h2 * ((Wf Q (S.N (t - P.L1) ω - ((mN Q n : ℕ) : ℤ)
            * ((S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) : ℤ) : ℝ) := by
  unfold Classical'.cI costRate
  rw [IL2_eq, IL1_eq]
  push_cast
  rw [add_assoc (phi _ _ _), ← mul_add, ← cost_split]

lemma QmatchCount_eq (t : ℝ) (ω : S.Ω) :
    ((Q : ℕ) : ℤ) * Classical'.matchCount S (ctrl R1 R2 Q n) t ω
      = S.N t ω - S.N t ω % ((Q : ℕ) : ℤ) - ((Q : ℕ) : ℤ) * max ((S.N t ω - ((mN Q n : ℕ) : ℤ)
          * ((S.N (t - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) / ((Q : ℕ) : ℤ)) 0 := by
  show ((Q : ℕ) : ℤ) * min (Classical'.reqCount S (ctrl R1 R2 Q n) t ω)
      (((n : ℕ) : ℤ) * Classical'.ordCount S (ctrl R1 R2 Q n) (t - P.L2) ω) = _
  rw [reqCount_eq, ordCount_eq, Qmin_eq]

end Pathwise

end Prop1

end TwoStageRnQ

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

section ClassicalMono

variable {P : Params} (S : DemandSpace P) (c : ClassicalControls)

lemma Classical'.reqCount_mono (ω : S.Ω) : Monotone (fun t => Classical'.reqCount S c t ω) := by
  intro s t hst
  unfold Classical'.reqCount
  apply Int.floor_mono
  have hQ : (0 : ℝ) < ((c.1.2.2.1 : ℕ) : ℝ) := by exact_mod_cast c.1.2.2.1.pos
  have := S.N_mono ω hst
  gcongr

lemma Classical'.ordCount_mono (ω : S.Ω) : Monotone (fun t => Classical'.ordCount S c t ω) := by
  intro s t hst
  unfold Classical'.ordCount
  apply Int.floor_mono
  have hQ : (0 : ℝ) < ((c.1.2.2.1 : ℕ) : ℝ) := by exact_mod_cast c.1.2.2.1.pos
  have hn : (0 : ℝ) < ((c.1.2.2.2.1 : ℕ) : ℝ) := by exact_mod_cast c.1.2.2.2.1.pos
  have := S.N_mono ω hst
  have h' : ((S.N s ω : ℤ) : ℝ) ≤ ((S.N t ω : ℤ) : ℝ) := by exact_mod_cast this
  gcongr

lemma Classical'.matchCount_mono (ω : S.Ω) :
    Monotone (fun t => Classical'.matchCount S c t ω) := by
  intro s t hst
  unfold Classical'.matchCount Classical'.recvCount
  have h1 := Classical'.reqCount_mono S c ω hst
  have h2 := Classical'.ordCount_mono S c ω (by linarith : s - P.L2 ≤ t - P.L2)
  have hn : (0 : ℤ) ≤ ((c.1.2.2.2.1 : ℕ) : ℤ) := by positivity
  exact min_le_min h1 (mul_le_mul_of_nonneg_left h2 hn)

end ClassicalMono

theorem classical_ship_le_lot_pf (P : Params) (S : DemandSpace P) (c : ClassicalControls) :
    classicalShipCost P S c ≤ classicalLotCost P S c := by
  unfold classicalShipCost classicalLotCost
  refine longRunCost_mono _ _ (fun T hT ω => ?_)
  have hQ : (0 : ℤ) < ((c.1.2.2.1 : ℕ) : ℤ) := by exact_mod_cast c.1.2.2.1.pos
  have hn : (0 : ℤ) < ((c.1.2.2.2.1 : ℕ) : ℤ) := by exact_mod_cast c.1.2.2.2.1.pos
  have j1 : (jumpCount (fun t => Classical'.U1 S c t ω) T : ℝ)
      ≤ ((Classical'.matchCount S c T ω - Classical'.matchCount S c 0 ω : ℤ) : ℝ) :=
    jumpCount_mul_le (g := fun t => Classical'.matchCount S c t ω)
      (Classical'.matchCount_mono S c ω) _ hQ hT
  have j2 : (jumpCount (fun t => Classical'.U2 S c t ω) T : ℝ)
      ≤ ((Classical'.ordCount S c T ω - Classical'.ordCount S c 0 ω : ℤ) : ℝ) :=
    jumpCount_mul_le (g := fun t => Classical'.ordCount S c t ω)
      (Classical'.ordCount_mono S c ω) _ (mul_pos hn hQ) hT
  have k1 := P.K1_nonneg
  have k2 := P.K2_nonneg
  have := mul_le_mul_of_nonneg_left j1 k1
  have := mul_le_mul_of_nonneg_left j2 k2
  linarith

end TwoStageRnQ

open Finset
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace Prop1

section Bounds

variable (Q n : ℕ+) (R1 R2 : ℤ)

lemma Qmax_le (y : ℤ) : ((Q : ℕ) : ℤ) * max (y / ((Q : ℕ) : ℤ)) 0 ≤ |y| := by
  have hq : (0 : ℤ) < ((Q : ℕ) : ℤ) := by exact_mod_cast Q.pos
  rcases le_total (y / ((Q : ℕ) : ℤ)) 0 with h | h
  · rw [max_eq_right h, mul_zero]; exact abs_nonneg y
  · rw [max_eq_left h]; exact (Int.mul_ediv_self_le hq.ne').trans (le_abs_self y)

lemma Qmax_nonneg (y : ℤ) : 0 ≤ ((Q : ℕ) : ℤ) * max (y / ((Q : ℕ) : ℤ)) 0 :=
  mul_nonneg (by positivity) (le_max_right _ _)

lemma IPf_abs (y : ℤ) : |IPf Q R1 y| ≤ |sz Q R1| + ((Q : ℕ) : ℤ) + |y| := by
  have hq : (0 : ℤ) < ((Q : ℕ) : ℤ) := by exact_mod_cast Q.pos
  unfold IPf
  have h0 := Int.emod_nonneg y hq.ne'
  have h1 := Int.emod_lt_of_pos y hq
  have h3 := Qmax_nonneg Q y
  have h4 := Qmax_le Q y
  rw [abs_le]
  constructor
  · have := neg_abs_le (sz Q R1); linarith
  · have := le_abs_self (sz Q R1); linarith

lemma Wf_nonneg (y : ℤ) : 0 ≤ Wf Q y := by
  unfold Wf; exact mul_nonneg (by positivity) (le_max_right _ _)

lemma Wf_le (y : ℤ) : Wf Q y ≤ |y| + ((Q : ℕ) : ℤ) := by
  have hq : (0 : ℤ) < ((Q : ℕ) : ℤ) := by exact_mod_cast Q.pos
  unfold Wf
  rcases le_total (-(y / ((Q : ℕ) : ℤ))) 0 with h | h
  · rw [max_eq_right h, mul_zero]; positivity
  · rw [max_eq_left h, mul_neg]
    have h5 : y < ((Q : ℕ) : ℤ) * (y / ((Q : ℕ) : ℤ)) + ((Q : ℕ) : ℤ) :=
      Int.lt_mul_ediv_self_add hq
    have := neg_abs_le y
    linarith

lemma abs_cast_le_add (a : ℤ) (d : ℕ) : |((a + (d : ℤ) : ℤ) : ℝ)| ≤ |(a : ℝ)| + (d : ℝ) := by
  have h1 := abs_add_le (a : ℝ) (d : ℝ)
  have h2 : |(d : ℝ)| = d := abs_of_nonneg (Nat.cast_nonneg d)
  push_cast
  linarith

lemma pint_A (P : Params) (ρ : ℤ) :
    PInt P.mu2 (fun d : ℕ => P.lossDown ((IPf Q R1 (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ)
      + P.h2 * ((Wf Q (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ)) := by
  have hμ := P.mu2_nonneg
  set K : ℝ := P.h1 + P.h2 + P.p with hKdef
  have hK : 0 ≤ K := add_nonneg P.a_nonneg P.p_nonneg
  set a : ℝ := |((ρ - cz Q n R1 R2 : ℤ) : ℝ)| with ha
  set b : ℝ := |((sz Q R1 : ℤ) : ℝ)| with hb
  refine PInt.of_abs_le hμ ((pint_const (K * (b + ((Q : ℕ) : ℝ) + a + P.mu1)
    + P.h2 * (a + ((Q : ℕ) : ℝ)))).add hμ (pint_nat.const_mul (K + P.h2))) (fun d => ?_)
  have hy := abs_cast_le_add (ρ - cz Q n R1 R2) d
  have hIP : |((IPf Q R1 (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ)|
      ≤ b + ((Q : ℕ) : ℝ) + |((ρ - cz Q n R1 R2 + (d : ℤ) : ℤ) : ℝ)| := by
    have := IPf_abs Q R1 (ρ - cz Q n R1 R2 + d)
    have h' : (((|IPf Q R1 (ρ - cz Q n R1 R2 + d)| : ℤ)) : ℝ)
        ≤ (((|sz Q R1| + ((Q : ℕ) : ℤ) + |ρ - cz Q n R1 R2 + d|) : ℤ) : ℝ) := by exact_mod_cast this
    push_cast at h' ⊢
    simpa [hb] using h'
  have hL := P.lossDown_le ((IPf Q R1 (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ)
  have hL0 := P.lossDown_nonneg ((IPf Q R1 (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ)
  have hW : ((Wf Q (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ)
      ≤ |((ρ - cz Q n R1 R2 + (d : ℤ) : ℤ) : ℝ)| + ((Q : ℕ) : ℝ) := by
    have := Wf_le Q (ρ - cz Q n R1 R2 + d)
    have h' : ((Wf Q (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ)
        ≤ ((|ρ - cz Q n R1 R2 + d| + ((Q : ℕ) : ℤ) : ℤ) : ℝ) := by exact_mod_cast this
    push_cast at h' ⊢
    exact h'
  have hW0 : 0 ≤ ((Wf Q (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ) := by exact_mod_cast Wf_nonneg Q _
  rw [abs_of_nonneg (add_nonneg hL0 (mul_nonneg P.h2_nonneg hW0))]
  have e1 : P.lossDown ((IPf Q R1 (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ)
      ≤ K * (b + ((Q : ℕ) : ℝ) + (a + d) + P.mu1) :=
    hL.trans (mul_le_mul_of_nonneg_left (by linarith) hK)
  have e2 : P.h2 * ((Wf Q (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ) ≤ P.h2 * (a + d + ((Q : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) P.h2_nonneg
  have e3 : K * (b + ((Q : ℕ) : ℝ) + (a + d) + P.mu1) + P.h2 * (a + d + ((Q : ℕ) : ℝ))
      = K * (b + ((Q : ℕ) : ℝ) + a + P.mu1) + P.h2 * (a + ((Q : ℕ) : ℝ)) + (K + P.h2) * d := by
    ring
  linarith

lemma pint_B (P : Params) (j : ℕ) :
    PInt P.mu2 (fun d : ℕ => latAvg (Q : ℕ) P.lossDown ((R1 : ℝ) + ((Q : ℕ) : ℝ)
        - max (-((R2 : ℝ) - (R1 : ℝ) + (j : ℝ) * ((Q : ℕ) : ℝ) - (d : ℝ))) 0)
      + P.h2 * max ((R2 : ℝ) - (R1 : ℝ) + (j : ℝ) * ((Q : ℕ) : ℝ) - (d : ℝ)) 0) := by
  have hμ := P.mu2_nonneg
  set w0 : ℝ := (R2 : ℝ) - (R1 : ℝ) + (j : ℝ) * ((Q : ℕ) : ℝ) with hw0
  set s0 : ℝ := (R1 : ℝ) + ((Q : ℕ) : ℝ) with hs0
  have hwabs : ∀ d : ℕ, |w0 - (d : ℝ)| ≤ |w0| + d := fun d => abs_sub_nat w0 d
  have hf : PInt P.mu2 (fun d : ℕ => s0 - max (-(w0 - (d : ℝ))) 0) := by
    refine PInt.of_abs_le hμ ((pint_const (|s0| + |w0|)).add hμ pint_nat) (fun d => ?_)
    have h1 : |max (-(w0 - (d : ℝ))) 0| ≤ |w0 - (d : ℝ)| := by
      rcases le_total (-(w0 - (d : ℝ))) 0 with h | h
      · rw [max_eq_right h, abs_zero]; exact abs_nonneg _
      · rw [max_eq_left h, abs_neg]
    have h2 := abs_sub s0 (max (-(w0 - (d : ℝ))) 0)
    have h3 := hwabs d
    linarith
  have h1 := (P.pint_latAvg_G0 (Q : ℕ) hf).sub hμ (pint_const P.H0)
  have e : (fun d : ℕ => latAvg (Q : ℕ) P.G0 (s0 - max (-(w0 - (d : ℝ))) 0) - P.H0)
      = (fun d : ℕ => latAvg (Q : ℕ) P.lossDown (s0 - max (-(w0 - (d : ℝ))) 0)) := by
    funext d; rw [P.latAvg_G0 Q.pos]; ring
  have h1' : PInt P.mu2 (fun d : ℕ => latAvg (Q : ℕ) P.lossDown (s0 - max (-(w0 - (d : ℝ))) 0)) := by
    have : PInt P.mu2 (fun d : ℕ => latAvg (Q : ℕ) P.G0 (s0 - max (-(w0 - (d : ℝ))) 0) - P.H0) := h1
    rwa [e] at this
  have h2 : PInt P.mu2 (fun d : ℕ => P.h2 * max (w0 - (d : ℝ)) 0) := by
    refine PInt.of_abs_le hμ (((pint_const |w0|).add hμ pint_nat).const_mul P.h2) (fun d => ?_)
    have h1 : |max (w0 - (d : ℝ)) 0| ≤ |w0 - (d : ℝ)| := by
      rcases le_total (w0 - (d : ℝ)) 0 with h | h
      · rw [max_eq_right h, abs_zero]; exact abs_nonneg _
      · rw [max_eq_left h]
    rw [abs_mul, abs_of_nonneg P.h2_nonneg]
    exact mul_le_mul_of_nonneg_left (h1.trans (hwabs d)) P.h2_nonneg
  exact h1'.add hμ h2

end Bounds

section Identity

variable (P : Params) (Q n : ℕ+) (R1 R2 : ℤ)

lemma cycle_identity :
    P.invCost n Q ((R1 : ℝ) + ((Q : ℕ) : ℝ)) ((R2 : ℝ) - (R1 : ℝ))
      = P.H0 + ∑ ρ ∈ Finset.Ico (0 : ℤ) (mN Q n), (1 / ((mN Q n : ℕ) : ℝ)) *
          pexp P.mu2 (fun d : ℕ => P.lossDown ((IPf Q R1 (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ)
            + P.h2 * ((Wf Q (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ)) := by
  have hQ : (0 : ℝ) < ((Q : ℕ) : ℝ) := by exact_mod_cast Q.pos
  have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
  have hμ := P.mu2_nonneg
  have hA := pint_A Q n R1 R2 P
  have hB := pint_B Q R1 R2 P

  have h1 : P.invCost n Q ((R1 : ℝ) + ((Q : ℕ) : ℝ)) ((R2 : ℝ) - (R1 : ℝ))
      = P.H0 + (∑ j ∈ range (n : ℕ), pexp P.mu2 (fun d : ℕ => latAvg (Q : ℕ) P.lossDown
          ((R1 : ℝ) + ((Q : ℕ) : ℝ) - max (-((R2 : ℝ) - (R1 : ℝ) + (j : ℝ) * ((Q : ℕ) : ℝ)
            - (d : ℝ))) 0)
          + P.h2 * max ((R2 : ℝ) - (R1 : ℝ) + (j : ℝ) * ((Q : ℕ) : ℝ) - (d : ℝ)) 0))
          / ((n : ℕ) : ℝ) := by
    unfold Params.invCost
    have e : ∀ j ∈ range (n : ℕ), pexp P.mu2 (fun d : ℕ => latAvg (Q : ℕ) P.G0
        ((R1 : ℝ) + ((Q : ℕ) : ℝ) - max (-((R2 : ℝ) - (R1 : ℝ) + (j : ℝ) * ((Q : ℕ) : ℝ)
          - (d : ℝ))) 0)
        + P.h2 * max ((R2 : ℝ) - (R1 : ℝ) + (j : ℝ) * ((Q : ℕ) : ℝ) - (d : ℝ)) 0)
        = P.H0 + pexp P.mu2 (fun d : ℕ => latAvg (Q : ℕ) P.lossDown
          ((R1 : ℝ) + ((Q : ℕ) : ℝ) - max (-((R2 : ℝ) - (R1 : ℝ) + (j : ℝ) * ((Q : ℕ) : ℝ)
            - (d : ℝ))) 0)
          + P.h2 * max ((R2 : ℝ) - (R1 : ℝ) + (j : ℝ) * ((Q : ℕ) : ℝ) - (d : ℝ)) 0) := by
      intro j _
      rw [← pexp_const P.mu2 P.H0, ← pexp_add hμ (pint_const _) (hB j)]
      refine pexp_congr (fun d => ?_)
      rw [P.latAvg_G0 Q.pos]; ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    field_simp

  have hcomb : ∀ d : ℕ, ∑ ρ ∈ Finset.Ico (0 : ℤ) (mN Q n),
      (P.lossDown ((IPf Q R1 (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ)
        + P.h2 * ((Wf Q (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ))
      = ((Q : ℕ) : ℝ) * ∑ j ∈ range (n : ℕ), (latAvg (Q : ℕ) P.lossDown
          ((R1 : ℝ) + ((Q : ℕ) : ℝ) - max (-((R2 : ℝ) - (R1 : ℝ) + (j : ℝ) * ((Q : ℕ) : ℝ)
            - (d : ℝ))) 0)
          + P.h2 * max ((R2 : ℝ) - (R1 : ℝ) + (j : ℝ) * ((Q : ℕ) : ℝ) - (d : ℝ)) 0) := by
    intro d
    have e1 := decomp Q n R1 R2
      (fun y => P.lossDown ((IPf Q R1 y : ℤ) : ℝ) + P.h2 * ((Wf Q y : ℤ) : ℝ)) (d : ℤ)
    rw [e1, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hI := sum_IPf Q R1 (fun z : ℤ => P.lossDown (z : ℝ))
      ((R2 - R1) + (j : ℤ) * ((Q : ℕ) : ℤ) - (d : ℤ))
    have hW := sum_Wf Q ((R2 - R1) + (j : ℤ) * ((Q : ℕ) : ℤ) - (d : ℤ))
    have hW' : ∑ u ∈ range (Q : ℕ), ((Wf Q ((u : ℤ) - ((R2 - R1) + (j : ℤ) * ((Q : ℕ) : ℤ)
        - (d : ℤ))) : ℤ) : ℝ)
        = ((Q : ℕ) : ℝ) * max ((((R2 - R1) + (j : ℤ) * ((Q : ℕ) : ℤ) - (d : ℤ)) : ℤ) : ℝ) 0 := by
      rw [← Int.cast_sum, hW]
      push_cast
      ring
    rw [hI, hW']
    beta_reduce
    unfold latAvg
    rw [mul_add, mul_div_cancel₀ _ hQ.ne']
    congr 1
    · refine Finset.sum_congr rfl (fun v _ => ?_)
      congr 1
      unfold sz
      push_cast
      ring
    · push_cast
      ring
  rw [h1, ← Finset.mul_sum, ← pexp_finset_sum hμ _ (fun ρ _ => hA ρ), pexp_congr hcomb,
    pexp_const_mul, pexp_finset_sum hμ _ (fun j _ => hB j), mN_castR]
  field_simp

end Identity

section PoisSum

lemma tsum_ofReal_pexp {μ : ℝ} (hμ : 0 ≤ μ) {f : ℕ → ℝ} (hf0 : ∀ d, 0 ≤ f d) (hf : PInt μ f) :
    ∑' d : ℕ, ENNReal.ofReal (poisW μ d) * ENNReal.ofReal (f d) = ENNReal.ofReal (pexp μ f) := by
  unfold pexp
  rw [ENNReal.ofReal_tsum_of_nonneg (fun d => mul_nonneg (poisW_nonneg hμ d) (hf0 d))
    (hf.summable hμ)]
  refine tsum_congr (fun d => ?_)
  rw [ENNReal.ofReal_mul (poisW_nonneg hμ d)]

end PoisSum

end Prop1

end TwoStageRnQ

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace Prop1

open TwoStageRnQ.Prop1

section Asym

lemma iiOfBdd {f : ℝ → ℝ} {C : ℝ} (hm : Measurable f) (hb : ∀ t, |f t| ≤ C) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hb 0)
  refine (intervalIntegrable_const (c := C)).mono_fun hm.aestronglyMeasurable ?_
  refine ae_of_all _ (fun x => ?_)
  simp only [Real.norm_eq_abs, abs_of_nonneg hC]
  exact hb x

lemma cesaro_Ioc {f : ℝ → ℝ} {C I : ℝ} (hm : Measurable f) (hb : ∀ t, |f t| ≤ C)
    (hl : Tendsto f atTop (𝓝 I)) :
    Tendsto (fun T => T⁻¹ * ∫ t in Set.Ioc 0 T, f t) atTop (𝓝 I) := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hb 0)
  have hii := iiOfBdd hm hb
  have hii' : ∀ a b : ℝ, IntervalIntegrable (fun t => f t - I) volume a b :=
    fun a b => (hii a b).sub intervalIntegrable_const
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T0, hT0⟩ := Metric.tendsto_atTop.mp hl (ε / 2) (by linarith)
  have hT1n : 0 ≤ max T0 0 := le_max_right _ _
  have hKn : 0 ≤ C + |I| := by positivity
  refine ⟨max (max T0 0 + 1) (4 * (C + |I|) * max T0 0 / ε + 1), fun T hT => ?_⟩
  have hTa : max T0 0 + 1 ≤ T := le_trans (le_max_left _ _) hT
  have hTb : 4 * (C + |I|) * max T0 0 / ε + 1 ≤ T := le_trans (le_max_right _ _) hT
  have hTpos : 0 < T := by linarith
  have hT1T : max T0 0 ≤ T := by linarith
  have hsplit : ∫ t in Set.Ioc 0 T, f t = (∫ t in (0 : ℝ)..(max T0 0), (f t - I))
      + (∫ t in (max T0 0)..T, (f t - I)) + T * I := by
    rw [← intervalIntegral.integral_of_le hTpos.le,
      intervalIntegral.integral_add_adjacent_intervals (hii' 0 (max T0 0)) (hii' (max T0 0) T),
      intervalIntegral.integral_sub (hii 0 T) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    ring
  have hA : |∫ t in (0 : ℝ)..(max T0 0), (f t - I)| ≤ (C + |I|) * max T0 0 := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := max T0 0)
      (f := fun t => f t - I) (C := C + |I|) (fun x _ => by
        rw [Real.norm_eq_abs]
        calc |f x - I| ≤ |f x| + |I| := abs_sub _ _
          _ ≤ C + |I| := by linarith [hb x])
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hT1n] at h
    exact h
  have hB : |∫ t in (max T0 0)..T, (f t - I)| ≤ ε / 2 * (T - max T0 0) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := max T0 0) (b := T)
      (f := fun t => f t - I) (C := ε / 2) (fun x hx => by
        rw [Real.norm_eq_abs]
        rw [Set.uIoc_of_le hT1T] at hx
        have hx0 : T0 ≤ x := le_trans (le_max_left _ _) hx.1.le
        have h' := hT0 x hx0
        rw [Real.dist_eq] at h'
        exact h'.le)
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ T - max T0 0)] at h
    exact h
  have hTi : 0 < T⁻¹ := inv_pos.mpr hTpos
  have hTT : T⁻¹ * (T * I) = I := by rw [← mul_assoc, inv_mul_cancel₀ hTpos.ne', one_mul]
  rw [Real.dist_eq, hsplit, mul_add, mul_add, hTT, add_sub_cancel_right]
  calc |T⁻¹ * (∫ t in (0 : ℝ)..(max T0 0), (f t - I)) + T⁻¹ * (∫ t in (max T0 0)..T, (f t - I))|
      ≤ |T⁻¹ * (∫ t in (0 : ℝ)..(max T0 0), (f t - I))| + |T⁻¹ * (∫ t in (max T0 0)..T, (f t - I))| :=
        abs_add_le _ _
    _ = T⁻¹ * |∫ t in (0 : ℝ)..(max T0 0), (f t - I)| + T⁻¹ * |∫ t in (max T0 0)..T, (f t - I)| := by
        rw [abs_mul, abs_mul, abs_of_pos hTi]
    _ ≤ T⁻¹ * ((C + |I|) * max T0 0) + T⁻¹ * (ε / 2 * (T - max T0 0)) := by
        gcongr
    _ < ε := by
        have h1 : T⁻¹ * ((C + |I|) * max T0 0) ≤ ε / 4 := by
          rw [inv_mul_le_iff₀ hTpos]
          have e : ε / 4 * (4 * (C + |I|) * max T0 0 / ε + 1) = (C + |I|) * max T0 0 + ε / 4 := by
            field_simp
          have h3 := mul_le_mul_of_nonneg_left hTb (by positivity : (0 : ℝ) ≤ ε / 4)
          rw [e] at h3
          linarith
        have h2 : T⁻¹ * (ε / 2 * (T - max T0 0)) ≤ ε / 2 := by
          rw [inv_mul_le_iff₀ hTpos]
          nlinarith
        linarith

lemma tendsto_of_bdd {a : ℝ → ℝ} {c B : ℝ} (h : ∀ T, 0 ≤ T → |a T - c * T| ≤ B) :
    Tendsto (fun T => T⁻¹ * a T) atTop (𝓝 c) := by
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (h 0 le_rfl)
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨B / ε + 1, fun T hT => ?_⟩
  have hBe : 0 ≤ B / ε := div_nonneg hB hε.le
  have hTpos : 0 < T := by linarith
  have hT0 : T ≠ 0 := hTpos.ne'
  rw [Real.dist_eq]
  have e : T⁻¹ * (a T - c * T) = T⁻¹ * a T - c := by
    rw [mul_sub, mul_comm c T, ← mul_assoc, inv_mul_cancel₀ hT0, one_mul]
  rw [← e, abs_mul, abs_of_pos (inv_pos.mpr hTpos)]
  calc T⁻¹ * |a T - c * T| ≤ T⁻¹ * B := mul_le_mul_of_nonneg_left (h T hTpos.le) (inv_pos.mpr hTpos).le
    _ < ε := by
      rw [inv_mul_lt_iff₀ hTpos]
      have e2 : B / ε * ε = B := by field_simp
      nlinarith

lemma toReal_add_eq {a b c d : ℝ≥0∞} (h : a + b = c + d) (hb : b ≠ ⊤) (hc : c ≠ ⊤) (hd : d ≠ ⊤) :
    a ≠ ⊤ ∧ a.toReal + b.toReal = c.toReal + d.toReal := by
  have hcd : c + d ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hc, hd⟩
  have ha : a ≠ ⊤ := by
    intro ha
    rw [ha, top_add] at h
    exact hcd h.symm
  refine ⟨ha, ?_⟩
  rw [← ENNReal.toReal_add ha hb, ← ENNReal.toReal_add hc hd, h]

end Asym

section Expect

variable {P : Params} (S : DemandSpace P) (R1 R2 : ℤ) (Q n : ℕ+)

lemma meas_N2 {β : Type*} [MeasurableSpace β] (f : ℤ × ℤ → β) (a b : ℝ) :
    Measurable (fun ω => f (S.N a ω, S.N b ω)) := by
  have h := (measurable_of_countable f).comp ((S.N_meas a).prodMk (S.N_meas b))
  exact h

lemma matchCount_eq (t : ℝ) (ω : S.Ω) :
    Classical'.matchCount S (ctrl R1 R2 Q n) t ω
      = min (S.N t ω / ((Q : ℕ) : ℤ)) (((n : ℕ) : ℤ) * ((S.N (t - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) := by
  show min (Classical'.reqCount S (ctrl R1 R2 Q n) t ω)
    (((n : ℕ) : ℤ) * Classical'.ordCount S (ctrl R1 R2 Q n) (t - P.L2) ω) = _
  rw [reqCount_eq, ordCount_eq]

lemma match_meas (t : ℝ) : Measurable (fun ω => Classical'.matchCount S (ctrl R1 R2 Q n) t ω) := by
  have e : (fun ω => Classical'.matchCount S (ctrl R1 R2 Q n) t ω)
      = fun ω => (fun z : ℤ × ℤ => min (z.1 / ((Q : ℕ) : ℤ))
          (((n : ℕ) : ℤ) * ((z.2 + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)))) (S.N t ω, S.N (t - P.L2) ω) := by
    funext ω
    exact matchCount_eq S R1 R2 Q n t ω
  rw [e]
  exact meas_N2 S (fun z : ℤ × ℤ => min (z.1 / ((Q : ℕ) : ℤ))
    (((n : ℕ) : ℤ) * ((z.2 + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)))) t (t - P.L2)

lemma lintegral_phi {t : ℝ} (ht : P.L1 ≤ t) {X : S.Ω → ℤ} (hX : Measurable[S.𝓕 (t - P.L1)] X) :
    ∫⁻ ω, ENNReal.ofReal (phi (P.h1 + P.h2) P.p ((X ω : ℝ)
      - ((S.N t ω - S.N (t - P.L1) ω : ℤ) : ℝ))) ∂S.ν
      = ∫⁻ ω, ENNReal.ofReal (P.lossDown (X ω)) ∂S.ν := by
  have hv : t - P.L1 ≤ t := by linarith [P.L1_nonneg]
  have key := S.lintegral_incr (by linarith : 0 ≤ t - P.L1) hv hX
    (fun (a : ℤ) (d : ℕ) => ENNReal.ofReal (phi (P.h1 + P.h2) P.p ((a : ℝ) - (d : ℝ))))
  have e1 : ∫⁻ ω, ENNReal.ofReal (phi (P.h1 + P.h2) P.p ((X ω : ℝ)
      - ((S.N t ω - S.N (t - P.L1) ω : ℤ) : ℝ))) ∂S.ν
      = ∫⁻ ω, ENNReal.ofReal (phi (P.h1 + P.h2) P.p ((X ω : ℝ)
          - (((S.N t ω - S.N (t - P.L1) ω).toNat : ℕ) : ℝ))) ∂S.ν := by
    refine lintegral_congr (fun ω => ?_)
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (S.incr_nonneg hv ω)]
  have hXm : Measurable X := hX.mono (S.𝓕.le _) le_rfl
  rw [e1, key, S.lintegral_comp hXm (fun a => ENNReal.ofReal (P.lossDown (a : ℝ)))]
  refine tsum_congr (fun a => ?_)
  congr 1
  rw [show P.lam * (t - (t - P.L1)) = P.mu1 by unfold Params.mu1; ring]
  have hpint := (phi_linGrowth P.a_nonneg P.p_nonneg (a : ℝ)).pint P.mu1_nonneg
  exact tsum_ofReal_pexp P.mu1_nonneg (fun d => phi_nonneg P.a_nonneg P.p_nonneg _) hpint

theorem lintegral_cI_asym {t : ℝ} (ht : P.L1 + P.L2 ≤ t) :
    ∫⁻ ω, ENNReal.ofReal (Classical'.cI S (ctrl R1 R2 Q n) t ω) ∂S.ν
      + ENNReal.ofReal P.h2 * ∫⁻ ω, ENNReal.ofReal ((((S.N (t - P.L2) ω + cz Q n R1 R2) % ((mN Q n : ℕ) : ℤ) : ℤ)) : ℝ) ∂S.ν
      = ∑ ρ ∈ Finset.Ico (0 : ℤ) (mN Q n), S.shLaw (mN Q n) (t - P.L1 - P.L2) (cz Q n R1 R2) ρ
          * ENNReal.ofReal (pexp P.mu2 (fun d : ℕ => P.lossDown ((IPf Q R1 (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ) + P.h2 * ((Wf Q (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ)))
        + ENNReal.ofReal P.h2 * (ENNReal.ofReal (P.lam * P.L1) + ∫⁻ ω, ENNReal.ofReal ((((S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) % ((mN Q n : ℕ) : ℤ) : ℤ)) : ℝ) ∂S.ν) := by
  have hm := mN_pos Q n
  have hm' : (0 : ℤ) < ((mN Q n : ℕ) : ℤ) := by exact_mod_cast hm
  have hL1 := P.L1_nonneg
  have hL2 := P.L2_nonneg
  have hμ := P.mu2_nonneg

  have hpt : ∀ ω, ENNReal.ofReal (Classical'.cI S (ctrl R1 R2 Q n) t ω)
      = (ENNReal.ofReal (phi (P.h1 + P.h2) P.p (((IPf Q R1 (S.N (t - P.L1) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) : ℤ) : ℝ) - ((S.N t ω - S.N (t - P.L1) ω : ℤ) : ℝ))) + ENNReal.ofReal (P.h2 * ((Wf Q (S.N (t - P.L1) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) : ℤ) : ℝ)))
        + ENNReal.ofReal (P.h2 * ((((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ) - (S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)) : ℤ) : ℝ)) := by
    intro ω
    rw [cI_eq]
    have a1 : 0 ≤ phi (P.h1 + P.h2) P.p (((IPf Q R1 (S.N (t - P.L1) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) : ℤ) : ℝ) - ((S.N t ω - S.N (t - P.L1) ω : ℤ) : ℝ)) := phi_nonneg P.a_nonneg P.p_nonneg _
    have hOO : (S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ) ≤ (S.N (t - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ) :=
      Int.ediv_le_ediv hm' (by linarith [S.N_mono ω (by linarith : t - P.L1 - P.L2 ≤ t - P.L2)])
    have a2 : 0 ≤ P.h2 * ((((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ) - (S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)) : ℤ) : ℝ) :=
      mul_nonneg P.h2_nonneg (by exact_mod_cast mul_nonneg hm'.le (by linarith))
    have a3 : 0 ≤ P.h2 * ((Wf Q (S.N (t - P.L1) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) : ℤ) : ℝ) :=
      mul_nonneg P.h2_nonneg (by exact_mod_cast Wf_nonneg Q _)
    rw [← ENNReal.ofReal_add a1 a3, ← ENNReal.ofReal_add (add_nonneg a1 a3) a2]
    congr 1
    ring

  have hX : Measurable[S.𝓕 (t - P.L1)] (fun ω => IPf Q R1 (S.N (t - P.L1) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)))) := by
    have h := (measurable_of_countable (fun p : ℤ × ℤ => IPf Q R1 (p.1 - ((mN Q n : ℕ) : ℤ)
      * ((p.2 + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))))).comp ((S.N_adapted (t - P.L1)).prodMk
        (S.N_meas_le (by linarith : t - P.L1 - P.L2 ≤ t - P.L1)))
    exact h
  have m1 : Measurable (fun ω => ENNReal.ofReal (phi (P.h1 + P.h2) P.p (((IPf Q R1 (S.N (t - P.L1) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) : ℤ) : ℝ) - ((S.N t ω - S.N (t - P.L1) ω : ℤ) : ℝ)))) := by
    have h := (measurable_of_countable (fun z : ℤ × ℤ × ℤ => ENNReal.ofReal
      (phi (P.h1 + P.h2) P.p (((IPf Q R1 (z.2.1 - ((mN Q n : ℕ) : ℤ) * ((z.2.2 + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)))
        : ℤ) : ℝ) - ((z.1 - z.2.1 : ℤ) : ℝ))))).comp
      ((S.N_meas t).prodMk ((S.N_meas (t - P.L1)).prodMk (S.N_meas (t - P.L1 - P.L2))))
    exact h
  have m2 : Measurable (fun ω => ENNReal.ofReal (P.h2 * ((((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ) - (S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)) : ℤ) : ℝ))) := by
    have h := meas_N2 S (fun z : ℤ × ℤ => ENNReal.ofReal (P.h2 * ((((mN Q n : ℕ) : ℤ)
      * ((z.1 + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ) - (z.2 + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)) : ℤ) : ℝ)))
      (t - P.L2) (t - P.L1 - P.L2)
    exact h
  have m3 : Measurable (fun ω => ENNReal.ofReal ((((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ) - (S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)) : ℤ) : ℝ)) := by
    have h := meas_N2 S (fun z : ℤ × ℤ => ENNReal.ofReal ((((mN Q n : ℕ) : ℤ)
      * ((z.1 + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ) - (z.2 + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)) : ℤ) : ℝ))
      (t - P.L2) (t - P.L1 - P.L2)
    exact h
  have m4 : Measurable (fun ω => ENNReal.ofReal (P.lossDown ((IPf Q R1 (S.N (t - P.L1) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) : ℤ) : ℝ))) := by
    have h := meas_N2 S (fun z : ℤ × ℤ => ENNReal.ofReal (P.lossDown ((IPf Q R1 (z.1
      - ((mN Q n : ℕ) : ℤ) * ((z.2 + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) : ℤ) : ℝ)))
      (t - P.L1) (t - P.L1 - P.L2)
    exact h
  rw [lintegral_congr hpt, lintegral_add_right _ m2, lintegral_add_left m1,
    lintegral_phi S (by linarith : P.L1 ≤ t) hX, ← lintegral_add_left m4]
  have hY := S.lintegral_Y (mN Q n) hm hL2 (t := t - P.L1) (by linarith) (cz Q n R1 R2)
    (fun y => ENNReal.ofReal (P.lossDown ((IPf Q R1 y : ℤ) : ℝ))
      + ENNReal.ofReal (P.h2 * ((Wf Q y : ℤ) : ℝ)))
  rw [hY]
  have hO := S.lintegral_ordIncr (mN Q n) hm (by linarith : t - P.L1 - P.L2 ≤ t - P.L2) (cz Q n R1 R2)
  rw [show t - P.L2 - (t - P.L1 - P.L2) = P.L1 by ring] at hO
  have e2 : (fun ω => ENNReal.ofReal (P.h2 * ((((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ) - (S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)) : ℤ) : ℝ)))
      = fun ω => ENNReal.ofReal P.h2 * ENNReal.ofReal ((((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ) - (S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)) : ℤ) : ℝ) := by
    funext ω; rw [ENNReal.ofReal_mul P.h2_nonneg]
  rw [e2, lintegral_const_mul _ m3]
  have hinner : ∀ ρ ∈ Finset.Ico (0 : ℤ) (mN Q n),
      S.shLaw (mN Q n) (t - P.L1 - P.L2) (cz Q n R1 R2) ρ * ∑' d : ℕ, ENNReal.ofReal (poisW (P.lam * P.L2) d)
        * (ENNReal.ofReal (P.lossDown ((IPf Q R1 (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ))
          + ENNReal.ofReal (P.h2 * ((Wf Q (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ)))
      = S.shLaw (mN Q n) (t - P.L1 - P.L2) (cz Q n R1 R2) ρ * ENNReal.ofReal (pexp P.mu2 (fun d : ℕ => P.lossDown ((IPf Q R1 (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ) + P.h2 * ((Wf Q (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ))) := by
    intro ρ _
    congr 1
    have hnn : ∀ d : ℕ, 0 ≤ P.lossDown ((IPf Q R1 (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ)
        + P.h2 * ((Wf Q (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ) := fun d =>
      add_nonneg (P.lossDown_nonneg _) (mul_nonneg P.h2_nonneg (by exact_mod_cast Wf_nonneg Q _))
    have e3 : ∀ d : ℕ, (ENNReal.ofReal (P.lossDown ((IPf Q R1 (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ))
          + ENNReal.ofReal (P.h2 * ((Wf Q (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ)))
        = ENNReal.ofReal (P.lossDown ((IPf Q R1 (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ)
            + P.h2 * ((Wf Q (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ)) := fun d =>
      (ENNReal.ofReal_add (P.lossDown_nonneg _)
        (mul_nonneg P.h2_nonneg (by exact_mod_cast Wf_nonneg Q _))).symm
    simp_rw [e3]
    rw [show P.lam * P.L2 = P.mu2 from rfl,
      tsum_ofReal_pexp hμ hnn (pint_A Q n R1 R2 P ρ)]
  have final : ∀ (X Y Z W V : ℝ≥0∞), Y + Z = W → X = V →
      X + ENNReal.ofReal P.h2 * Y + ENNReal.ofReal P.h2 * Z = V + ENNReal.ofReal P.h2 * W := by
    intro X Y Z W V h1 h2
    rw [← h1, ← h2, add_assoc, ← mul_add]
  exact final _ _ _ _ _ hO (Finset.sum_congr rfl hinner)

lemma cI_le (t : ℝ) (ω : S.Ω) :
    Classical'.cI S (ctrl R1 R2 Q n) t ω
      ≤ ((P.h1 + P.h2 + P.p) * (|((sz Q R1 : ℤ) : ℝ)| + ((Q : ℕ) : ℝ) + |((cz Q n R1 R2 : ℤ) : ℝ)| + ((mN Q n : ℕ) : ℝ)) + P.h2 * (2 * ((mN Q n : ℕ) : ℝ) + |((cz Q n R1 R2 : ℤ) : ℝ)| + ((Q : ℕ) : ℝ))) + ((P.h1 + P.h2 + P.p) + 2 * P.h2) * ((S.N t ω - S.N (t - P.L1 - P.L2) ω : ℤ) : ℝ) := by
  have hm := mN_pos Q n
  have hm' : (0 : ℤ) < ((mN Q n : ℕ) : ℤ) := by exact_mod_cast hm
  have hq : (0 : ℤ) < ((Q : ℕ) : ℤ) := by exact_mod_cast Q.pos
  have hL1 := P.L1_nonneg
  have hL2 := P.L2_nonneg
  rw [cI_eq]
  have m1 : S.N (t - P.L1 - P.L2) ω ≤ S.N (t - P.L1) ω := S.N_mono ω (by linarith)
  have m2 : S.N (t - P.L1) ω ≤ S.N t ω := S.N_mono ω (by linarith)
  have m3 : S.N (t - P.L1 - P.L2) ω ≤ S.N (t - P.L2) ω := S.N_mono ω (by linarith)
  have m4 : S.N (t - P.L2) ω ≤ S.N t ω := S.N_mono ω (by linarith)
  have r0 := Int.emod_add_mul_ediv (S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) ((mN Q n : ℕ) : ℤ)
  have r0a := Int.emod_nonneg (S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) hm'.ne'
  have r0b := Int.emod_lt_of_pos (S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) hm'
  have r1 := Int.emod_add_mul_ediv (S.N (t - P.L2) ω + cz Q n R1 R2) ((mN Q n : ℕ) : ℤ)
  have r1a := Int.emod_nonneg (S.N (t - P.L2) ω + cz Q n R1 R2) hm'.ne'
  have r1b := Int.emod_lt_of_pos (S.N (t - P.L2) ω + cz Q n R1 R2) hm'
  have hc1 := le_abs_self (cz Q n R1 R2)
  have hc2 := neg_abs_le (cz Q n R1 R2)

  have hY : |S.N (t - P.L1) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))|
      ≤ (S.N (t - P.L1) ω - S.N (t - P.L1 - P.L2) ω) + |cz Q n R1 R2| + ((mN Q n : ℕ) : ℤ) := by
    rw [abs_le]; constructor <;> linarith
  have hIP := IPf_abs Q R1 (S.N (t - P.L1) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)))
  have hW := Wf_le Q (S.N (t - P.L1) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)))
  have hO : ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ) - (S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))
      ≤ (S.N t ω - S.N (t - P.L1 - P.L2) ω) + ((mN Q n : ℕ) : ℤ) := by
    rw [mul_sub]; linarith

  have hYr : |((S.N (t - P.L1) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)) : ℤ) : ℝ)|
      ≤ ((S.N (t - P.L1) ω - S.N (t - P.L1 - P.L2) ω : ℤ) : ℝ) + |((cz Q n R1 R2 : ℤ) : ℝ)| + ((mN Q n : ℕ) : ℝ) := by
    have h := (Int.cast_le (R := ℝ)).mpr hY
    push_cast at h ⊢
    exact h
  have hIPr : |((IPf Q R1 (S.N (t - P.L1) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) : ℤ) : ℝ)|
      ≤ |((sz Q R1 : ℤ) : ℝ)| + ((Q : ℕ) : ℝ)
        + |((S.N (t - P.L1) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)) : ℤ) : ℝ)| := by
    have h := (Int.cast_le (R := ℝ)).mpr hIP
    push_cast at h ⊢
    exact h
  have hWr : ((Wf Q (S.N (t - P.L1) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) : ℤ) : ℝ)
      ≤ |((S.N (t - P.L1) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)) : ℤ) : ℝ)| + ((Q : ℕ) : ℝ) := by
    have h := (Int.cast_le (R := ℝ)).mpr hW
    push_cast at h ⊢
    exact h
  have hOr : (((((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ) - (S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) : ℤ) : ℝ)
      ≤ ((S.N t ω - S.N (t - P.L1 - P.L2) ω : ℤ) : ℝ) + ((mN Q n : ℕ) : ℝ) := by
    have h := (Int.cast_le (R := ℝ)).mpr hO
    push_cast at h ⊢
    exact h
  have hd1 : ((S.N (t - P.L1) ω - S.N (t - P.L1 - P.L2) ω : ℤ) : ℝ)
      ≤ ((S.N t ω - S.N (t - P.L1 - P.L2) ω : ℤ) : ℝ) := by
    have h : S.N (t - P.L1) ω - S.N (t - P.L1 - P.L2) ω ≤ S.N t ω - S.N (t - P.L1 - P.L2) ω := by
      linarith
    exact_mod_cast h
  have hd2 : (0 : ℝ) ≤ ((S.N t ω - S.N (t - P.L1) ω : ℤ) : ℝ) := by
    have h : 0 ≤ S.N t ω - S.N (t - P.L1) ω := by linarith
    exact_mod_cast h
  have hdd : ((S.N t ω - S.N (t - P.L1) ω : ℤ) : ℝ) + ((S.N (t - P.L1) ω - S.N (t - P.L1 - P.L2) ω : ℤ) : ℝ)
      = ((S.N t ω - S.N (t - P.L1 - P.L2) ω : ℤ) : ℝ) := by push_cast; ring

  have k0 : 0 ≤ P.h1 + P.h2 + P.p := add_nonneg P.a_nonneg P.p_nonneg
  have hph : ∀ x : ℝ, phi (P.h1 + P.h2) P.p x ≤ (P.h1 + P.h2 + P.p) * |x| := by
    intro x
    unfold phi
    have e1 : max x 0 ≤ |x| := max_le (le_abs_self x) (abs_nonneg x)
    have e2 : max (-x) 0 ≤ |x| := max_le (neg_le_abs x) (abs_nonneg x)
    have e3 := mul_le_mul_of_nonneg_left e1 P.a_nonneg
    have e4 := mul_le_mul_of_nonneg_left e2 P.p_nonneg
    nlinarith
  set x := ((IPf Q R1 (S.N (t - P.L1) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) : ℤ) : ℝ)
    - ((S.N t ω - S.N (t - P.L1) ω : ℤ) : ℝ) with hx
  have hxa : |x| ≤ |((IPf Q R1 (S.N (t - P.L1) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) : ℤ) : ℝ)|
      + ((S.N t ω - S.N (t - P.L1) ω : ℤ) : ℝ) := by
    rw [hx]
    calc _ ≤ _ := abs_sub _ _
      _ = _ := by rw [abs_of_nonneg hd2]
  have f1 := hph x
  have f2 := mul_le_mul_of_nonneg_left hxa k0
  have f3 := mul_le_mul_of_nonneg_left hIPr k0
  have f4 := mul_le_mul_of_nonneg_left hYr k0
  have f5 := mul_le_mul_of_nonneg_left hOr P.h2_nonneg
  have f6 := mul_le_mul_of_nonneg_left hWr P.h2_nonneg
  have f7 := mul_le_mul_of_nonneg_left hYr P.h2_nonneg
  have f8 := mul_le_mul_of_nonneg_left hd1 P.h2_nonneg
  have f9 := mul_le_mul_of_nonneg_left hd1 k0
  nlinarith

lemma CB_nonneg : 0 ≤ ((P.h1 + P.h2 + P.p) * (|((sz Q R1 : ℤ) : ℝ)| + ((Q : ℕ) : ℝ) + |((cz Q n R1 R2 : ℤ) : ℝ)| + ((mN Q n : ℕ) : ℝ)) + P.h2 * (2 * ((mN Q n : ℕ) : ℝ) + |((cz Q n R1 R2 : ℤ) : ℝ)| + ((Q : ℕ) : ℝ))) + ((P.h1 + P.h2 + P.p) + 2 * P.h2) * (P.lam * (P.L1 + P.L2)) := by
  have k0 : 0 ≤ P.h1 + P.h2 + P.p := add_nonneg P.a_nonneg P.p_nonneg
  have := P.h2_nonneg
  have := P.lam_nonneg
  have := P.L1_nonneg
  have := P.L2_nonneg
  have hQ : (0 : ℝ) ≤ ((Q : ℕ) : ℝ) := by positivity
  have hmR : (0 : ℝ) ≤ ((mN Q n : ℕ) : ℝ) := by positivity
  positivity

lemma lintegral_cI_le (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Classical'.cI S (ctrl R1 R2 Q n) t ω) ∂S.ν
      ≤ ENNReal.ofReal (((P.h1 + P.h2 + P.p) * (|((sz Q R1 : ℤ) : ℝ)| + ((Q : ℕ) : ℝ) + |((cz Q n R1 R2 : ℤ) : ℝ)| + ((mN Q n : ℕ) : ℝ)) + P.h2 * (2 * ((mN Q n : ℕ) : ℝ) + |((cz Q n R1 R2 : ℤ) : ℝ)| + ((Q : ℕ) : ℝ))) + ((P.h1 + P.h2 + P.p) + 2 * P.h2) * (P.lam * (P.L1 + P.L2))) := by
  have k0 : 0 ≤ P.h1 + P.h2 + P.p := add_nonneg P.a_nonneg P.p_nonneg
  have hQ : (0 : ℝ) ≤ ((Q : ℕ) : ℝ) := by positivity
  have hmR : (0 : ℝ) ≤ ((mN Q n : ℕ) : ℝ) := by positivity
  have h0 : 0 ≤ ((P.h1 + P.h2 + P.p) * (|((sz Q R1 : ℤ) : ℝ)| + ((Q : ℕ) : ℝ) + |((cz Q n R1 R2 : ℤ) : ℝ)| + ((mN Q n : ℕ) : ℝ)) + P.h2 * (2 * ((mN Q n : ℕ) : ℝ) + |((cz Q n R1 R2 : ℤ) : ℝ)| + ((Q : ℕ) : ℝ))) := by have := P.h2_nonneg; positivity
  have h1 : 0 ≤ ((P.h1 + P.h2 + P.p) + 2 * P.h2) := by have := P.h2_nonneg; positivity
  have hv : t - P.L1 - P.L2 ≤ t := by linarith [P.L1_nonneg, P.L2_nonneg]
  have hmeas : Measurable (fun ω => ENNReal.ofReal (((S.N t ω - S.N (t - P.L1 - P.L2) ω : ℤ) : ℝ))) := by
    have h := meas_N2 S (fun z : ℤ × ℤ => ENNReal.ofReal (((z.1 - z.2 : ℤ) : ℝ))) t (t - P.L1 - P.L2)
    exact h
  calc ∫⁻ ω, ENNReal.ofReal (Classical'.cI S (ctrl R1 R2 Q n) t ω) ∂S.ν
      ≤ ∫⁻ ω, (ENNReal.ofReal (((P.h1 + P.h2 + P.p) * (|((sz Q R1 : ℤ) : ℝ)| + ((Q : ℕ) : ℝ) + |((cz Q n R1 R2 : ℤ) : ℝ)| + ((mN Q n : ℕ) : ℝ)) + P.h2 * (2 * ((mN Q n : ℕ) : ℝ) + |((cz Q n R1 R2 : ℤ) : ℝ)| + ((Q : ℕ) : ℝ)))) + ENNReal.ofReal (((P.h1 + P.h2 + P.p) + 2 * P.h2))
          * ENNReal.ofReal (((S.N t ω - S.N (t - P.L1 - P.L2) ω : ℤ) : ℝ))) ∂S.ν := by
        refine lintegral_mono (fun ω => ?_)
        rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_add h0 (mul_nonneg h1 (by
          exact_mod_cast S.incr_nonneg hv ω))]
        exact ENNReal.ofReal_le_ofReal (cI_le S R1 R2 Q n t ω)
    _ = ENNReal.ofReal (((P.h1 + P.h2 + P.p) * (|((sz Q R1 : ℤ) : ℝ)| + ((Q : ℕ) : ℝ) + |((cz Q n R1 R2 : ℤ) : ℝ)| + ((mN Q n : ℕ) : ℝ)) + P.h2 * (2 * ((mN Q n : ℕ) : ℝ) + |((cz Q n R1 R2 : ℤ) : ℝ)| + ((Q : ℕ) : ℝ))) + ((P.h1 + P.h2 + P.p) + 2 * P.h2) * (P.lam * (P.L1 + P.L2))) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ hmeas, S.lintegral_incr_val hv,
          ← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_add h0 (mul_nonneg h1 (mul_nonneg P.lam_nonneg
            (by linarith [P.L1_nonneg, P.L2_nonneg])))]
        congr 2
        ring

lemma lintegral_cI_ne_top (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Classical'.cI S (ctrl R1 R2 Q n) t ω) ∂S.ν ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lintegral_cI_le S R1 R2 Q n t)

def fcI (t : ℝ) : ℝ := (∫⁻ ω, ENNReal.ofReal (Classical'.cI S (ctrl R1 R2 Q n) t ω) ∂S.ν).toReal

lemma fcI_bdd (t : ℝ) : |fcI S R1 R2 Q n t| ≤ ((P.h1 + P.h2 + P.p) * (|((sz Q R1 : ℤ) : ℝ)| + ((Q : ℕ) : ℝ) + |((cz Q n R1 R2 : ℤ) : ℝ)| + ((mN Q n : ℕ) : ℝ)) + P.h2 * (2 * ((mN Q n : ℕ) : ℝ) + |((cz Q n R1 R2 : ℤ) : ℝ)| + ((Q : ℕ) : ℝ))) + ((P.h1 + P.h2 + P.p) + 2 * P.h2) * (P.lam * (P.L1 + P.L2)) := by
  unfold fcI
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_le_of_le_ofReal (CB_nonneg (P := P) R1 R2 Q n) (lintegral_cI_le S R1 R2 Q n t)

theorem fcI_tendsto (hlam : 0 < P.lam) :
    Tendsto (fcI S R1 R2 Q n) atTop (𝓝 (P.invCost n Q ((R1 : ℝ) + ((Q : ℕ) : ℝ)) ((R2 : ℝ) - (R1 : ℝ)))) := by
  have hm := mN_pos Q n
  have hm' : (0 : ℤ) < ((mN Q n : ℕ) : ℤ) := by exact_mod_cast hm
  have hEr : ∀ y : ℝ, (∫⁻ ω, ENNReal.ofReal ((((S.N y ω + cz Q n R1 R2) % ((mN Q n : ℕ) : ℤ) : ℤ)) : ℝ) ∂S.ν).toReal
      = ∑ a ∈ Finset.Ico (0 : ℤ) (mN Q n), (S.shLaw (mN Q n) y (cz Q n R1 R2) a).toReal * (a : ℝ) := by
    intro y
    rw [S.lintegral_res_val (mN Q n) hm y (cz Q n R1 R2), ENNReal.toReal_sum (fun a _ =>
      ENNReal.mul_ne_top (S.shLaw_ne_top _ _ _ _) ENNReal.ofReal_ne_top)]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by exact_mod_cast (Finset.mem_Ico.mp ha).1)]
  have hEr_ne : ∀ y : ℝ, ∫⁻ ω, ENNReal.ofReal ((((S.N y ω + cz Q n R1 R2) % ((mN Q n : ℕ) : ℤ) : ℤ)) : ℝ) ∂S.ν ≠ ⊤ :=
    fun y => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (S.lintegral_res_le (mN Q n) hm y (cz Q n R1 R2))
  have hpx : ∀ ρ : ℤ, 0 ≤ pexp P.mu2 (fun d : ℕ => P.lossDown ((IPf Q R1 (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ) + P.h2 * ((Wf Q (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ)) := fun ρ => pexp_nonneg P.mu2_nonneg (fun d =>
    add_nonneg (P.lossDown_nonneg _) (mul_nonneg P.h2_nonneg (by exact_mod_cast Wf_nonneg Q _)))
  have hform : ∀ t, P.L1 + P.L2 ≤ t → fcI S R1 R2 Q n t
      = ∑ ρ ∈ Finset.Ico (0 : ℤ) (mN Q n), (S.shLaw (mN Q n) (t - P.L1 - P.L2) (cz Q n R1 R2) ρ).toReal * (pexp P.mu2 (fun d : ℕ => P.lossDown ((IPf Q R1 (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ) + P.h2 * ((Wf Q (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ)))
        + P.h2 * (P.lam * P.L1 + ∑ a ∈ Finset.Ico (0 : ℤ) (mN Q n),
            (S.shLaw (mN Q n) (t - P.L1 - P.L2) (cz Q n R1 R2) a).toReal * (a : ℝ))
        - P.h2 * ∑ a ∈ Finset.Ico (0 : ℤ) (mN Q n), (S.shLaw (mN Q n) (t - P.L2) (cz Q n R1 R2) a).toReal * (a : ℝ) := by
    intro t ht
    have key := lintegral_cI_asym S R1 R2 Q n ht
    have hF := lintegral_cI_ne_top S R1 R2 Q n t
    have hsum_ne : ∑ ρ ∈ Finset.Ico (0 : ℤ) (mN Q n), S.shLaw (mN Q n) (t - P.L1 - P.L2) (cz Q n R1 R2) ρ
        * ENNReal.ofReal (pexp P.mu2 (fun d : ℕ => P.lossDown ((IPf Q R1 (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ) + P.h2 * ((Wf Q (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ))) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr (fun ρ _ => ENNReal.mul_ne_top (S.shLaw_ne_top _ _ _ _) ENNReal.ofReal_ne_top)
    have h1 := congrArg ENNReal.toReal key
    rw [ENNReal.toReal_add hF (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hEr_ne _)),
      ENNReal.toReal_add hsum_ne (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hEr_ne _⟩)),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_add ENNReal.ofReal_ne_top (hEr_ne _),
      ENNReal.toReal_ofReal P.h2_nonneg, ENNReal.toReal_ofReal (mul_nonneg P.lam_nonneg P.L1_nonneg),
      hEr, hEr, ENNReal.toReal_sum (fun ρ _ => ENNReal.mul_ne_top (S.shLaw_ne_top _ _ _ _)
        ENNReal.ofReal_ne_top)] at h1
    have h2 : ∀ ρ ∈ Finset.Ico (0 : ℤ) (mN Q n),
        (S.shLaw (mN Q n) (t - P.L1 - P.L2) (cz Q n R1 R2) ρ * ENNReal.ofReal (pexp P.mu2 (fun d : ℕ => P.lossDown ((IPf Q R1 (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ) + P.h2 * ((Wf Q (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ)))).toReal
          = (S.shLaw (mN Q n) (t - P.L1 - P.L2) (cz Q n R1 R2) ρ).toReal * (pexp P.mu2 (fun d : ℕ => P.lossDown ((IPf Q R1 (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ) + P.h2 * ((Wf Q (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ))) := by
      intro ρ _
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hpx ρ)]
    rw [Finset.sum_congr rfl h2] at h1
    unfold fcI
    linarith
  have hx : Tendsto (fun t : ℝ => t - P.L1 - P.L2) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun b => ⟨b + P.L1 + P.L2, fun a ha => by linarith⟩)
  have hx2 : Tendsto (fun t : ℝ => t - P.L2) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun b => ⟨b + P.L2, fun a ha => by linarith⟩)
  have hw : ∀ (g : ℝ → ℝ), Tendsto g atTop atTop → ∀ (F : ℤ → ℝ),
      Tendsto (fun t => ∑ a ∈ Finset.Ico (0 : ℤ) (mN Q n), (S.shLaw (mN Q n) (g t) (cz Q n R1 R2) a).toReal * F a)
        atTop (𝓝 (∑ a ∈ Finset.Ico (0 : ℤ) (mN Q n), (1 / ((mN Q n : ℕ) : ℝ)) * F a)) := by
    intro g hg F
    exact tendsto_finsetSum _ (fun a ha =>
      ((S.shLaw_tendsto (mN Q n) hlam hm (cz Q n R1 R2) ha).comp hg).mul_const (F a))
  have hA := hw _ hx (fun ρ => pexp P.mu2 (fun d : ℕ => P.lossDown ((IPf Q R1 (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ) + P.h2 * ((Wf Q (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ)))
  have hB := hw _ hx (fun a => (a : ℝ))
  have hC := hw _ hx2 (fun a => (a : ℝ))
  have hlim := (hA.add ((hB.const_add (P.lam * P.L1)).const_mul P.h2)).sub (hC.const_mul P.h2)
  have hval : (∑ ρ ∈ Finset.Ico (0 : ℤ) (mN Q n), (1 / ((mN Q n : ℕ) : ℝ)) * (pexp P.mu2 (fun d : ℕ => P.lossDown ((IPf Q R1 (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ) + P.h2 * ((Wf Q (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ))))
      + P.h2 * (P.lam * P.L1 + ∑ a ∈ Finset.Ico (0 : ℤ) (mN Q n), (1 / ((mN Q n : ℕ) : ℝ)) * (a : ℝ))
      - P.h2 * ∑ a ∈ Finset.Ico (0 : ℤ) (mN Q n), (1 / ((mN Q n : ℕ) : ℝ)) * (a : ℝ) = P.invCost n Q ((R1 : ℝ) + ((Q : ℕ) : ℝ)) ((R2 : ℝ) - (R1 : ℝ)) := by
    rw [cycle_identity P Q n R1 R2]
    unfold Params.H0
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (P.L1 + P.L2)] with t ht
  rw [hform t ht]

lemma lintegral_match_id {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ ω, ENNReal.ofReal ((((Q : ℕ) : ℤ) * (Classical'.matchCount S (ctrl R1 R2 Q n) T ω - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω) : ℤ) : ℝ) ∂S.ν + ∫⁻ ω, (ENNReal.ofReal (((S.N (T) ω % ((Q : ℕ) : ℤ) : ℤ)) : ℝ) + ENNReal.ofReal (((((Q : ℕ) : ℤ) * max ((S.N (T) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (T - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) / ((Q : ℕ) : ℤ)) 0 : ℤ)) : ℝ)) ∂S.ν
      = ENNReal.ofReal (P.lam * T) + ∫⁻ ω, (ENNReal.ofReal (((S.N (0) ω % ((Q : ℕ) : ℤ) : ℤ)) : ℝ) + ENNReal.ofReal (((((Q : ℕ) : ℤ) * max ((S.N (0) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (0 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) / ((Q : ℕ) : ℤ)) 0 : ℤ)) : ℝ)) ∂S.ν := by
  have hm := mN_pos Q n
  have hq : (0 : ℤ) < ((Q : ℕ) : ℤ) := by exact_mod_cast Q.pos
  have hL2 := P.L2_nonneg
  have hμ := P.mu2_nonneg
  have hdvd : ((Q : ℕ) : ℤ) ∣ ((mN Q n : ℕ) : ℤ) := ⟨((n : ℕ) : ℤ), by rw [mN_cast]; ring⟩
  have hpt : ∀ ω, ENNReal.ofReal ((((Q : ℕ) : ℤ) * (Classical'.matchCount S (ctrl R1 R2 Q n) T ω - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω) : ℤ) : ℝ) + (ENNReal.ofReal ((S.N T ω % ((Q : ℕ) : ℤ) : ℤ) : ℝ)
      + ENNReal.ofReal ((((Q : ℕ) : ℤ) * max ((S.N (T) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (T - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) / ((Q : ℕ) : ℤ)) 0 : ℤ) : ℝ))
      = ENNReal.ofReal ((S.N T ω - S.N 0 ω : ℤ) : ℝ) + (ENNReal.ofReal ((S.N 0 ω % ((Q : ℕ) : ℤ) : ℤ) : ℝ)
      + ENNReal.ofReal ((((Q : ℕ) : ℤ) * max ((S.N (0) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (0 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) / ((Q : ℕ) : ℤ)) 0 : ℤ) : ℝ)) := by
    intro ω
    have h1 := QmatchCount_eq S R1 R2 Q n T ω
    have h2 := QmatchCount_eq S R1 R2 Q n 0 ω
    have hM : Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω
        ≤ Classical'.matchCount S (ctrl R1 R2 Q n) T ω :=
      Classical'.matchCount_mono S (ctrl R1 R2 Q n) ω hT
    have hA : (0 : ℝ) ≤ ((((Q : ℕ) : ℤ) * (Classical'.matchCount S (ctrl R1 R2 Q n) T ω - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω) : ℤ) : ℝ) := by exact_mod_cast mul_nonneg hq.le (by linarith)
    have hB : (0 : ℝ) ≤ ((S.N T ω % ((Q : ℕ) : ℤ) : ℤ) : ℝ) := by exact_mod_cast Int.emod_nonneg (S.N T ω) hq.ne'
    have hC : (0 : ℝ) ≤ ((((Q : ℕ) : ℤ) * max ((S.N (T) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (T - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) / ((Q : ℕ) : ℤ)) 0 : ℤ) : ℝ) := by exact_mod_cast Qmax_nonneg Q _
    have hD : (0 : ℝ) ≤ ((S.N T ω - S.N 0 ω : ℤ) : ℝ) := by
      exact_mod_cast S.incr_nonneg hT ω
    have hE : (0 : ℝ) ≤ ((S.N 0 ω % ((Q : ℕ) : ℤ) : ℤ) : ℝ) := by exact_mod_cast Int.emod_nonneg (S.N 0 ω) hq.ne'
    have hF : (0 : ℝ) ≤ ((((Q : ℕ) : ℤ) * max ((S.N (0) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (0 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) / ((Q : ℕ) : ℤ)) 0 : ℤ) : ℝ) := by exact_mod_cast Qmax_nonneg Q _
    have hz : ((Q : ℕ) : ℤ) * (Classical'.matchCount S (ctrl R1 R2 Q n) T ω - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω) + (S.N T ω % ((Q : ℕ) : ℤ) + ((Q : ℕ) : ℤ) * max ((S.N (T) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (T - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) / ((Q : ℕ) : ℤ)) 0) = (S.N T ω - S.N 0 ω) + (S.N 0 ω % ((Q : ℕ) : ℤ) + ((Q : ℕ) : ℤ) * max ((S.N (0) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (0 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) / ((Q : ℕ) : ℤ)) 0) := by
      rw [mul_sub, h1, h2]; ring
    rw [← ENNReal.ofReal_add hB hC, ← ENNReal.ofReal_add hA (add_nonneg hB hC),
      ← ENNReal.ofReal_add hE hF, ← ENNReal.ofReal_add hD (add_nonneg hE hF)]
    congr 1
    exact_mod_cast hz
  have m6 : Measurable (fun ω => ENNReal.ofReal ((((Q : ℕ) : ℤ) * (Classical'.matchCount S (ctrl R1 R2 Q n) T ω - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω) : ℤ) : ℝ)) := by
    have h := (measurable_of_countable (fun z : ℤ × ℤ => ENNReal.ofReal
      ((((Q : ℕ) : ℤ) * (z.1 - z.2) : ℤ) : ℝ))).comp
      ((match_meas S R1 R2 Q n T).prodMk (match_meas S R1 R2 Q n 0))
    exact h
  have mN0 : Measurable (fun ω => ENNReal.ofReal (((S.N T ω - S.N 0 ω : ℤ) : ℝ))) := by
    have h := meas_N2 S (fun z : ℤ × ℤ => ENNReal.ofReal (((z.1 - z.2 : ℤ) : ℝ))) T 0
    exact h
  have hint := lintegral_congr (μ := S.ν) hpt
  rw [lintegral_add_left m6, lintegral_add_left mN0, S.lintegral_incr_val hT, sub_zero] at hint
  exact hint

lemma lintegral_B_le (t : ℝ) : ∫⁻ ω, (ENNReal.ofReal (((S.N (t) ω % ((Q : ℕ) : ℤ) : ℤ)) : ℝ) + ENNReal.ofReal (((((Q : ℕ) : ℤ) * max ((S.N (t) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) / ((Q : ℕ) : ℤ)) 0 : ℤ)) : ℝ)) ∂S.ν ≤ ENNReal.ofReal ((((Q : ℕ) : ℝ) + |((cz Q n R1 R2 : ℤ) : ℝ)| + ((mN Q n : ℕ) : ℝ) + P.lam * P.L2)) := by
  have hm := mN_pos Q n
  have hm' : (0 : ℤ) < ((mN Q n : ℕ) : ℤ) := by exact_mod_cast hm
  have hq : (0 : ℤ) < ((Q : ℕ) : ℤ) := by exact_mod_cast Q.pos
  have hv : t - P.L2 ≤ t := by linarith [P.L2_nonneg]
  have hc0 : (0 : ℝ) ≤ ((Q : ℕ) : ℝ) + |((cz Q n R1 R2 : ℤ) : ℝ)| + ((mN Q n : ℕ) : ℝ) := by positivity
  have hmeas : Measurable (fun ω => ENNReal.ofReal (((S.N t ω - S.N (t - P.L2) ω : ℤ) : ℝ))) := by
    have h := meas_N2 S (fun z : ℤ × ℤ => ENNReal.ofReal (((z.1 - z.2 : ℤ) : ℝ))) t (t - P.L2)
    exact h
  calc ∫⁻ ω, (ENNReal.ofReal (((S.N (t) ω % ((Q : ℕ) : ℤ) : ℤ)) : ℝ) + ENNReal.ofReal (((((Q : ℕ) : ℤ) * max ((S.N (t) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) / ((Q : ℕ) : ℤ)) 0 : ℤ)) : ℝ)) ∂S.ν
      ≤ ∫⁻ ω, (ENNReal.ofReal (((Q : ℕ) : ℝ) + |((cz Q n R1 R2 : ℤ) : ℝ)| + ((mN Q n : ℕ) : ℝ))
          + ENNReal.ofReal (((S.N t ω - S.N (t - P.L2) ω : ℤ) : ℝ))) ∂S.ν := by
        refine lintegral_mono (fun ω => ?_)
        have r0 := Int.emod_add_mul_ediv (S.N (t - P.L2) ω + cz Q n R1 R2) ((mN Q n : ℕ) : ℤ)
        have r0a := Int.emod_nonneg (S.N (t - P.L2) ω + cz Q n R1 R2) hm'.ne'
        have r0b := Int.emod_lt_of_pos (S.N (t - P.L2) ω + cz Q n R1 R2) hm'
        have q0a := Int.emod_nonneg (S.N t ω) hq.ne'
        have q0b := Int.emod_lt_of_pos (S.N t ω) hq
        have hmo := S.N_mono ω hv
        have hc1 := le_abs_self (cz Q n R1 R2)
        have hc2 := neg_abs_le (cz Q n R1 R2)
        have hY : |S.N t ω - ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))|
            ≤ (S.N t ω - S.N (t - P.L2) ω) + |cz Q n R1 R2| + ((mN Q n : ℕ) : ℤ) := by
          rw [abs_le]; constructor <;> linarith
        have hQm := Qmax_le Q (S.N t ω - ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)))
        have hQn := Qmax_nonneg Q (S.N t ω - ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)))
        have hz : S.N t ω % ((Q : ℕ) : ℤ) + ((Q : ℕ) : ℤ) * max ((S.N t ω - ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) / ((Q : ℕ) : ℤ)) 0
            ≤ ((Q : ℕ) : ℤ) + |cz Q n R1 R2| + ((mN Q n : ℕ) : ℤ) + (S.N t ω - S.N (t - P.L2) ω) := by linarith
        have hzr : (((S.N t ω % ((Q : ℕ) : ℤ) : ℤ)) : ℝ) + (((((Q : ℕ) : ℤ) * max ((S.N t ω - ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) / ((Q : ℕ) : ℤ)) 0 : ℤ)) : ℝ)
            ≤ (((Q : ℕ) : ℝ) + |((cz Q n R1 R2 : ℤ) : ℝ)| + ((mN Q n : ℕ) : ℝ)) + ((S.N t ω - S.N (t - P.L2) ω : ℤ) : ℝ) := by
          have h := (Int.cast_le (R := ℝ)).mpr hz
          push_cast at h ⊢
          linarith
        have e1 : (0 : ℝ) ≤ (((S.N t ω % ((Q : ℕ) : ℤ) : ℤ)) : ℝ) := by exact_mod_cast q0a
        have e2 : (0 : ℝ) ≤ (((((Q : ℕ) : ℤ) * max ((S.N t ω - ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) / ((Q : ℕ) : ℤ)) 0 : ℤ)) : ℝ) := by
          exact_mod_cast hQn
        have e3 : (0 : ℝ) ≤ ((S.N t ω - S.N (t - P.L2) ω : ℤ) : ℝ) := by exact_mod_cast S.incr_nonneg hv ω
        rw [← ENNReal.ofReal_add e1 e2, ← ENNReal.ofReal_add hc0 e3]
        exact ENNReal.ofReal_le_ofReal hzr
    _ = ENNReal.ofReal ((((Q : ℕ) : ℝ) + |((cz Q n R1 R2 : ℤ) : ℝ)| + ((mN Q n : ℕ) : ℝ) + P.lam * P.L2)) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          S.lintegral_incr_val hv, ← ENNReal.ofReal_add hc0 (mul_nonneg P.lam_nonneg (by linarith))]
        congr 1
        ring

lemma lintegral_setup_split {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ ω, ENNReal.ofReal (P.K1 * ((Classical'.matchCount S (ctrl R1 R2 Q n) T ω - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω : ℤ) : ℝ) + P.K2 * ((Classical'.ordCount S (ctrl R1 R2 Q n) T ω - Classical'.ordCount S (ctrl R1 R2 Q n) 0 ω : ℤ) : ℝ)) ∂S.ν = ENNReal.ofReal (P.K1 / ((Q : ℕ) : ℝ)) * ∫⁻ ω, ENNReal.ofReal ((((Q : ℕ) : ℤ) * (Classical'.matchCount S (ctrl R1 R2 Q n) T ω - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω) : ℤ) : ℝ) ∂S.ν
      + ENNReal.ofReal (P.K2 / ((mN Q n : ℕ) : ℝ)) * ∫⁻ ω, ENNReal.ofReal (((((mN Q n : ℕ) : ℤ) * ((S.N T ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ) - (S.N 0 ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)) : ℤ)) : ℝ) ∂S.ν := by
  have hm := mN_pos Q n
  have hm' : (0 : ℤ) < ((mN Q n : ℕ) : ℤ) := by exact_mod_cast hm
  have hq : (0 : ℤ) < ((Q : ℕ) : ℤ) := by exact_mod_cast Q.pos
  have hQ : (0 : ℝ) < ((Q : ℕ) : ℝ) := by exact_mod_cast Q.pos
  have hmR : (0 : ℝ) < ((mN Q n : ℕ) : ℝ) := by exact_mod_cast hm
  have hK1 : 0 ≤ P.K1 / ((Q : ℕ) : ℝ) := div_nonneg P.K1_nonneg hQ.le
  have hK2 : 0 ≤ P.K2 / ((mN Q n : ℕ) : ℝ) := div_nonneg P.K2_nonneg hmR.le
  have hpt : ∀ ω, ENNReal.ofReal (P.K1 * ((Classical'.matchCount S (ctrl R1 R2 Q n) T ω
        - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω : ℤ) : ℝ)
      + P.K2 * ((Classical'.ordCount S (ctrl R1 R2 Q n) T ω
        - Classical'.ordCount S (ctrl R1 R2 Q n) 0 ω : ℤ) : ℝ))
      = ENNReal.ofReal (P.K1 / ((Q : ℕ) : ℝ)) * ENNReal.ofReal ((((Q : ℕ) : ℤ) * (Classical'.matchCount S (ctrl R1 R2 Q n) T ω - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω) : ℤ) : ℝ)
        + ENNReal.ofReal (P.K2 / ((mN Q n : ℕ) : ℝ)) * ENNReal.ofReal ((((mN Q n : ℕ) : ℤ) * ((S.N (T) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ) - (S.N (0) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)) : ℤ) : ℝ) := by
    intro ω
    have hM : Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω
        ≤ Classical'.matchCount S (ctrl R1 R2 Q n) T ω :=
      Classical'.matchCount_mono S (ctrl R1 R2 Q n) ω hT
    have hO : Classical'.ordCount S (ctrl R1 R2 Q n) 0 ω
        ≤ Classical'.ordCount S (ctrl R1 R2 Q n) T ω :=
      Classical'.ordCount_mono S (ctrl R1 R2 Q n) ω hT
    rw [ordCount_eq, ordCount_eq] at hO ⊢
    have hA : (0 : ℝ) ≤ ((((Q : ℕ) : ℤ) * (Classical'.matchCount S (ctrl R1 R2 Q n) T ω - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω) : ℤ) : ℝ) := by exact_mod_cast mul_nonneg hq.le (by linarith)
    have hB : (0 : ℝ) ≤ ((((mN Q n : ℕ) : ℤ) * ((S.N (T) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ) - (S.N (0) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)) : ℤ) : ℝ) := by exact_mod_cast mul_nonneg hm'.le (by linarith)
    rw [← ENNReal.ofReal_mul hK1, ← ENNReal.ofReal_mul hK2,
      ← ENNReal.ofReal_add (mul_nonneg hK1 hA) (mul_nonneg hK2 hB)]
    congr 1
    push_cast
    field_simp
  have m7 : Measurable (fun ω => ENNReal.ofReal ((((Q : ℕ) : ℤ) * (Classical'.matchCount S (ctrl R1 R2 Q n) T ω - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω) : ℤ) : ℝ)) := by
    have h := (measurable_of_countable (fun z : ℤ × ℤ => ENNReal.ofReal
      ((((Q : ℕ) : ℤ) * (z.1 - z.2) : ℤ) : ℝ))).comp
      ((match_meas S R1 R2 Q n T).prodMk (match_meas S R1 R2 Q n 0))
    exact h
  have m8 : Measurable (fun ω => ENNReal.ofReal ((((mN Q n : ℕ) : ℤ) * ((S.N (T) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ) - (S.N (0) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)) : ℤ) : ℝ)) := by
    have h := meas_N2 S (fun z : ℤ × ℤ => ENNReal.ofReal ((((mN Q n : ℕ) : ℤ)
      * ((z.1 + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ) - (z.2 + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)) : ℤ) : ℝ)) T 0
    exact h
  rw [lintegral_congr hpt, lintegral_add_left (m7.const_mul _), lintegral_const_mul _ m7,
    lintegral_const_mul _ m8]

lemma setup_bdd {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ ω, ENNReal.ofReal (P.K1 * ((Classical'.matchCount S (ctrl R1 R2 Q n) T ω - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω : ℤ) : ℝ) + P.K2 * ((Classical'.ordCount S (ctrl R1 R2 Q n) T ω - Classical'.ordCount S (ctrl R1 R2 Q n) 0 ω : ℤ) : ℝ)) ∂S.ν ≠ ⊤ ∧
    |(∫⁻ ω, ENNReal.ofReal (P.K1 * ((Classical'.matchCount S (ctrl R1 R2 Q n) T ω - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω : ℤ) : ℝ) + P.K2 * ((Classical'.ordCount S (ctrl R1 R2 Q n) T ω - Classical'.ordCount S (ctrl R1 R2 Q n) 0 ω : ℤ) : ℝ)) ∂S.ν).toReal - (P.k1 / ((Q : ℕ) : ℝ) + P.k2 / (((n : ℕ) : ℝ) * ((Q : ℕ) : ℝ))) * T|
      ≤ P.K1 / ((Q : ℕ) : ℝ) * ((((Q : ℕ) : ℝ) + |((cz Q n R1 R2 : ℤ) : ℝ)| + ((mN Q n : ℕ) : ℝ) + P.lam * P.L2)) + P.K2 / ((mN Q n : ℕ) : ℝ) * ((mN Q n : ℕ) : ℝ) := by
  have hm := mN_pos Q n
  have hQ : (0 : ℝ) < ((Q : ℕ) : ℝ) := by exact_mod_cast Q.pos
  have hmR : (0 : ℝ) < ((mN Q n : ℕ) : ℝ) := by exact_mod_cast hm
  have hK1 : 0 ≤ P.K1 / ((Q : ℕ) : ℝ) := div_nonneg P.K1_nonneg hQ.le
  have hK2 : 0 ≤ P.K2 / ((mN Q n : ℕ) : ℝ) := div_nonneg P.K2_nonneg hmR.le
  have hBc : 0 ≤ (((Q : ℕ) : ℝ) + |((cz Q n R1 R2 : ℤ) : ℝ)| + ((mN Q n : ℕ) : ℝ) + P.lam * P.L2) := by have := P.lam_nonneg; have := P.L2_nonneg; positivity

  have hB_ne : ∀ t, ∫⁻ ω, (ENNReal.ofReal (((S.N (t) ω % ((Q : ℕ) : ℤ) : ℤ)) : ℝ) + ENNReal.ofReal (((((Q : ℕ) : ℤ) * max ((S.N (t) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) / ((Q : ℕ) : ℤ)) 0 : ℤ)) : ℝ)) ∂S.ν ≠ ⊤ := fun t =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lintegral_B_le S R1 R2 Q n t)
  obtain ⟨hM_ne, hM⟩ := toReal_add_eq (lintegral_match_id S R1 R2 Q n hT) (hB_ne T)
    ENNReal.ofReal_ne_top (hB_ne 0)
  rw [ENNReal.toReal_ofReal (mul_nonneg P.lam_nonneg hT)] at hM
  have hBT := ENNReal.toReal_le_of_le_ofReal hBc (lintegral_B_le S R1 R2 Q n T)
  have hB0 := ENNReal.toReal_le_of_le_ofReal hBc (lintegral_B_le S R1 R2 Q n 0)
  have hBT0 : 0 ≤ (∫⁻ ω, (ENNReal.ofReal (((S.N (T) ω % ((Q : ℕ) : ℤ) : ℤ)) : ℝ) + ENNReal.ofReal (((((Q : ℕ) : ℤ) * max ((S.N (T) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (T - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) / ((Q : ℕ) : ℤ)) 0 : ℤ)) : ℝ)) ∂S.ν).toReal := ENNReal.toReal_nonneg
  have hB00 : 0 ≤ (∫⁻ ω, (ENNReal.ofReal (((S.N (0) ω % ((Q : ℕ) : ℤ) : ℤ)) : ℝ) + ENNReal.ofReal (((((Q : ℕ) : ℤ) * max ((S.N (0) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (0 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) / ((Q : ℕ) : ℤ)) 0 : ℤ)) : ℝ)) ∂S.ν).toReal := ENNReal.toReal_nonneg

  have hR_ne : ∀ x, ∫⁻ ω, ENNReal.ofReal ((((S.N x ω + cz Q n R1 R2) % ((mN Q n : ℕ) : ℤ) : ℤ)) : ℝ) ∂S.ν ≠ ⊤ := fun x =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (S.lintegral_res_le (mN Q n) hm x (cz Q n R1 R2))
  obtain ⟨hO_ne, hO⟩ := toReal_add_eq (S.lintegral_ordIncr (mN Q n) hm hT (cz Q n R1 R2)) (hR_ne T)
    ENNReal.ofReal_ne_top (hR_ne 0)
  rw [ENNReal.toReal_ofReal (mul_nonneg P.lam_nonneg (by linarith)), sub_zero] at hO
  have hRT := ENNReal.toReal_le_of_le_ofReal hmR.le (S.lintegral_res_le (mN Q n) hm T (cz Q n R1 R2))
  have hR0 := ENNReal.toReal_le_of_le_ofReal hmR.le (S.lintegral_res_le (mN Q n) hm 0 (cz Q n R1 R2))
  have hRT0 : 0 ≤ (∫⁻ ω, ENNReal.ofReal ((((S.N T ω + cz Q n R1 R2) % ((mN Q n : ℕ) : ℤ) : ℤ)) : ℝ) ∂S.ν).toReal :=
    ENNReal.toReal_nonneg
  have hR00 : 0 ≤ (∫⁻ ω, ENNReal.ofReal ((((S.N 0 ω + cz Q n R1 R2) % ((mN Q n : ℕ) : ℤ) : ℤ)) : ℝ) ∂S.ν).toReal :=
    ENNReal.toReal_nonneg
  have hsplit := lintegral_setup_split S R1 R2 Q n hT
  have hne : ∫⁻ ω, ENNReal.ofReal (P.K1 * ((Classical'.matchCount S (ctrl R1 R2 Q n) T ω - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω : ℤ) : ℝ) + P.K2 * ((Classical'.ordCount S (ctrl R1 R2 Q n) T ω - Classical'.ordCount S (ctrl R1 R2 Q n) 0 ω : ℤ) : ℝ)) ∂S.ν ≠ ⊤ := by
    rw [hsplit]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM_ne,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hO_ne⟩
  refine ⟨hne, ?_⟩
  rw [hsplit, ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM_ne)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hO_ne),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK1, ENNReal.toReal_ofReal hK2]
  have ek : P.k1 / ((Q : ℕ) : ℝ) + P.k2 / (((n : ℕ) : ℝ) * ((Q : ℕ) : ℝ)) = P.K1 / ((Q : ℕ) : ℝ) * P.lam + P.K2 / ((mN Q n : ℕ) : ℝ) * P.lam := by
    unfold Params.k1 Params.k2
    rw [mN_castR]
    ring
  rw [ek]
  have d1 : |(∫⁻ ω, ENNReal.ofReal ((((Q : ℕ) : ℤ) * (Classical'.matchCount S (ctrl R1 R2 Q n) T ω - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω) : ℤ) : ℝ) ∂S.ν).toReal - P.lam * T| ≤ (((Q : ℕ) : ℝ) + |((cz Q n R1 R2 : ℤ) : ℝ)| + ((mN Q n : ℕ) : ℝ) + P.lam * P.L2) := by
    rw [abs_le]; constructor <;> linarith
  have d2 : |(∫⁻ ω, ENNReal.ofReal (((((mN Q n : ℕ) : ℤ) * ((S.N T ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ) - (S.N 0 ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)) : ℤ)) : ℝ) ∂S.ν).toReal - P.lam * T| ≤ ((mN Q n : ℕ) : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  have e : P.K1 / ((Q : ℕ) : ℝ) * (∫⁻ ω, ENNReal.ofReal ((((Q : ℕ) : ℤ) * (Classical'.matchCount S (ctrl R1 R2 Q n) T ω - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω) : ℤ) : ℝ) ∂S.ν).toReal + P.K2 / ((mN Q n : ℕ) : ℝ) * (∫⁻ ω, ENNReal.ofReal (((((mN Q n : ℕ) : ℤ) * ((S.N T ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ) - (S.N 0 ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)) : ℤ)) : ℝ) ∂S.ν).toReal
      - (P.K1 / ((Q : ℕ) : ℝ) * P.lam + P.K2 / ((mN Q n : ℕ) : ℝ) * P.lam) * T
      = P.K1 / ((Q : ℕ) : ℝ) * ((∫⁻ ω, ENNReal.ofReal ((((Q : ℕ) : ℤ) * (Classical'.matchCount S (ctrl R1 R2 Q n) T ω - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω) : ℤ) : ℝ) ∂S.ν).toReal - P.lam * T)
        + P.K2 / ((mN Q n : ℕ) : ℝ) * ((∫⁻ ω, ENNReal.ofReal (((((mN Q n : ℕ) : ℤ) * ((S.N T ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ) - (S.N 0 ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)) : ℤ)) : ℝ) ∂S.ν).toReal - P.lam * T) := by ring
  rw [e]
  calc _ ≤ |P.K1 / ((Q : ℕ) : ℝ) * ((∫⁻ ω, ENNReal.ofReal ((((Q : ℕ) : ℤ) * (Classical'.matchCount S (ctrl R1 R2 Q n) T ω - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω) : ℤ) : ℝ) ∂S.ν).toReal - P.lam * T)|
        + |P.K2 / ((mN Q n : ℕ) : ℝ) * ((∫⁻ ω, ENNReal.ofReal (((((mN Q n : ℕ) : ℤ) * ((S.N T ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ) - (S.N 0 ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)) : ℤ)) : ℝ) ∂S.ν).toReal - P.lam * T)| := abs_add_le _ _
    _ = P.K1 / ((Q : ℕ) : ℝ) * |(∫⁻ ω, ENNReal.ofReal ((((Q : ℕ) : ℤ) * (Classical'.matchCount S (ctrl R1 R2 Q n) T ω - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω) : ℤ) : ℝ) ∂S.ν).toReal - P.lam * T|
        + P.K2 / ((mN Q n : ℕ) : ℝ) * |(∫⁻ ω, ENNReal.ofReal (((((mN Q n : ℕ) : ℤ) * ((S.N T ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ) - (S.N 0 ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)) : ℤ)) : ℝ) ∂S.ν).toReal - P.lam * T| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hK1, abs_of_nonneg hK2]
    _ ≤ _ := by gcongr

lemma cI_joint_meas :
    Measurable (fun p : S.Ω × ℝ => ENNReal.ofReal (Classical'.cI S (ctrl R1 R2 Q n) p.2 p.1)) := by
  have e : (fun p : S.Ω × ℝ => ENNReal.ofReal (Classical'.cI S (ctrl R1 R2 Q n) p.2 p.1))
      = (fun z : ℤ × ℤ × ℤ × ℤ => ENNReal.ofReal (phi (P.h1 + P.h2) P.p (((IPf Q R1 (z.2.1 - ((mN Q n : ℕ) : ℤ) * ((z.2.2.1 + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) : ℤ) : ℝ) - ((z.1 - z.2.1 : ℤ) : ℝ)) + P.h2 * ((((mN Q n : ℕ) : ℤ) * ((z.2.2.2 + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ) - (z.2.2.1 + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)) : ℤ) : ℝ)
          + P.h2 * ((Wf Q (z.2.1 - ((mN Q n : ℕ) : ℤ) * ((z.2.2.1 + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) : ℤ) : ℝ)))
        ∘ (fun p : S.Ω × ℝ => (S.N p.2 p.1, S.N (p.2 - P.L1) p.1, S.N (p.2 - P.L1 - P.L2) p.1,
            S.N (p.2 - P.L2) p.1)) := by
    funext p
    exact congrArg ENNReal.ofReal (cI_eq S R1 R2 Q n p.2 p.1)
  rw [e]
  have hs : ∀ g : S.Ω × ℝ → ℝ, Measurable g → Measurable (fun p : S.Ω × ℝ => S.N (g p) p.1) := by
    intro g hg
    have h := S.N_joint.comp (measurable_fst.prodMk hg)
    exact h
  refine (measurable_of_countable _).comp ?_
  exact (hs (fun p => p.2) measurable_snd).prodMk
    ((hs (fun p => p.2 - P.L1) (measurable_snd.sub_const _)).prodMk
    ((hs (fun p => p.2 - P.L1 - P.L2) ((measurable_snd.sub_const _).sub_const _)).prodMk
      (hs (fun p => p.2 - P.L2) (measurable_snd.sub_const _))))

theorem lotCost_eq (hlam : 0 < P.lam) :
    classicalLotCost P S (ctrl R1 R2 Q n) = ENNReal.ofReal (P.classicalFormula R1 R2 Q n) := by
  have hm := mN_pos Q n
  have hQ : (0 : ℝ) < ((Q : ℕ) : ℝ) := by exact_mod_cast Q.pos
  have hmeas := cI_joint_meas S R1 R2 Q n
  have hFm : Measurable (fun t => ∫⁻ ω, ENNReal.ofReal (Classical'.cI S (ctrl R1 R2 Q n) t ω) ∂S.ν) :=
    hmeas.lintegral_prod_left'
  have hfm : Measurable (fcI S R1 R2 Q n) := hFm.ennreal_toReal
  have hfb := fcI_bdd S R1 R2 Q n
  have hii := iiOfBdd hfm hfb
  have hces := cesaro_Ioc hfm hfb (fcI_tendsto S R1 R2 Q n hlam)
  have hz := tendsto_of_bdd (a := fun T => (∫⁻ ω, ENNReal.ofReal (P.K1 * ((Classical'.matchCount S (ctrl R1 R2 Q n) T ω - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω : ℤ) : ℝ) + P.K2 * ((Classical'.ordCount S (ctrl R1 R2 Q n) T ω - Classical'.ordCount S (ctrl R1 R2 Q n) 0 ω : ℤ) : ℝ)) ∂S.ν).toReal)
    (fun T hT => (setup_bdd S R1 R2 Q n hT).2)
  have hlim : Tendsto (fun T => T⁻¹ * ((∫ t in Set.Ioc 0 T, fcI S R1 R2 Q n t)
      + (∫⁻ ω, ENNReal.ofReal (P.K1 * ((Classical'.matchCount S (ctrl R1 R2 Q n) T ω - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω : ℤ) : ℝ) + P.K2 * ((Classical'.ordCount S (ctrl R1 R2 Q n) T ω - Classical'.ordCount S (ctrl R1 R2 Q n) 0 ω : ℤ) : ℝ)) ∂S.ν).toReal)) atTop (𝓝 (P.classicalFormula R1 R2 Q n)) := by
    have h := hces.add hz
    have e : P.invCost n Q ((R1 : ℝ) + ((Q : ℕ) : ℝ)) ((R2 : ℝ) - (R1 : ℝ)) + (P.k1 / ((Q : ℕ) : ℝ) + P.k2 / (((n : ℕ) : ℝ) * ((Q : ℕ) : ℝ))) = P.classicalFormula R1 R2 Q n := by
      unfold Params.classicalFormula
      ring
    rw [e] at h
    refine h.congr (fun T => ?_)
    ring
  unfold classicalLotCost longRunCost
  have hev : ∀ᶠ T in atTop, ENNReal.ofReal T⁻¹ * ∫⁻ ω, ((∫⁻ t in Set.Ioc 0 T,
      ENNReal.ofReal (Classical'.cI S (ctrl R1 R2 Q n) t ω)) + ENNReal.ofReal (P.K1 * ((Classical'.matchCount S (ctrl R1 R2 Q n) T ω - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω : ℤ) : ℝ) + P.K2 * ((Classical'.ordCount S (ctrl R1 R2 Q n) T ω - Classical'.ordCount S (ctrl R1 R2 Q n) 0 ω : ℤ) : ℝ))) ∂S.ν
      = ENNReal.ofReal (T⁻¹ * ((∫ t in Set.Ioc 0 T, fcI S R1 R2 Q n t)
        + (∫⁻ ω, ENNReal.ofReal (P.K1 * ((Classical'.matchCount S (ctrl R1 R2 Q n) T ω - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω : ℤ) : ℝ) + P.K2 * ((Classical'.ordCount S (ctrl R1 R2 Q n) T ω - Classical'.ordCount S (ctrl R1 R2 Q n) 0 ω : ℤ) : ℝ)) ∂S.ν).toReal)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [lintegral_add_left (Measurable.lintegral_prod_right' (ν := volume.restrict (Set.Ioc 0 T))
        hmeas),
      lintegral_lintegral_swap (μ := S.ν) (ν := volume.restrict (Set.Ioc 0 T))
        (f := fun ω t => ENNReal.ofReal (Classical'.cI S (ctrl R1 R2 Q n) t ω))
        (Measurable.aemeasurable hmeas)]
    have hint : Integrable (fcI S R1 R2 Q n) (volume.restrict (Set.Ioc 0 T)) := (hii 0 T).1
    have h0 : 0 ≤ ∫ t in Set.Ioc 0 T, fcI S R1 R2 Q n t :=
      integral_nonneg (fun t => ENNReal.toReal_nonneg)
    have h1 : ∫⁻ t in Set.Ioc 0 T, ∫⁻ ω, ENNReal.ofReal (Classical'.cI S (ctrl R1 R2 Q n) t ω) ∂S.ν
        = ENNReal.ofReal (∫ t in Set.Ioc 0 T, fcI S R1 R2 Q n t) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun t => ENNReal.toReal_nonneg))]
      exact lintegral_congr (fun t => (ENNReal.ofReal_toReal (lintegral_cI_ne_top S R1 R2 Q n t)).symm)
    rw [h1, ENNReal.ofReal_mul (inv_nonneg.mpr hT.le), ENNReal.ofReal_add h0 ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (setup_bdd S R1 R2 Q n hT.le).1]
  rw [limsup_congr hev]
  exact (ENNReal.tendsto_ofReal hlim).limsup_eq

end Expect

end Prop1

theorem exact_cost_classical_pf (P : Params) (hlam : 0 < P.lam) (S : DemandSpace P)
    (R1 R2 : ℤ) (Q n : ℕ+) :
    classicalLotCost P S ⟨(R1, R2, Q, n, 0), Q.pos⟩
        = ENNReal.ofReal (P.classicalFormula R1 R2 Q n) ∧
      classicalShipCost P S ⟨(R1, R2, Q, n, 0), Q.pos⟩
        ≤ classicalLotCost P S ⟨(R1, R2, Q, n, 0), Q.pos⟩ :=
  ⟨Prop1.lotCost_eq S R1 R2 Q n hlam, classical_ship_le_lot_pf P S _⟩

end TwoStageRnQ

namespace TwoStageRnQ

theorem _root_.solution (P : Params) (hlam : 0 < P.lam) (S : DemandSpace P)
    (R1 R2 : ℤ) (Q n : ℕ+) :
    classicalLotCost P S ⟨(R1, R2, Q, n, 0), Q.pos⟩
        = ENNReal.ofReal (P.classicalFormula R1 R2 Q n) ∧
      classicalShipCost P S ⟨(R1, R2, Q, n, 0), Q.pos⟩
        ≤ classicalLotCost P S ⟨(R1, R2, Q, n, 0), Q.pos⟩ :=
  exact_cost_classical_pf P hlam S R1 R2 Q n

end TwoStageRnQ
