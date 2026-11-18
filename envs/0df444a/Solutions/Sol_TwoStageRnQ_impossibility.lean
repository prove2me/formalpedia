-- Prove2me | solution 1 for TwoStageRnQ.impossibility
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T00:27:18.88063+00:00
-- url     : https://prove2.me/submissions/5e689a8b-841b-496c-818b-557cfde7b392

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
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Definitions.Def_TwoStageRnQ_Model
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Infix
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Finset.Sort
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

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

lemma PInt.const_mul {μ : ℝ} {f : ℕ → ℝ} (hf : PInt μ f) (c : ℝ) :
    PInt μ (fun n => c * f n) := by
  unfold PInt at hf ⊢
  simp_rw [abs_mul, mul_left_comm _ |c|]
  exact hf.mul_left |c|

lemma PInt.sum {μ : ℝ} (hμ : 0 ≤ μ) {ι : Type*} (s : Finset ι) {f : ι → ℕ → ℝ}
    (hf : ∀ i ∈ s, PInt μ (f i)) : PInt μ (fun n => ∑ i ∈ s, f i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (pint_const (μ := μ) 0)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (mem_insert_self a s)).add hμ (ih (fun i hi => hf i (mem_insert_of_mem hi)))

lemma LinGrowth.pint {μ : ℝ} (hμ : 0 ≤ μ) {f : ℕ → ℝ} (hf : LinGrowth f) : PInt μ f := by
  obtain ⟨A, B, h⟩ := hf
  exact PInt.of_abs_le hμ ((pint_const A).add hμ (pint_nat.const_mul B)) h

lemma pexp_sub {μ : ℝ} (hμ : 0 ≤ μ) {f g : ℕ → ℝ} (hf : PInt μ f) (hg : PInt μ g) :
    pexp μ (fun n => f n - g n) = pexp μ f - pexp μ g := by
  unfold pexp
  simp_rw [mul_sub]
  exact Summable.tsum_sub (hf.summable hμ) (hg.summable hμ)

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

lemma mu2_nonneg : 0 ≤ P.mu2 := mul_nonneg P.lam_nonneg P.L2_nonneg
end Params

namespace Params

variable (P : Params)

end Params

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

lemma N_joint_shift (a : ℝ) : Measurable (fun p : S.Ω × ℝ => S.N (p.2 + a) p.1) :=
  S.N_joint.comp (measurable_fst.prodMk (measurable_snd.add_const a))

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

variable (Q n : ℕ+) (R1 R2 : ℤ)

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

lemma Wf_nonneg (y : ℤ) : 0 ≤ Wf Q y := by
  unfold Wf; exact mul_nonneg (by positivity) (le_max_right _ _)

end Bounds

section Identity

variable (P : Params) (Q n : ℕ+) (R1 R2 : ℤ)

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

end Expect

end Prop1

end TwoStageRnQ

open Finset

namespace TwoStageRnQ

namespace LB

def vrel (a b : ℤ) : Prop := b = a - 1 ∨ a < b

def dstates : List ℤ → List ℤ
  | a :: b :: t => (if b = a - 1 then [a] else []) ++ dstates (b :: t)
  | _ => []

def upc : List ℤ → ℕ
  | a :: b :: t => (if b = a - 1 then 0 else 1) + upc (b :: t)
  | _ => 0

noncomputable def pcost (F : ℤ → ℝ) (k : ℝ) : List ℤ → ℝ
  | a :: b :: t => (if b = a - 1 then F a else k) + pcost F k (b :: t)
  | _ => 0

noncomputable def tcost (F : ℤ → ℝ) (k : ℝ) (a b : ℤ) : ℝ := if b = a - 1 then F a else k

def tdown (a b : ℤ) : ℕ := if b = a - 1 then 1 else 0

variable (F : ℤ → ℝ) (k : ℝ)

section Basic

lemma downCount_eq_length : ∀ l : List ℤ, downCount l = (dstates l).length
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
    rw [downCount, dstates, List.length_append, downCount_eq_length (b :: t)]
    split_ifs <;> simp

lemma pcost_eq : ∀ l : List ℤ, pcost F k l = ((dstates l).map F).sum + k * (upc l : ℝ)
  | [] => by simp [pcost, dstates, upc]
  | [_] => by simp [pcost, dstates, upc]
  | a :: b :: t => by
    rw [pcost, dstates, upc, pcost_eq (b :: t), List.map_append, List.sum_append]
    split_ifs <;> simp <;> ring

lemma snoc : ∀ (l : List ℤ) (a s : ℤ), l.getLast? = some a →
    pcost F k (l ++ [s]) = pcost F k l + tcost F k a s ∧
    downCount (l ++ [s]) = downCount l + tdown a s ∧
    dstates (l ++ [s]) = dstates l ++ (if s = a - 1 then [a] else [])
  | [], a, s, h => by simp at h
  | [x], a, s, h => by
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    subst h
    simp only [List.singleton_append, pcost, downCount, dstates, tcost, tdown]
    split_ifs <;> simp
  | x :: y :: t, a, s, h => by
    have h' : (y :: t).getLast? = some a := by
      rw [List.getLast?_cons_cons] at h; exact h
    obtain ⟨e1, e2, e3⟩ := snoc (y :: t) a s h'
    simp only [List.cons_append] at e1 e2 e3 ⊢
    refine ⟨?_, ?_, ?_⟩
    · rw [pcost, e1, pcost]; ring
    · rw [downCount, e2, downCount]; ring
    · rw [dstates, e3, dstates, List.append_assoc]

lemma split : ∀ (A : List ℤ) (s : ℤ) (B : List ℤ),
    pcost F k (A ++ s :: B) = pcost F k (A ++ [s]) + pcost F k (s :: B) ∧
    downCount (A ++ s :: B) = downCount (A ++ [s]) + downCount (s :: B)
  | [], s, B => by simp [pcost, downCount]
  | [x], s, B => by
    simp only [List.singleton_append, pcost, downCount]
    constructor <;> ring
  | x :: y :: t, s, B => by
    obtain ⟨e1, e2⟩ := split (y :: t) s B
    simp only [List.cons_append] at e1 e2 ⊢
    constructor
    · rw [pcost, e1, pcost]; ring
    · rw [downCount, e2, downCount]; ring

lemma dstates_cons_sub (a : ℤ) : ∀ t : List ℤ, (dstates t).Sublist (dstates (a :: t))
  | [] => by simp [dstates]
  | b :: t => by rw [dstates]; exact List.sublist_append_right _ _

lemma dstates_suffix : ∀ {l₁ l : List ℤ}, l₁ <:+ l → (dstates l₁).Sublist (dstates l)
  | l₁, [], h => by
    rw [List.suffix_nil] at h; subst h; exact List.Sublist.refl _
  | l₁, a :: t, h => by
    rcases List.suffix_cons_iff.mp h with h1 | h1
    · rw [h1]
    · exact (dstates_suffix h1).trans (dstates_cons_sub a t)

lemma dstates_prefix : ∀ {l₁ l : List ℤ}, l₁ <+: l → (dstates l₁).Sublist (dstates l)
  | [], l, _ => by simp [dstates]
  | [x], l, _ => by simp [dstates]
  | x :: y :: t, [], h => by simp at h
  | x :: y :: t, [a], h => by
    have := h.length_le; simp at this
  | x :: y :: t, a :: b :: u, h => by
    rw [List.cons_prefix_cons] at h
    obtain ⟨rfl, h2⟩ := h
    rw [List.cons_prefix_cons] at h2
    obtain ⟨rfl, h3⟩ := h2
    rw [dstates, dstates]
    exact List.Sublist.append_left (dstates_prefix (List.cons_prefix_cons.mpr ⟨rfl, h3⟩)) _

lemma dstates_sub_dropLast : ∀ l : List ℤ, (dstates l).Sublist l.dropLast
  | [] => by simp [dstates]
  | [_] => by simp [dstates]
  | a :: b :: t => by
    rw [dstates, List.dropLast_cons_cons]
    split_ifs
    · exact List.Sublist.cons₂ a (dstates_sub_dropLast (b :: t))
    · exact List.Sublist.cons a (dstates_sub_dropLast (b :: t))

lemma mem_dstates : ∀ {l : List ℤ} {y : ℤ}, y ∈ dstates l → y ∈ l ∧ y - 1 ∈ l
  | [], y, h => by simp [dstates] at h
  | [_], y, h => by simp [dstates] at h
  | a :: b :: t, y, h => by
    rw [dstates, List.mem_append] at h
    rcases h with h | h
    · split_ifs at h with hb
      · rw [List.mem_singleton] at h
        subst h
        exact ⟨List.mem_cons_self, by rw [← hb]; exact List.mem_cons_of_mem _ List.mem_cons_self⟩
      · simp at h
    · obtain ⟨h1, h2⟩ := mem_dstates h
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

lemma getLast?_cons_concat : ∀ (M : ℤ) (Q : List ℤ) (s : ℤ), (M :: (Q ++ [s])).getLast? = some s
  | M, [], s => rfl
  | M, x :: Q, s => by
    simp only [List.cons_append]
    rw [List.getLast?_cons_cons]
    exact getLast?_cons_concat x Q s

lemma cross : ∀ {l : List ℤ}, l.IsChain vrel → ∀ {a b y : ℤ}, l.head? = some a →
    l.getLast? = some b → b < y → y ≤ a → y ∈ dstates l
  | [], _, a, b, y, ha, _, _, _ => by simp at ha
  | [x], _, a, b, y, ha, hb, h1, h2 => by
    simp at ha hb; subst ha; subst hb; linarith
  | x :: z :: t, hv, a, b, y, ha, hb, h1, h2 => by
    simp only [List.head?_cons, Option.some.injEq] at ha
    subst ha
    rw [List.isChain_cons_cons] at hv
    obtain ⟨hr, hv'⟩ := hv
    have hb' : (z :: t).getLast? = some b := by rw [List.getLast?_cons_cons] at hb; exact hb
    rw [dstates, List.mem_append]
    rcases hr with hr | hr
    · by_cases hy : y = x
      · left; rw [if_pos hr, hy]; exact List.mem_singleton_self _
      · right
        exact cross hv' (a := z) rfl hb' h1 (by rw [hr]; omega)
    · right
      exact cross hv' (a := z) rfl hb' h1 (by omega)

lemma down_last : ∀ {l : List ℤ}, l.IsChain vrel → upc l = 0 → ∀ {a b : ℤ}, l.head? = some a →
    l.getLast? = some b → b + ((l.length - 1 : ℕ) : ℤ) = a
  | [], _, _, a, b, ha, _ => by simp at ha
  | [x], _, _, a, b, ha, hb => by simp at ha hb; subst ha; subst hb; simp
  | x :: z :: t, hv, hu, a, b, ha, hb => by
    simp only [List.head?_cons, Option.some.injEq] at ha
    subst ha
    rw [List.isChain_cons_cons] at hv
    rw [upc] at hu
    have hb' : (z :: t).getLast? = some b := by rw [List.getLast?_cons_cons] at hb; exact hb
    have hz : z = x - 1 := by
      by_contra hne
      rw [if_neg hne] at hu
      omega
    rw [if_pos hz] at hu
    have := down_last hv.2 (by omega) (a := z) rfl hb'
    simp only [List.length_cons] at this ⊢
    omega

end Basic

section Cycle

lemma sum_Ioc_eq (μ M : ℤ) (hμ : μ ≤ M) :
    ∑ y ∈ Finset.Ioc μ M, F y = ∑ j ∈ Finset.range (M - μ).toNat, F (M - j) := by
  refine Finset.sum_nbij' (fun y => (M - y).toNat) (fun j => M - j) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    rw [Finset.mem_Ioc] at hy
    rw [Finset.mem_range]
    omega
  · intro j hj
    rw [Finset.mem_range] at hj
    rw [Finset.mem_Ioc]
    omega
  · intro y hy
    rw [Finset.mem_Ioc] at hy
    show M - (((M - y).toNat : ℕ) : ℤ) = y
    omega
  · intro j _
    show (M - (M - (j : ℤ))).toNat = j
    omega
  · intro y hy
    rw [Finset.mem_Ioc] at hy
    show F y = F (M - (((M - y).toNat : ℕ) : ℤ))
    congr 1
    omega

theorem cycle_bound (hF : ∀ x, 0 ≤ F x) (hk : 0 ≤ k) {C : ℝ}
    (hC : ∀ (m : ℕ) (s : ℤ), 0 < m → (m : ℝ) * C ≤ k + ∑ j ∈ Finset.range m, F (s - j))
    {V : List ℤ} {s : ℤ} (hV : V.head? = some s) (hnd : V.Nodup) (hv : (V ++ [s]).IsChain vrel) :
    C * (downCount (V ++ [s]) : ℝ) ≤ pcost F k (V ++ [s]) := by
  have hne : V ≠ [] := by rintro rfl; simp at hV
  have hsV : s ∈ V := by
    obtain ⟨x, t, rfl⟩ := List.exists_cons_of_ne_nil hne
    simp at hV; subst hV; exact List.mem_cons_self
  have hfne : V.toFinset.Nonempty := ⟨s, List.mem_toFinset.mpr hsV⟩
  set μ := V.toFinset.min' hfne with hμdef
  set M := V.toFinset.max' hfne with hMdef
  have hμ : ∀ x ∈ V, μ ≤ x := fun x hx => Finset.min'_le _ _ (List.mem_toFinset.mpr hx)
  have hM : ∀ x ∈ V, x ≤ M := fun x hx => Finset.le_max' _ _ (List.mem_toFinset.mpr hx)
  have hμV : μ ∈ V := List.mem_toFinset.mp (Finset.min'_mem _ _)
  have hMV : M ∈ V := List.mem_toFinset.mp (Finset.max'_mem _ _)
  have hW : ∀ x ∈ V ++ [s], x ∈ V := by
    intro x hx
    rw [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx
    · exact hx
    · rw [hx]; exact hsV

  have hnd2 : (dstates (V ++ [s])).Nodup := by
    have h := dstates_sub_dropLast (V ++ [s])
    rw [List.dropLast_concat] at h
    exact h.nodup hnd
  have hset : (dstates (V ++ [s])).toFinset = Finset.Ioc μ M := by
    ext y
    rw [List.mem_toFinset, Finset.mem_Ioc]
    constructor
    · intro hy
      obtain ⟨h1, h2⟩ := mem_dstates hy
      exact ⟨by have := hμ _ (hW _ h2); omega, hM _ (hW _ h1)⟩
    · rintro ⟨h1, h2⟩
      by_cases hys : y ≤ s
      · obtain ⟨P, Q, hPQ⟩ := List.mem_iff_append.mp hμV
        have hpre : (P ++ [μ]) <+: (V ++ [s]) := by
          rw [hPQ]
          exact ⟨Q ++ [s], by simp⟩
        have hhead : (P ++ [μ]).head? = some s := by
          cases P with
          | nil =>
            simp only [List.nil_append] at hPQ
            rw [hPQ] at hV
            simp at hV
            omega
          | cons x P' =>
            rw [hPQ] at hV
            simpa using hV
        exact (dstates_prefix hpre).subset
          (cross (hv.prefix hpre) hhead (b := μ) (by simp) h1 hys)
      · push Not at hys
        obtain ⟨P, Q, hPQ⟩ := List.mem_iff_append.mp hMV
        have hsuf : (M :: (Q ++ [s])) <:+ (V ++ [s]) := by
          rw [hPQ]
          exact ⟨P, by simp⟩
        exact (dstates_suffix hsuf).subset
          (cross (hv.suffix hsuf) (a := M) (b := s) (by simp) (getLast?_cons_concat M Q s) hys h2)
  have hlen : downCount (V ++ [s]) = (M - μ).toNat := by
    rw [downCount_eq_length, ← List.toFinset_card_of_nodup hnd2, hset, Int.card_Ioc]
  have hsum : ((dstates (V ++ [s])).map F).sum = ∑ y ∈ Finset.Ioc μ M, F y := by
    rw [← hset, List.sum_toFinset _ hnd2]
  have hμM : μ ≤ M := hμ _ hMV
  rw [pcost_eq, hsum, hlen]
  rcases eq_or_lt_of_le hμM with heq | hlt
  · rw [heq, sub_self]
    have : (0 : ℝ) ≤ ∑ y ∈ Finset.Ioc M M, F y + k * (upc (V ++ [s]) : ℝ) := by
      have := Finset.sum_nonneg (fun y (_ : y ∈ Finset.Ioc M M) => hF y)
      positivity
    simpa using this
  ·
    have hup : 1 ≤ upc (V ++ [s]) := by
      by_contra h0
      push Not at h0
      have h00 : upc (V ++ [s]) = 0 := by omega
      have h := down_last hv h00 (a := s) (b := s) (by
        obtain ⟨x, t, rfl⟩ := List.exists_cons_of_ne_nil hne
        simp at hV ⊢; exact hV) (by simp)
      have hl : 2 ≤ (V ++ [s]).length := by
        rw [List.length_append]
        have := List.length_pos_of_ne_nil hne
        simp; omega
      omega
    have hd : 0 < (M - μ).toNat := by omega
    have h1 := hC _ M hd
    rw [sum_Ioc_eq F μ M hμM]
    have h2 : k ≤ k * (upc (V ++ [s]) : ℝ) := by
      have : (1 : ℝ) ≤ (upc (V ++ [s]) : ℝ) := by exact_mod_cast hup
      nlinarith
    rw [mul_comm C]
    linarith

end Cycle

section Erase

lemma loopErase_snoc (p : List ℤ) (s : ℤ) :
    loopErase (p ++ [s]) = loopEraseStep (loopErase p) s := by
  unfold loopErase
  rw [List.foldl_append]
  rfl

lemma takeWhile_split : ∀ {R : List ℤ} {s : ℤ}, s ∈ R →
    ∃ B, R = R.takeWhile (· ≠ s) ++ s :: B ∧ s ∉ R.takeWhile (· ≠ s)
  | [], s, h => by simp at h
  | x :: R, s, h => by
    by_cases hx : x = s
    · subst hx
      refine ⟨R, ?_, ?_⟩ <;> simp
    · have hR : s ∈ R := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hx
        · exact h
      obtain ⟨B, hB, hn⟩ := takeWhile_split hR
      have ht : (x :: R).takeWhile (· ≠ s) = x :: R.takeWhile (· ≠ s) := by
        simp [hx]
      refine ⟨B, ?_, ?_⟩
      · rw [ht, List.cons_append, ← hB]
      · rw [ht, List.mem_cons]
        push Not
        exact ⟨fun h => hx h.symm, hn⟩

theorem erase_bound (hF : ∀ x, 0 ≤ F x) (hk : 0 ≤ k) {C : ℝ}
    (hC : ∀ (m : ℕ) (s : ℤ), 0 < m → (m : ℝ) * C ≤ k + ∑ j ∈ Finset.range m, F (s - j)) :
    ∀ p : List ℤ, p.IsChain vrel →
      (loopErase p).Nodup ∧ (loopErase p).getLast? = p.getLast? ∧ (loopErase p).IsChain vrel ∧
      pcost F k (loopErase p) + C * ((downCount p : ℝ) - downCount (loopErase p))
        ≤ pcost F k p := by
  intro p
  induction p using List.reverseRecOn with
  | nil => intro _; simp [loopErase, pcost, downCount]
  | append_singleton p s ih =>
    intro hv
    have hvp : p.IsChain vrel := hv.left_of_append
    obtain ⟨hnd, hlast, hch, hineq⟩ := ih hvp
    rw [loopErase_snoc]
    rcases List.eq_nil_or_concat p with hp | ⟨p', a, hp'⟩
    · subst hp
      simp [loopErase, loopEraseStep, pcost, downCount]
    · have hpa : p.getLast? = some a := by rw [hp']; simp
      have hrel : vrel a s := by
        have h := hv.rel_getLast_head_of_append (l₁ := p) (l₂ := [s]) (by rw [hp']; simp) (by simp)
        have e : p.getLast (by rw [hp']; simp) = a := by
          rw [List.getLast_eq_iff_getLast?_eq_some]; exact hpa
        rw [e] at h; simpa using h
      have hRa : (loopErase p).getLast? = some a := by rw [hlast, hpa]
      obtain ⟨ep1, ep2, -⟩ := snoc F k p a s hpa
      unfold loopEraseStep
      split_ifs with hs
      ·
        obtain ⟨B, hB, hnot⟩ := takeWhile_split hs
        set A := (loopErase p).takeWhile (· ≠ s) with hA
        have hBne : B ≠ [] := by
          rintro rfl
          rw [hB] at hRa
          simp at hRa
          rcases hrel with h | h <;> omega
        have hlastB : (s :: B).getLast? = some a := by
          rw [hB] at hRa
          rw [List.getLast?_append] at hRa
          simpa using hRa
        have hsplit := split F k A s B
        rw [← hB] at hsplit
        obtain ⟨es1, es2⟩ := hsplit
        have hpre : (A ++ [s]) <+: loopErase p := by
          rw [hB]; exact ⟨B, by simp⟩
        have hsuf : (s :: B) <:+ loopErase p := by
          rw [hB]; exact ⟨A, rfl⟩
        have hVnd : (s :: B).Nodup := hnd.sublist hsuf.sublist
        have hWv : ((s :: B) ++ [s]).IsChain vrel := by
          refine (hch.suffix hsuf).append (List.isChain_singleton s) ?_
          intro x hx y hy
          simp at hy
          subst hy
          rw [hlastB, Option.mem_some_iff] at hx
          subst hx
          exact hrel
        have hcyc := cycle_bound F k hF hk hC (V := s :: B) (s := s) (by simp) hVnd hWv
        obtain ⟨ec1, ec2, -⟩ := snoc F k (s :: B) a s hlastB
        refine ⟨hnd.sublist hpre.sublist, by simp, hch.prefix hpre, ?_⟩
        rw [ep1, ep2]
        rw [ec1, ec2] at hcyc
        rw [es1, es2] at hineq
        push_cast at hineq hcyc ⊢
        nlinarith
      ·
        obtain ⟨er1, er2, -⟩ := snoc F k (loopErase p) a s hRa
        refine ⟨List.nodup_append.mpr ⟨hnd, List.nodup_singleton s, by
            intro x hx y hy; simp at hy; rw [hy]; rintro rfl; exact hs hx⟩, by simp, ?_, ?_⟩
        · refine hch.append (List.isChain_singleton s) ?_
          intro x hx y hy
          simp at hy
          subst hy
          rw [hRa, Option.mem_some_iff] at hx
          subst hx
          exact hrel
        · rw [er1, er2, ep1, ep2]
          push_cast
          linarith

end Erase

end LB

end TwoStageRnQ

open Finset

namespace TwoStageRnQ

namespace LB

def RCont (f : ℝ → ℤ) : Prop := ∀ t, ∃ δ > 0, ∀ s, t ≤ s → s < t + δ → f s = f t

def IsJump (f : ℝ → ℤ) (t : ℝ) : Prop := leftVal f t < f t

section LeftVal

variable {f : ℝ → ℤ}

lemma lv_bdd (hf : Monotone f) (t : ℝ) : BddAbove (f '' Set.Iio t) :=
  ⟨f t, by rintro _ ⟨s, hs, rfl⟩; exact hf hs.le⟩

lemma lv_ne (t : ℝ) : (f '' Set.Iio t).Nonempty := ⟨f (t - 1), t - 1, by simp, rfl⟩

lemma lv_le (hf : Monotone f) (t : ℝ) : leftVal f t ≤ f t :=
  csSup_le (lv_ne t) (by rintro _ ⟨s, hs, rfl⟩; exact hf hs.le)

lemma le_lv (hf : Monotone f) {s t : ℝ} (h : s < t) : f s ≤ leftVal f t :=
  le_csSup (lv_bdd hf t) ⟨s, h, rfl⟩

lemma lv_mem (hf : Monotone f) (t : ℝ) : ∃ s < t, f s = leftVal f t := by
  obtain ⟨s, hs, e⟩ := Int.csSup_mem (lv_ne (f := f) t) (lv_bdd hf t)
  exact ⟨s, hs, e⟩

lemma jump_iff (hf : Monotone f) (t : ℝ) : (∀ s < t, f s < f t) ↔ IsJump f t := by
  constructor
  · intro h
    obtain ⟨s, hs, e⟩ := lv_mem hf t
    unfold IsJump
    rw [← e]
    exact h s hs
  · intro h s hs
    exact lt_of_le_of_lt (le_lv hf hs) h

lemma const_noJump (hf : Monotone f) (hr : RCont f) {a b : ℝ}
    (hno : ∀ t, a < t → t < b → ¬ IsJump f t) : ∀ c, a ≤ c → c < b → f c = f a := by
  intro c hac hcb
  by_contra hne
  have hlt : f a < f c := lt_of_le_of_ne (hf hac) (Ne.symm hne)
  have hac' : a < c := lt_of_le_of_ne hac (by rintro rfl; exact hne rfl)
  let A : Set ℝ := {s | a < s ∧ s ≤ c ∧ f a < f s}
  have hcA : c ∈ A := ⟨hac', le_rfl, hlt⟩
  have hAne : A.Nonempty := ⟨c, hcA⟩
  have hAb : BddBelow A := ⟨a, fun s hs => hs.1.le⟩
  have haτ : a ≤ sInf A := le_csInf hAne (fun s hs => hs.1.le)
  have hτc : sInf A ≤ c := csInf_le hAb hcA
  have hbelow : ∀ s, a ≤ s → s < sInf A → f s = f a := by
    intro s h1 h2
    by_contra h3
    have h4 : f a < f s := lt_of_le_of_ne (hf h1) (Ne.symm h3)
    have h5 : a < s := lt_of_le_of_ne h1 (by rintro rfl; exact h3 rfl)
    have hsA : s ∈ A := ⟨h5, le_trans h2.le hτc, h4⟩
    exact absurd (csInf_le hAb hsA) (not_le.mpr h2)
  obtain ⟨δ, hδ, hδc⟩ := hr (sInf A)
  have hfτ : f a < f (sInf A) := by
    by_contra h4
    have h5 : f (sInf A) = f a := le_antisymm (not_lt.mp h4) (hf haτ)
    have h6 : sInf A + δ ≤ sInf A := le_csInf hAne (fun s hs => by
      by_contra h7
      have h8 : sInf A ≤ s := csInf_le hAb hs
      have h9 := hδc s h8 (lt_of_not_ge h7)
      have h10 := hs.2.2
      rw [h9, h5] at h10
      exact lt_irrefl _ h10)
    linarith
  have haτ' : a < sInf A := lt_of_le_of_ne haτ (by
    intro h
    rw [← h] at hfτ
    exact lt_irrefl _ hfτ)
  have hlv : leftVal f (sInf A) = f a := by
    apply le_antisymm
    · apply csSup_le (lv_ne _)
      rintro _ ⟨s, hs, rfl⟩
      rcases lt_or_ge s a with h | h
      · exact hf h.le
      · exact (hbelow s h hs).le
    · exact le_lv hf haτ'
  exact hno (sInf A) haτ' (lt_of_le_of_lt hτc hcb) (by unfold IsJump; rw [hlv]; exact hfτ)

lemma lv_noJump (hf : Monotone f) (hr : RCont f) {a b : ℝ} (hab : a < b)
    (hno : ∀ t, a < t → t < b → ¬ IsJump f t) : leftVal f b = f a := by
  have hc := const_noJump hf hr hno
  apply le_antisymm
  · apply csSup_le (lv_ne _)
    rintro _ ⟨s, hs, rfl⟩
    rcases lt_or_ge s a with h | h
    · exact hf h.le
    · exact (hc s h hs).le
  · exact le_lv hf hab

lemma val_noJump (hf : Monotone f) (hr : RCont f) {a b : ℝ} (hab : a ≤ b)
    (hno : ∀ t, a < t → t ≤ b → ¬ IsJump f t) : f b = f a := by
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  · have h1 := lv_noJump hf hr h (fun t h1 h2 => hno t h1 h2.le)
    have h2 := hno b h le_rfl
    unfold IsJump at h2
    have h3 := lv_le hf b
    omega

lemma jumps_card (hf : Monotone f) (S : Finset ℝ) :
    ∀ b, 0 ≤ b → (∀ t ∈ S, 0 < t ∧ t ≤ b ∧ IsJump f t) → (S.card : ℤ) ≤ f b - f 0 := by
  induction S using Finset.induction_on_max with
  | empty =>
    intro b hb _
    have := hf hb
    simp only [Finset.card_empty, Nat.cast_zero]
    omega
  | insert a s hlt ih =>
    intro b hb hS
    have ha := hS a (Finset.mem_insert_self a s)
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [Finset.card_insert_of_notMem has]
    have h1 : (s.card : ℤ) ≤ leftVal f a - f 0 := by
      rcases s.eq_empty_or_nonempty with hs | hs
      · rw [hs]
        have := le_lv hf ha.1
        simp only [Finset.card_empty, Nat.cast_zero]
        omega
      · have hm := hlt _ (s.max'_mem hs)
        have h2 := ih (s.max' hs) (le_of_lt (hS _ (Finset.mem_insert_of_mem (s.max'_mem hs))).1)
          (fun t ht => ⟨(hS t (Finset.mem_insert_of_mem ht)).1, s.le_max' t ht,
            (hS t (Finset.mem_insert_of_mem ht)).2.2⟩)
        have h3 := le_lv hf hm
        omega
    have h4 : leftVal f a < f a := ha.2.2
    have h5 := hf ha.2.1
    push_cast
    omega

lemma jumps_finite (hf : Monotone f) (T : ℝ) : {t | t ∈ Set.Ioc 0 T ∧ IsJump f t}.Finite := by
  by_contra h
  obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq h ((f T - f 0).toNat + 1)
  have hT : 0 ≤ T := by
    obtain ⟨t, ht⟩ := Set.Infinite.nonempty h
    exact le_of_lt (lt_of_lt_of_le ht.1.1 ht.1.2)
  have := jumps_card hf S T hT (fun t ht => by
    have h' := hS ht
    exact ⟨h'.1.1, h'.1.2, h'.2⟩)
  rw [hcard] at this
  push_cast at this
  omega

end LeftVal

def evSet (U N : ℝ → ℤ) (T : ℝ) : Set ℝ :=
  {t | t ∈ Set.Ioc 0 T ∧ (leftVal N t < N t ∨ leftVal U t < U t)}

lemma evSet_finite {U N : ℝ → ℤ} (hU : Monotone U) (hN : Monotone N) (T : ℝ) :
    (evSet U N T).Finite := by
  refine ((jumps_finite hN T).union (jumps_finite hU T)).subset ?_
  rintro t ⟨h1, h2 | h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩

noncomputable def cstep (U N : ℝ → ℤ) (acc : List ℤ × ℤ) (t : ℝ) : List ℤ × ℤ :=
  let dn : ℕ := (N t - leftVal N t).toNat
  let du : ℤ := U t - leftVal U t
  let downs : List ℤ := (List.range dn).map (fun k => acc.2 - ((k : ℤ) + 1))
  let s1 : ℤ := acc.2 - (dn : ℤ)
  if 0 < du then (acc.1 ++ downs ++ [s1 + du], s1 + du) else (acc.1 ++ downs, s1)

lemma chronPath_eq (x : ℤ) (U N : ℝ → ℤ) (T : ℝ) (hE : (evSet U N T).Finite) :
    chronPath x U N T = ((hE.toFinset.sort (· ≤ ·)).foldl (cstep U N)
      ([x + U 0 - N 0], x + U 0 - N 0)).1 := by
  unfold chronPath
  simp only
  rw [dif_pos (show {t | t ∈ Set.Ioc 0 T ∧ (leftVal N t < N t ∨ leftVal U t < U t)}.Finite from hE)]
  rfl

lemma fm_aux (a : ℤ) : ∀ l : List ℕ, List.map (fun k : ℤ => a - (k + 1))
    (List.flatMap (fun n : ℕ => [((n : ℕ) : ℤ)]) l) = List.map (fun j : ℕ => a - ((j : ℤ) + 1)) l
  | [] => rfl
  | x :: l => by
    simp only [List.flatMap_cons, List.map_append, List.map_cons, List.map_nil, fm_aux a l]
    rfl

lemma coe_range_map (a : ℤ) (d : ℕ) : (List.range d).map (fun k => a - ((k : ℤ) + 1))
    = (List.range d).map (fun j : ℕ => a - ((j : ℤ) + 1)) := by
  simp only [bind_pure_comp]
  have := fm_aux a (List.range d)
  simp at this ⊢

variable (F : ℤ → ℝ) (k : ℝ)

lemma run_spec (l : List ℤ) (a : ℤ) (hl : l.getLast? = some a) (hc : l.IsChain vrel) :
    ∀ d : ℕ,
    (l ++ (List.range d).map (fun j : ℕ => a - ((j : ℤ) + 1))).getLast? = some (a - d) ∧
    (l ++ (List.range d).map (fun j : ℕ => a - ((j : ℤ) + 1))).IsChain vrel ∧
    pcost F k (l ++ (List.range d).map (fun j : ℕ => a - ((j : ℤ) + 1)))
      = pcost F k l + ∑ j ∈ Finset.range d, F (a - j) ∧
    downCount (l ++ (List.range d).map (fun j : ℕ => a - ((j : ℤ) + 1))) = downCount l + d
  | 0 => by simp [hl, hc]
  | d + 1 => by
    obtain ⟨h1, h2, h3, h4⟩ := run_spec l a hl hc d
    rw [List.range_succ, List.map_append, ← List.append_assoc]
    simp only [List.map_cons, List.map_nil]
    obtain ⟨e1, e2, -⟩ := snoc F k _ (a - d) (a - ((d : ℤ) + 1)) h1
    have hdown : a - ((d : ℤ) + 1) = a - d - 1 := by ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [List.getLast?_concat]
      push_cast
      ring_nf
    · refine h2.append (List.isChain_singleton _) ?_
      intro x hx y hy
      rw [h1, Option.mem_some_iff] at hx
      simp only [List.head?_cons, Option.mem_some_iff] at hy
      subst hx
      subst hy
      left
      ring
    · rw [e1, h3, Finset.sum_range_succ]
      unfold tcost
      rw [if_pos hdown]
      ring
    · rw [e2, h4]
      unfold tdown
      rw [if_pos hdown]
      ring

lemma cstep_spec (U N : ℝ → ℤ) (acc : List ℤ × ℤ) (t : ℝ)
    (hl : acc.1.getLast? = some acc.2) (hc : acc.1.IsChain vrel) (hdu : 0 ≤ U t - leftVal U t) :
    (cstep U N acc t).1.getLast? = some (cstep U N acc t).2 ∧
    (cstep U N acc t).1.IsChain vrel ∧
    (cstep U N acc t).2 = acc.2 - ((N t - leftVal N t).toNat : ℤ) + (U t - leftVal U t) ∧
    pcost F k (cstep U N acc t).1 = pcost F k acc.1
      + ∑ j ∈ Finset.range (N t - leftVal N t).toNat, F (acc.2 - j)
      + (if 0 < U t - leftVal U t then k else 0) ∧
    downCount (cstep U N acc t).1 = downCount acc.1 + (N t - leftVal N t).toNat := by
  obtain ⟨h1, h2, h3, h4⟩ := run_spec F k acc.1 acc.2 hl hc (N t - leftVal N t).toNat
  unfold cstep
  simp only
  rw [coe_range_map]
  split_ifs with hu
  · obtain ⟨e1, e2, -⟩ := snoc F k _ _
      (acc.2 - ((N t - leftVal N t).toNat : ℤ) + (U t - leftVal U t)) h1
    have hnd : ¬ (acc.2 - ((N t - leftVal N t).toNat : ℤ) + (U t - leftVal U t)
        = acc.2 - ((N t - leftVal N t).toNat : ℤ) - 1) := by omega
    refine ⟨List.getLast?_concat, ?_, rfl, ?_, ?_⟩
    · refine h2.append (List.isChain_singleton _) ?_
      intro x hx y hy
      rw [h1, Option.mem_some_iff] at hx
      simp only [List.head?_cons, Option.mem_some_iff] at hy
      subst hx
      subst hy
      right
      omega
    · rw [e1, h3]
      unfold tcost
      rw [if_neg hnd]
    · rw [e2, h4]
      unfold tdown
      rw [if_neg hnd]
      ring
  · have hdu0 : U t - leftVal U t = 0 := by omega
    refine ⟨h1, h2, by rw [hdu0]; ring, by rw [h3]; ring, h4⟩

theorem fold_spec (x : ℤ) (U N : ℝ → ℤ) (hU : Monotone U) (hUr : RCont U)
    (hN : Monotone N) (hNr : RCont N) (T : ℝ) :
    ∀ (L : List ℝ) (p : ℝ) (acc : List ℤ × ℤ),
      p ≤ T → L.Pairwise (· < ·) → (∀ t ∈ L, p < t ∧ t ≤ T) →
      (∀ t, p < t → t ≤ T → ((IsJump N t ∨ IsJump U t) ↔ t ∈ L)) →
      acc.1.getLast? = some acc.2 → acc.1.IsChain vrel → acc.2 = x + U p - N p →
      (L.foldl (cstep U N) acc).1.getLast? = some (L.foldl (cstep U N) acc).2 ∧
      (L.foldl (cstep U N) acc).1.IsChain vrel ∧
      (L.foldl (cstep U N) acc).2 = x + U T - N T ∧
      pcost F k (L.foldl (cstep U N) acc).1 = pcost F k acc.1
        + (L.map (fun τ => ∑ j ∈ Finset.range (N τ - leftVal N τ).toNat,
            F (x + leftVal U τ - leftVal N τ - j))).sum
        + k * ((L.filter (fun τ => decide (0 < U τ - leftVal U τ))).length : ℝ) ∧
      (downCount (L.foldl (cstep U N) acc).1 : ℤ) = downCount acc.1 + (N T - N p) := by
  intro L
  induction L with
  | nil =>
    intro p acc hpT _ _ hev hl hc hx
    have hnoU : ∀ t, p < t → t ≤ T → ¬ IsJump U t := fun t h1 h2 h3 =>
      by simpa using (hev t h1 h2).mp (Or.inr h3)
    have hnoN : ∀ t, p < t → t ≤ T → ¬ IsJump N t := fun t h1 h2 h3 =>
      by simpa using (hev t h1 h2).mp (Or.inl h3)
    have e1 := val_noJump hU hUr hpT hnoU
    have e2 := val_noJump hN hNr hpT hnoN
    simp only [List.foldl_nil]
    refine ⟨hl, hc, by rw [hx, e1, e2], by simp, by rw [e2]; simp⟩
  | cons τ L ih =>
    intro p acc hpT hpw hmem hev hl hc hx
    rw [List.pairwise_cons] at hpw
    have hτ := hmem τ List.mem_cons_self

    have hno : ∀ t, p < t → t < τ → ¬ (IsJump N t ∨ IsJump U t) := by
      intro t h1 h2 h3
      have h4 := (hev t h1 (by linarith [hτ.2])).mp h3
      rcases List.mem_cons.mp h4 with h5 | h5
      · linarith
      · have := hpw.1 t h5; linarith
    have hlU : leftVal U τ = U p := lv_noJump hU hUr hτ.1 (fun t h1 h2 h3 => hno t h1 h2 (Or.inr h3))
    have hlN : leftVal N τ = N p := lv_noJump hN hNr hτ.1 (fun t h1 h2 h3 => hno t h1 h2 (Or.inl h3))
    have hdu : 0 ≤ U τ - leftVal U τ := by have := lv_le hU τ; omega
    have hdn : 0 ≤ N τ - leftVal N τ := by have := lv_le hN τ; omega
    obtain ⟨c1, c2, c3, c4, c5⟩ := cstep_spec F k U N acc τ hl hc hdu
    have hx' : (cstep U N acc τ).2 = x + U τ - N τ := by
      rw [c3, Int.toNat_of_nonneg hdn, hx, hlU, hlN]
      ring
    obtain ⟨i1, i2, i3, i4, i5⟩ := ih τ (cstep U N acc τ) hτ.2 hpw.2
      (fun t ht => ⟨hpw.1 t ht, (hmem t (List.mem_cons_of_mem _ ht)).2⟩)
      (fun t h1 h2 => by
        rw [hev t (by linarith [hτ.1]) h2, List.mem_cons]
        constructor
        · rintro (h | h)
          · linarith
          · exact h
        · exact fun h => Or.inr h)
      c1 c2 hx'
    rw [List.foldl_cons]
    refine ⟨i1, i2, i3, ?_, ?_⟩
    · rw [i4, c4, List.map_cons, List.sum_cons, List.filter_cons]
      have e : acc.2 = x + leftVal U τ - leftVal N τ := by rw [hx, hlU, hlN]
      rw [e]
      split_ifs with h1 h2 h2
      · simp only [List.length_cons]
        push_cast
        ring
      · simp at h1 h2
        omega
      · simp at h1 h2
        omega
      · ring
    · rw [i5, c5]
      push_cast
      rw [Int.toNat_of_nonneg hdn, hlN]
      ring

theorem chron_spec (x : ℤ) (U N : ℝ → ℤ) (hU : Monotone U) (hUr : RCont U)
    (hN : Monotone N) (hNr : RCont N) {T : ℝ} (hT : 0 ≤ T) :
    (chronPath x U N T).IsChain vrel ∧
    pcost F k (chronPath x U N T)
      = ∑ τ ∈ (evSet_finite hU hN T).toFinset, ∑ j ∈ Finset.range (N τ - leftVal N τ).toNat,
          F (x + leftVal U τ - leftVal N τ - j)
        + k * (jumpCount U T : ℝ) ∧
    (downCount (chronPath x U N T) : ℤ) = N T - N 0 := by
  have hE := evSet_finite hU hN T
  have hpw : (hE.toFinset.sort (· ≤ ·)).Pairwise (· < ·) := by
    have h1 := Finset.pairwise_sort hE.toFinset (· ≤ ·)
    have h2 := Finset.sort_nodup hE.toFinset (· ≤ ·)
    exact (h1.and h2).imp (fun h => lt_of_le_of_ne h.1 h.2)
  have hmemL : ∀ t, t ∈ hE.toFinset.sort (· ≤ ·) ↔ t ∈ evSet U N T := by
    intro t
    rw [Finset.mem_sort, Set.Finite.mem_toFinset]
  obtain ⟨-, f2, -, f4, f5⟩ := fold_spec F k x U N hU hUr hN hNr T (hE.toFinset.sort (· ≤ ·)) 0
    ([x + U 0 - N 0], x + U 0 - N 0)
    hT hpw (fun t ht => by
      have := (hmemL t).mp ht
      exact ⟨this.1.1, this.1.2⟩)
    (fun t h1 h2 => by
      rw [hmemL t]
      exact ⟨fun h => ⟨⟨h1, h2⟩, h⟩, fun h => h.2⟩)
    rfl (List.isChain_singleton _) (by ring)
  rw [chronPath_eq x U N T hE]
  refine ⟨f2, ?_, ?_⟩
  · rw [f4]
    have hs : ((hE.toFinset.sort (· ≤ ·)).map (fun τ => ∑ j ∈ Finset.range (N τ - leftVal N τ).toNat,
        F (x + leftVal U τ - leftVal N τ - j))).sum
        = ∑ τ ∈ hE.toFinset, ∑ j ∈ Finset.range (N τ - leftVal N τ).toNat,
            F (x + leftVal U τ - leftVal N τ - j) := by
      rw [← List.sum_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
    have hj : (((hE.toFinset.sort (· ≤ ·)).filter (fun τ => decide (0 < U τ - leftVal U τ))).length : ℝ)
        = (jumpCount U T : ℝ) := by
      congr 1
      have hnd : ((hE.toFinset.sort (· ≤ ·)).filter (fun τ => decide (0 < U τ - leftVal U τ))).Nodup :=
        (Finset.sort_nodup _ _).filter _
      rw [← List.toFinset_card_of_nodup hnd, List.toFinset_filter, Finset.sort_toFinset]
      unfold jumpCount
      rw [← Set.ncard_coe_finset]
      congr 1
      ext t
      simp only [Finset.coe_filter, Set.Finite.mem_toFinset, decide_eq_true_eq, Set.mem_setOf_eq]
      rw [jump_iff hU t]
      unfold evSet IsJump
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩
        exact ⟨h1, by omega⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, Or.inr h2⟩, by omega⟩
    rw [hs, hj]
    simp [pcost]
  · rw [f5]
    simp [downCount]

end LB

end TwoStageRnQ

open MeasureTheory Filter Topology Finset
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace LB

def gp (T : ℝ) (n j : ℕ) : ℝ := (j : ℝ) * (T / 2 ^ n)

lemma gp_succ (T : ℝ) (n j : ℕ) : gp T n (j + 1) = gp T n j + T / 2 ^ n := by
  unfold gp; push_cast; ring

lemma cell_iff {T : ℝ} (hT : 0 < T) (n j : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    ⌈τ / (T / 2 ^ n)⌉₊ - 1 = j ↔ gp T n j < τ ∧ τ ≤ gp T n (j + 1) := by
  have hh : 0 < T / 2 ^ n := by positivity
  have hpos : 1 ≤ ⌈τ / (T / 2 ^ n)⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; positivity)
  have e1 : ⌈τ / (T / 2 ^ n)⌉₊ - 1 = j ↔ ⌈τ / (T / 2 ^ n)⌉₊ = j + 1 := by omega
  rw [e1, Nat.ceil_eq_iff (by omega), Nat.add_sub_cancel, gp, gp, lt_div_iff₀ hh, div_le_iff₀ hh]
  all_goals (push_cast; try rfl)

variable {x : ℤ} {U N : ℝ → ℤ}

end LB

end TwoStageRnQ

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace LBP

open TwoStageRnQ.LB

variable {P : Params} (S : DemandSpace P)

lemma pois_two {v w : ℝ} (hvw : v ≤ w) :
    S.ν {ω | 2 ≤ S.N w ω - S.N v ω} ≤ ENNReal.ofReal ((P.lam * (w - v)) ^ 2) := by
  set μ := P.lam * (w - v) with hμ
  have hμ0 : 0 ≤ μ := mul_nonneg P.lam_nonneg (by linarith)
  have hm : Measurable (fun ω => S.N w ω - S.N v ω) := (S.N_meas w).sub (S.N_meas v)
  have hA : MeasurableSet {ω | 2 ≤ S.N w ω - S.N v ω} := measurableSet_le measurable_const hm
  have hB : MeasurableSet ({ω | S.N w ω - S.N v ω = ((0 : ℕ) : ℤ)} ∪ {ω | S.N w ω - S.N v ω = ((1 : ℕ) : ℤ)}) :=
    (measurableSet_eq_fun hm measurable_const).union (measurableSet_eq_fun hm measurable_const)
  have hdisj : Disjoint {ω | 2 ≤ S.N w ω - S.N v ω}
      ({ω | S.N w ω - S.N v ω = ((0 : ℕ) : ℤ)} ∪ {ω | S.N w ω - S.N v ω = ((1 : ℕ) : ℤ)}) := by
    rw [Set.disjoint_left]
    rintro ω h1 (h2 | h2) <;> simp only [Set.mem_ofPred_eq] at h1 h2 <;> omega
  have hcov : {ω | 2 ≤ S.N w ω - S.N v ω}
      ∪ ({ω | S.N w ω - S.N v ω = ((0 : ℕ) : ℤ)} ∪ {ω | S.N w ω - S.N v ω = ((1 : ℕ) : ℤ)}) = Set.univ := by
    ext ω
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    have := S.incr_nonneg hvw ω
    push_cast
    omega
  have hdisj2 : Disjoint {ω | S.N w ω - S.N v ω = ((0 : ℕ) : ℤ)} {ω | S.N w ω - S.N v ω = ((1 : ℕ) : ℤ)} := by
    rw [Set.disjoint_left]
    intro ω h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2
    rw [h1] at h2
    norm_num at h2
  have htot := measure_union (μ := S.ν) hdisj hB
  rw [hcov, measure_univ, measure_union hdisj2 (measurableSet_eq_fun hm measurable_const),
    S.N_law v w hvw 0, S.N_law v w hvw 1] at htot
  have hp0 : poisW μ 0 = Real.exp (-μ) := by unfold poisW; simp
  have hp1 : poisW μ 1 = Real.exp (-μ) * μ := by unfold poisW; simp
  rw [← hμ, hp0, hp1] at htot
  have he := Real.add_one_le_exp (-μ)
  have hsum : 1 - μ ^ 2 ≤ Real.exp (-μ) + Real.exp (-μ) * μ := by nlinarith [Real.exp_pos (-μ)]
  have hle : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (μ ^ 2) + (ENNReal.ofReal (Real.exp (-μ))
      + ENNReal.ofReal (Real.exp (-μ) * μ)) := by
    rw [← ENNReal.ofReal_add (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le hμ0),
      ← ENNReal.ofReal_add (sq_nonneg _) (by positivity), ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hfin : ENNReal.ofReal (Real.exp (-μ)) + ENNReal.ofReal (Real.exp (-μ) * μ) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  rw [htot] at hle
  exact (ENNReal.add_le_add_iff_right hfin).mp hle

structure Proc (S : DemandSpace P) where
  x : S.Ω → ℤ
  U : ℝ → S.Ω → ℤ
  x_meas : Measurable[S.𝓕 0] x
  U_adapted : ∀ t, Measurable[S.𝓕 t] (U t)
  U_mono : ∀ ω, Monotone (fun t => U t ω)
  U_rcont : ∀ ω t, ∃ δ > 0, ∀ s, t ≤ s → s < t + δ → U s ω = U t ω

variable {S} (pr : Proc S)

lemma tsum_pois_mean {μ : ℝ} (hμ : 0 ≤ μ) :
    ∑' d : ℕ, ENNReal.ofReal (poisW μ d) * ENNReal.ofReal (d : ℝ) = ENNReal.ofReal μ := by
  conv_rhs => rw [← tsum_poisW_mul_nat μ]
  rw [ENNReal.ofReal_tsum_of_nonneg (fun d => mul_nonneg (poisW_nonneg hμ d) (Nat.cast_nonneg d))
    (summable_poisW_mul_nat μ)]
  refine tsum_congr (fun d => ?_)
  rw [ENNReal.ofReal_mul (poisW_nonneg hμ d)]

lemma lintegral_mul_incr {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) {Y : S.Ω → ℤ}
    (hY : Measurable[S.𝓕 v] Y) (g : ℤ → ℝ≥0∞) :
    ∫⁻ ω, g (Y ω) * ENNReal.ofReal ((S.N w ω - S.N v ω : ℤ) : ℝ) ∂S.ν
      = (∫⁻ ω, g (Y ω) ∂S.ν) * ENNReal.ofReal (P.lam * (w - v)) := by
  have hμ : 0 ≤ P.lam * (w - v) := mul_nonneg P.lam_nonneg (by linarith)
  have hYm : Measurable Y := hY.mono (S.𝓕.le v) le_rfl
  have e1 : ∀ ω, g (Y ω) * ENNReal.ofReal ((S.N w ω - S.N v ω : ℤ) : ℝ)
      = g (Y ω) * ENNReal.ofReal (((S.N w ω - S.N v ω).toNat : ℕ) : ℝ) := by
    intro ω
    congr 2
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (S.incr_nonneg hvw ω)]
  have key := S.lintegral_incr hv hvw hY (fun a (d : ℕ) => g a * ENNReal.ofReal (d : ℝ))
  rw [lintegral_congr e1, key, S.lintegral_comp hYm g, ← ENNReal.tsum_mul_right]
  refine tsum_congr (fun a => ?_)
  have e : ∑' d : ℕ, ENNReal.ofReal (poisW (P.lam * (w - v)) d) * (g a * ENNReal.ofReal (d : ℝ))
      = g a * ENNReal.ofReal (P.lam * (w - v)) := by
    rw [← tsum_pois_mean hμ, ← ENNReal.tsum_mul_left]
    congr 1
    funext d
    ring
  rw [e]
  ring

end LBP

end TwoStageRnQ

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace Imp

open TwoStageRnQ.LB TwoStageRnQ.Prop1 TwoStageRnQ.Prop1

section Jumps

variable {f : ℝ → ℤ}

lemma diff_le_jumps_aux (hf : Monotone f) (hr : RCont f) {B : ℤ} :
    ∀ E : Finset ℝ, ∀ b : ℝ, 0 ≤ b → (∀ t, (t ∈ Set.Ioc 0 b ∧ IsJump f t) ↔ t ∈ E) →
      (∀ t ∈ E, f t - leftVal f t ≤ B) → f b - f 0 ≤ B * (E.card : ℤ) := by
  intro E
  induction E using Finset.induction_on_max with
  | empty =>
    intro b hb hE _
    have := val_noJump hf hr hb (fun t h1 h2 hj => by
      have := (hE t).mp ⟨⟨h1, h2⟩, hj⟩; simp at this)
    simp [this]
  | insert a s hlt ih =>
    intro b hb hE hB
    have haE : a ∈ insert a s := mem_insert_self a s
    obtain ⟨⟨ha0, hab⟩, _⟩ := (hE a).mpr haE
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [card_insert_of_notMem has]
    have hfb : f b = f a := val_noJump hf hr hab (fun t h1 h2 hj => by
      have ht := (hE t).mp ⟨⟨by linarith, h2⟩, hj⟩
      rcases mem_insert.mp ht with h | h
      · linarith
      · linarith [hlt t h])
    have hlv : leftVal f a - f 0 ≤ B * (s.card : ℤ) := by
      rcases s.eq_empty_or_nonempty with hs | hs
      · subst hs
        have := lv_noJump hf hr ha0 (fun t h1 h2 hj => by
          have ht := (hE t).mp ⟨⟨h1, by linarith⟩, hj⟩
          rcases mem_insert.mp ht with h | h
          · linarith
          · simp at h)
        simp [this]
      · have ha's : s.max' hs ∈ s := s.max'_mem hs
        have ha'a : s.max' hs < a := hlt _ ha's
        have ha'0 : 0 < s.max' hs := ((hE _).mpr (mem_insert_of_mem ha's)).1.1
        have hlv' : leftVal f a = f (s.max' hs) := lv_noJump hf hr ha'a (fun t h1 h2 hj => by
          have ht := (hE t).mp ⟨⟨by linarith, by linarith⟩, hj⟩
          rcases mem_insert.mp ht with h | h
          · linarith
          · linarith [s.le_max' t h])
        have := ih (s.max' hs) ha'0.le (fun t => ⟨fun ⟨⟨h1, h2⟩, hj⟩ => by
            have ht := (hE t).mp ⟨⟨h1, by linarith⟩, hj⟩
            rcases mem_insert.mp ht with h | h
            · linarith
            · exact h,
          fun ht => ⟨⟨((hE t).mpr (mem_insert_of_mem ht)).1.1, s.le_max' t ht⟩,
            ((hE t).mpr (mem_insert_of_mem ht)).2⟩⟩)
          (fun t ht => hB t (mem_insert_of_mem ht))
        rw [hlv']; exact this
    have hBa := hB a haE
    rw [hfb]
    push_cast
    linarith

lemma diff_le_jumps (hf : Monotone f) (hr : RCont f) {B : ℤ} {T : ℝ} (hT : 0 ≤ T)
    (hB : ∀ t ∈ Set.Ioc 0 T, f t - leftVal f t ≤ B) :
    f T - f 0 ≤ B * (jumpCount f T : ℤ) := by
  have hfin := jumps_finite hf T
  have hJ : jumpCount f T = hfin.toFinset.card := by
    unfold jumpCount
    rw [← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
    congr 1
    ext t
    simp only [Set.mem_setOf_eq]
    rw [jump_iff hf]
  rw [hJ]
  refine diff_le_jumps_aux hf hr hfin.toFinset T hT (fun t => by simp) (fun t ht => ?_)
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at ht
  exact hB t ht.1

lemma rcont_shift (hr : RCont f) (c : ℝ) : RCont (fun t => f (t - c)) := by
  intro t
  obtain ⟨δ, hδ, h⟩ := hr (t - c)
  exact ⟨δ, hδ, fun s h1 h2 => h (s - c) (by linarith) (by linarith)⟩

lemma rcont_comp2 {g : ℝ → ℤ} (hf : RCont f) (hg : RCont g) (G : ℤ → ℤ → ℤ) :
    RCont (fun t => G (f t) (g t)) := by
  intro t
  obtain ⟨δ1, hδ1, h1⟩ := hf t
  obtain ⟨δ2, hδ2, h2⟩ := hg t
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun s hs1 hs2 => ?_⟩
  simp only
  rw [h1 s hs1 (by linarith [min_le_left δ1 δ2]), h2 s hs1 (by linarith [min_le_right δ1 δ2])]

lemma leftVal_shift (hf : Monotone f) (c t : ℝ) :
    leftVal (fun s => f (s - c)) t = leftVal f (t - c) := by
  unfold leftVal
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_Iio]
  constructor
  · rintro ⟨s, hs, rfl⟩; exact ⟨s - c, by linarith, rfl⟩
  · rintro ⟨s, hs, rfl⟩; exact ⟨s + c, by linarith, by simp⟩

lemma exists_left_common {g : ℝ → ℤ} (hf : Monotone f) (hg : Monotone g) (t : ℝ) :
    ∃ s < t, f s = leftVal f t ∧ g s = leftVal g t := by
  obtain ⟨s1, hs1, e1⟩ := lv_mem hf t
  obtain ⟨s2, hs2, e2⟩ := lv_mem hg t
  refine ⟨max s1 s2, max_lt hs1 hs2, ?_, ?_⟩
  · exact le_antisymm (le_lv hf (max_lt hs1 hs2)) (e1 ▸ hf (le_max_left _ _))
  · exact le_antisymm (le_lv hg (max_lt hs1 hs2)) (e2 ▸ hg (le_max_right _ _))

end Jumps

section UnitJumps

variable {P : Params} (S : DemandSpace P)

theorem unit_jumps_from (a : ℝ) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂S.ν, ∀ t ∈ Set.Ioc a (a + T), S.N t ω - leftVal (fun s => S.N s ω) t ≤ 1 := by
  rw [ae_iff]
  have hn : ∀ n : ℕ, S.ν {ω | ¬∀ t ∈ Set.Ioc a (a + T), S.N t ω - leftVal (fun s => S.N s ω) t ≤ 1}
      ≤ ENNReal.ofReal ((P.lam * T) ^ 2 / 2 ^ n) := by
    intro n
    have hh : 0 < T / 2 ^ n := by positivity
    have hsub : {ω | ¬∀ t ∈ Set.Ioc a (a + T), S.N t ω - leftVal (fun s => S.N s ω) t ≤ 1}
        ⊆ ⋃ j ∈ Finset.range (2 ^ n),
          {ω | 2 ≤ S.N (a + gp T n (j + 1)) ω - S.N (a + gp T n j) ω} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq, not_forall, not_le] at hω
      obtain ⟨t, ht, h2⟩ := hω
      have ht0 : 0 < t - a := by linarith [ht.1]
      have hcell := (cell_iff hT n (⌈(t - a) / (T / 2 ^ n)⌉₊ - 1) ht0).mp rfl
      have hjlt : ⌈(t - a) / (T / 2 ^ n)⌉₊ - 1 < 2 ^ n := by
        have h1 : (t - a) / (T / 2 ^ n) ≤ (2 ^ n : ℕ) := by
          rw [div_le_iff₀ hh]
          push_cast
          have : (2 : ℝ) ^ n * (T / 2 ^ n) = T := by field_simp
          linarith [ht.2]
        have h3 := Nat.ceil_le.mpr h1
        have h4 : 1 ≤ ⌈(t - a) / (T / 2 ^ n)⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
          rw [Ne, Nat.ceil_eq_zero, not_le]; exact div_pos ht0 hh)
        have h5 : 0 < 2 ^ n := by positivity
        omega
      simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_ofPred_eq]
      refine ⟨⌈(t - a) / (T / 2 ^ n)⌉₊ - 1, hjlt, ?_⟩
      have e1 : S.N t ω ≤ S.N (a + gp T n (⌈(t - a) / (T / 2 ^ n)⌉₊ - 1 + 1)) ω :=
        S.N_mono ω (by linarith [hcell.2])
      have e2 : S.N (a + gp T n (⌈(t - a) / (T / 2 ^ n)⌉₊ - 1)) ω
          ≤ leftVal (fun s => S.N s ω) t :=
        le_lv (S.N_mono ω) (by linarith [hcell.1])
      omega
    calc _ ≤ S.ν (⋃ j ∈ Finset.range (2 ^ n),
          {ω | 2 ≤ S.N (a + gp T n (j + 1)) ω - S.N (a + gp T n j) ω}) := measure_mono hsub
      _ ≤ ∑ j ∈ Finset.range (2 ^ n),
            S.ν {ω | 2 ≤ S.N (a + gp T n (j + 1)) ω - S.N (a + gp T n j) ω} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ j ∈ Finset.range (2 ^ n), ENNReal.ofReal ((P.lam * (T / 2 ^ n)) ^ 2) := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          have hvw : a + gp T n j ≤ a + gp T n (j + 1) := by rw [gp_succ]; linarith
          have h := LBP.pois_two S hvw
          rwa [show a + gp T n (j + 1) - (a + gp T n j) = T / 2 ^ n by rw [gp_succ]; ring] at h
      _ = ENNReal.ofReal ((P.lam * T) ^ 2 / 2 ^ n) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          push_cast
          field_simp
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal ((P.lam * T) ^ 2 / 2 ^ n)) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal (tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two) :
        Tendsto (fun n : ℕ => (P.lam * T) ^ 2 / (2 : ℝ) ^ n) atTop (𝓝 0))
    rwa [ENNReal.ofReal_zero] at h
  exact le_antisymm (ge_of_tendsto' hlim hn) zero_le

end UnitJumps

section Classical

variable {P : Params} (S : DemandSpace P) (R1 R2 : ℤ) (Q n : ℕ+)

def Gc (a b : ℤ) : ℤ :=
  ((Q : ℕ) : ℤ) * min (a / ((Q : ℕ) : ℤ)) (((n : ℕ) : ℤ) * ((b + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)))

lemma U1_eq (t : ℝ) (ω : S.Ω) :
    Classical'.U1 S (ctrl R1 R2 Q n) t ω = Gc R1 R2 Q n (S.N t ω) (S.N (t - P.L2) ω) := by
  show ((Q : ℕ) : ℤ) * min (Classical'.reqCount S (ctrl R1 R2 Q n) t ω)
      (((n : ℕ) : ℤ) * Classical'.ordCount S (ctrl R1 R2 Q n) (t - P.L2) ω) = _
  rw [reqCount_eq, ordCount_eq]
  rfl

lemma ediv_succ_le {q a a' : ℤ} (hq : 0 < q) (h : a' ≤ a + 1) : a' / q ≤ a / q + 1 := by
  have h1 : a' ≤ a + 1 * q := by linarith
  calc a' / q ≤ (a + 1 * q) / q := Int.ediv_le_ediv hq h1
    _ = a / q + 1 := Int.add_mul_ediv_right a 1 hq.ne'

lemma Gc_jump {a a' b b' : ℤ} (ha : a ≤ a') (ha' : a' ≤ a + 1) (hb : b ≤ b') (hb' : b' ≤ b + 1) :
    Gc R1 R2 Q n a' b' - Gc R1 R2 Q n a b ≤ ((mN Q n : ℕ) : ℤ) := by
  have hq : (0 : ℤ) < ((Q : ℕ) : ℤ) := by exact_mod_cast Q.pos
  have hn : (1 : ℤ) ≤ ((n : ℕ) : ℤ) := by exact_mod_cast n.pos
  have hm : (0 : ℤ) < ((mN Q n : ℕ) : ℤ) := by exact_mod_cast mN_pos Q n
  have hx := ediv_succ_le hq ha'
  have hy := ediv_succ_le hm (by linarith : b' + cz Q n R1 R2 ≤ (b + cz Q n R1 R2) + 1)
  have key : min (a' / ((Q : ℕ) : ℤ)) (((n : ℕ) : ℤ) * ((b' + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)))
      ≤ min (a / ((Q : ℕ) : ℤ)) (((n : ℕ) : ℤ) * ((b + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)))
        + ((n : ℕ) : ℤ) := by
    rcases le_total (a / ((Q : ℕ) : ℤ)) (((n : ℕ) : ℤ) * ((b + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)))
      with h | h
    · rw [min_eq_left h]; exact (min_le_left _ _).trans (by linarith)
    · rw [min_eq_right h]; exact (min_le_right _ _).trans (by nlinarith)
  unfold Gc
  calc ((Q : ℕ) : ℤ) * min (a' / ((Q : ℕ) : ℤ))
          (((n : ℕ) : ℤ) * ((b' + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)))
        - ((Q : ℕ) : ℤ) * min (a / ((Q : ℕ) : ℤ))
          (((n : ℕ) : ℤ) * ((b + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)))
      = ((Q : ℕ) : ℤ) * (min (a' / ((Q : ℕ) : ℤ))
          (((n : ℕ) : ℤ) * ((b' + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)))
        - min (a / ((Q : ℕ) : ℤ))
          (((n : ℕ) : ℤ) * ((b + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)))) := by ring
    _ ≤ ((Q : ℕ) : ℤ) * ((n : ℕ) : ℤ) := mul_le_mul_of_nonneg_left (by linarith) hq.le
    _ = ((mN Q n : ℕ) : ℤ) := by rw [mN_cast]; ring

lemma U1_mono' (ω : S.Ω) : Monotone (fun t => Classical'.U1 S (ctrl R1 R2 Q n) t ω) := by
  intro s t hst
  unfold Classical'.U1
  have := Classical'.matchCount_mono S (ctrl R1 R2 Q n) ω hst
  have hq : (0 : ℤ) ≤ ((Q : ℕ) : ℤ) := by positivity
  exact mul_le_mul_of_nonneg_left this hq

lemma U1_rcont' (ω : S.Ω) : RCont (fun t => Classical'.U1 S (ctrl R1 R2 Q n) t ω) := by
  have e : (fun t => Classical'.U1 S (ctrl R1 R2 Q n) t ω)
      = fun t => Gc R1 R2 Q n (S.N t ω) (S.N (t - P.L2) ω) := funext (fun t => U1_eq S R1 R2 Q n t ω)
  rw [e]
  exact rcont_comp2 (S.N_rcont ω) (rcont_shift (S.N_rcont ω) P.L2) _

lemma U1_jump_le (ω : S.Ω) (t : ℝ)
    (h1 : S.N t ω - leftVal (fun s => S.N s ω) t ≤ 1)
    (h2 : S.N (t - P.L2) ω - leftVal (fun s => S.N s ω) (t - P.L2) ≤ 1) :
    Classical'.U1 S (ctrl R1 R2 Q n) t ω
      - leftVal (fun s => Classical'.U1 S (ctrl R1 R2 Q n) s ω) t ≤ ((mN Q n : ℕ) : ℤ) := by
  have hN := S.N_mono ω
  have hNs : Monotone (fun s => S.N (s - P.L2) ω) := fun a b hab => hN (by linarith)
  obtain ⟨s, hst, e1, e2⟩ := exists_left_common hN hNs t
  rw [leftVal_shift hN P.L2 t] at e2
  have hle := le_lv (U1_mono' S R1 R2 Q n ω) hst
  have e1' : S.N s ω = leftVal (fun s => S.N s ω) t := e1
  have e2' : S.N (s - P.L2) ω = leftVal (fun s => S.N s ω) (t - P.L2) := e2
  have hU1s : Classical'.U1 S (ctrl R1 R2 Q n) s ω
      = Gc R1 R2 Q n (leftVal (fun s => S.N s ω) t) (leftVal (fun s => S.N s ω) (t - P.L2)) := by
    rw [U1_eq, e1', e2']
  have hj := Gc_jump R1 R2 Q n (lv_le hN t) (by linarith) (lv_le hN (t - P.L2)) (by linarith)
  rw [U1_eq] at ⊢
  rw [U1_eq] at hle
  rw [← U1_eq S R1 R2 Q n s ω, hU1s] at hle
  linarith

lemma U1_diff_le_jumps {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂S.ν, Classical'.U1 S (ctrl R1 R2 Q n) T ω - Classical'.U1 S (ctrl R1 R2 Q n) 0 ω
      ≤ ((mN Q n : ℕ) : ℤ) * (jumpCount (fun t => Classical'.U1 S (ctrl R1 R2 Q n) t ω) T : ℤ) := by
  have hL2 := P.L2_nonneg
  filter_upwards [unit_jumps_from S (-P.L2 - 1) (by linarith : 0 < T + P.L2 + 1)] with ω hω
  refine diff_le_jumps (U1_mono' S R1 R2 Q n ω) (U1_rcont' S R1 R2 Q n ω) hT.le (fun t ht => ?_)
  refine U1_jump_le S R1 R2 Q n ω t (hω t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    (hω (t - P.L2) ⟨by linarith [ht.1], by linarith [ht.2]⟩)

lemma IL2_eq' (t : ℝ) (ω : S.Ω) :
    netInv P.L2 (Classical'.x2 S (ctrl R1 R2 Q n)) (Classical'.U2 S (ctrl R1 R2 Q n)) S.N t ω
      = sz Q R1 - (S.N t ω - ((mN Q n : ℕ) : ℤ)
          * ((S.N (t - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) := by
  show R1 + ((Q : ℕ) : ℤ) + ((0 : ℕ) : ℤ) + ((n : ℕ) : ℤ) * ((Q : ℕ) : ℤ)
      * Classical'.ordCount S (ctrl R1 R2 Q n) (t - P.L2) ω - S.N t ω = _
  rw [ordCount_eq]
  unfold sz
  rw [mN_cast]
  push_cast
  ring

lemma IL1_le_IL2 (t : ℝ) (ω : S.Ω) :
    netInv P.L1 (Classical'.x1 S (ctrl R1 R2 Q n)) (Classical'.U1 S (ctrl R1 R2 Q n)) S.N t ω
      ≤ netInv P.L2 (Classical'.x2 S (ctrl R1 R2 Q n)) (Classical'.U2 S (ctrl R1 R2 Q n)) S.N t ω := by
  rw [IL2_eq S R1 R2 Q n t ω]
  have hm' : (0 : ℤ) < ((mN Q n : ℕ) : ℤ) := by exact_mod_cast mN_pos Q n
  have hO : (S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)
      ≤ (S.N (t - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ) :=
    Int.ediv_le_ediv hm' (by linarith [S.N_mono ω (by linarith [P.L1_nonneg] : t - P.L1 - P.L2 ≤ t - P.L2)])
  have hW := Wf_nonneg Q (S.N (t - P.L1) ω - ((mN Q n : ℕ) : ℤ)
    * ((S.N (t - P.L1 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ)))
  nlinarith

lemma phi_le_cI (t : ℝ) (ω : S.Ω) :
    phi P.h2 P.p ((netInv P.L2 (Classical'.x2 S (ctrl R1 R2 Q n)) (Classical'.U2 S (ctrl R1 R2 Q n))
      S.N t ω : ℤ) : ℝ) ≤ Classical'.cI S (ctrl R1 R2 Q n) t ω := by
  have hab := IL1_le_IL2 S R1 R2 Q n t ω
  have hab' : ((netInv P.L1 (Classical'.x1 S (ctrl R1 R2 Q n)) (Classical'.U1 S (ctrl R1 R2 Q n))
      S.N t ω : ℤ) : ℝ) ≤ ((netInv P.L2 (Classical'.x2 S (ctrl R1 R2 Q n))
        (Classical'.U2 S (ctrl R1 R2 Q n)) S.N t ω : ℤ) : ℝ) := by exact_mod_cast hab
  unfold Classical'.cI costRate phi
  set a := ((netInv P.L1 (Classical'.x1 S (ctrl R1 R2 Q n)) (Classical'.U1 S (ctrl R1 R2 Q n))
      S.N t ω : ℤ) : ℝ)
  set b := ((netInv P.L2 (Classical'.x2 S (ctrl R1 R2 Q n)) (Classical'.U2 S (ctrl R1 R2 Q n))
      S.N t ω : ℤ) : ℝ)
  have h1 := P.h1_nonneg
  have h2 := P.h2_nonneg
  have hp := P.p_nonneg
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · rw [max_eq_left ha, max_eq_left hb, max_eq_right (by linarith : -a ≤ 0),
      max_eq_right (by linarith : -b ≤ 0)]; nlinarith
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    rw [ha0, hb0]; simp
  · rw [max_eq_right ha, max_eq_left hb, max_eq_left (by linarith : 0 ≤ -a),
      max_eq_right (by linarith : -b ≤ 0)]; nlinarith
  · rw [max_eq_right ha, max_eq_right hb, max_eq_left (by linarith : 0 ≤ -a),
      max_eq_left (by linarith : 0 ≤ -b)]; nlinarith

end Classical

def Fimp (P : Params) (z : ℝ) : ℝ := pexp P.mu2 (fun d : ℕ => phi P.h2 P.p (z - d))

lemma Fimp_nonneg (P : Params) (z : ℝ) : 0 ≤ Fimp P z :=
  pexp_nonneg P.mu2_nonneg (fun _ => phi_nonneg P.h2_nonneg P.p_nonneg _)

section Upstream

variable {P : Params} (S : DemandSpace P) (R1 R2 : ℤ) (Q n : ℕ+)

def IL2c (t : ℝ) (ω : S.Ω) : ℤ :=
  netInv P.L2 (Classical'.x2 S (ctrl R1 R2 Q n)) (Classical'.U2 S (ctrl R1 R2 Q n)) S.N t ω

theorem lintegral_phi_IL2 {t : ℝ} (ht : P.L2 ≤ t) :
    ∫⁻ ω, ENNReal.ofReal (phi P.h2 P.p ((IL2c S R1 R2 Q n t ω : ℤ) : ℝ)) ∂S.ν
      = ∑ ρ ∈ Finset.Ico (0 : ℤ) (mN Q n), S.shLaw (mN Q n) (t - P.L2) (cz Q n R1 R2) ρ
          * ENNReal.ofReal (Fimp P (((sz Q R1 + cz Q n R1 R2 - ρ : ℤ) : ℝ))) := by
  have hm := mN_pos Q n
  have e : ∀ ω, ENNReal.ofReal (phi P.h2 P.p ((IL2c S R1 R2 Q n t ω : ℤ) : ℝ))
      = (fun y : ℤ => ENNReal.ofReal (phi P.h2 P.p ((sz Q R1 - y : ℤ) : ℝ)))
          (S.N t ω - ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) := by
    intro ω; unfold IL2c; rw [IL2_eq']
  rw [lintegral_congr e]
  refine (S.lintegral_Y (mN Q n) hm P.L2_nonneg ht (cz Q n R1 R2)
    (fun y : ℤ => ENNReal.ofReal (phi P.h2 P.p ((sz Q R1 - y : ℤ) : ℝ)))).trans ?_
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  congr 1
  have e2 : ∀ d : ℕ, ENNReal.ofReal (phi P.h2 P.p ((sz Q R1 - (ρ - cz Q n R1 R2 + d) : ℤ) : ℝ))
      = ENNReal.ofReal (phi P.h2 P.p (((sz Q R1 + cz Q n R1 R2 - ρ : ℤ) : ℝ) - d)) := by
    intro d; congr 2; push_cast; ring
  simp_rw [e2]
  exact tsum_ofReal_pexp P.mu2_nonneg (fun d => phi_nonneg P.h2_nonneg P.p_nonneg _)
    ((phi_linGrowth P.h2_nonneg P.p_nonneg _).pint P.mu2_nonneg)

def Cphi : ℝ := (P.h2 + P.p) * (|((sz Q R1 : ℤ) : ℝ)| + |((cz Q n R1 R2 : ℤ) : ℝ)|
  + ((mN Q n : ℕ) : ℝ) + P.lam * P.L2)

lemma Cphi_nonneg : 0 ≤ Cphi (P := P) R1 R2 Q n := by
  unfold Cphi
  have := P.h2_nonneg; have := P.p_nonneg; have := P.lam_nonneg; have := P.L2_nonneg
  positivity

lemma lintegral_phi_IL2_le (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (phi P.h2 P.p ((IL2c S R1 R2 Q n t ω : ℤ) : ℝ)) ∂S.ν
      ≤ ENNReal.ofReal (Cphi (P := P) R1 R2 Q n) := by
  have hm' : (0 : ℤ) < ((mN Q n : ℕ) : ℤ) := by exact_mod_cast mN_pos Q n
  have hv : t - P.L2 ≤ t := by linarith [P.L2_nonneg]
  have hab := add_nonneg P.h2_nonneg P.p_nonneg
  have hc0 : (0 : ℝ) ≤ (P.h2 + P.p) * (|((sz Q R1 : ℤ) : ℝ)| + |((cz Q n R1 R2 : ℤ) : ℝ)|
      + ((mN Q n : ℕ) : ℝ)) := by positivity
  have hmeas : Measurable (fun ω => ENNReal.ofReal (((S.N t ω - S.N (t - P.L2) ω : ℤ) : ℝ))) := by
    have h := meas_N2 S (fun z : ℤ × ℤ => ENNReal.ofReal (((z.1 - z.2 : ℤ) : ℝ))) t (t - P.L2)
    exact h
  calc ∫⁻ ω, ENNReal.ofReal (phi P.h2 P.p ((IL2c S R1 R2 Q n t ω : ℤ) : ℝ)) ∂S.ν
      ≤ ∫⁻ ω, (ENNReal.ofReal ((P.h2 + P.p) * (|((sz Q R1 : ℤ) : ℝ)| + |((cz Q n R1 R2 : ℤ) : ℝ)|
          + ((mN Q n : ℕ) : ℝ))) + ENNReal.ofReal (P.h2 + P.p)
            * ENNReal.ofReal (((S.N t ω - S.N (t - P.L2) ω : ℤ) : ℝ))) ∂S.ν := by
        refine lintegral_mono (fun ω => ?_)
        have r0 := Int.emod_add_mul_ediv (S.N (t - P.L2) ω + cz Q n R1 R2) ((mN Q n : ℕ) : ℤ)
        have r0a := Int.emod_nonneg (S.N (t - P.L2) ω + cz Q n R1 R2) hm'.ne'
        have r0b := Int.emod_lt_of_pos (S.N (t - P.L2) ω + cz Q n R1 R2) hm'
        have hmo := S.N_mono ω hv
        have hc1 := le_abs_self (cz Q n R1 R2)
        have hc2 := neg_abs_le (cz Q n R1 R2)
        have hs1 := le_abs_self (sz Q R1)
        have hs2 := neg_abs_le (sz Q R1)
        have hIL : |IL2c S R1 R2 Q n t ω| ≤ |sz Q R1| + |cz Q n R1 R2| + ((mN Q n : ℕ) : ℤ)
            + (S.N t ω - S.N (t - P.L2) ω) := by
          unfold IL2c; rw [IL2_eq']
          rw [abs_le]; constructor <;> linarith
        have hILr : |((IL2c S R1 R2 Q n t ω : ℤ) : ℝ)| ≤ |((sz Q R1 : ℤ) : ℝ)|
            + |((cz Q n R1 R2 : ℤ) : ℝ)| + ((mN Q n : ℕ) : ℝ)
            + ((S.N t ω - S.N (t - P.L2) ω : ℤ) : ℝ) := by
          have h := (Int.cast_le (R := ℝ)).mpr hIL
          push_cast at h ⊢
          linarith
        have hph := (le_abs_self _).trans (phi_abs_le P.h2_nonneg P.p_nonneg
          ((IL2c S R1 R2 Q n t ω : ℤ) : ℝ))
        have e3 : (0 : ℝ) ≤ ((S.N t ω - S.N (t - P.L2) ω : ℤ) : ℝ) := by
          exact_mod_cast S.incr_nonneg hv ω
        rw [← ENNReal.ofReal_mul hab, ← ENNReal.ofReal_add hc0 (mul_nonneg hab e3)]
        refine ENNReal.ofReal_le_ofReal (hph.trans ?_)
        nlinarith
    _ = ENNReal.ofReal (Cphi (P := P) R1 R2 Q n) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ hmeas, S.lintegral_incr_val hv, ← ENNReal.ofReal_mul hab,
          ← ENNReal.ofReal_add hc0 (mul_nonneg hab (mul_nonneg P.lam_nonneg (by linarith)))]
        unfold Cphi
        congr 1
        ring

def gphi (t : ℝ) : ℝ :=
  (∫⁻ ω, ENNReal.ofReal (phi P.h2 P.p ((IL2c S R1 R2 Q n t ω : ℤ) : ℝ)) ∂S.ν).toReal

lemma gphi_bdd (t : ℝ) : |gphi S R1 R2 Q n t| ≤ Cphi (P := P) R1 R2 Q n := by
  unfold gphi
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_le_of_le_ofReal (Cphi_nonneg R1 R2 Q n) (lintegral_phi_IL2_le S R1 R2 Q n t)

lemma IL2c_joint_meas :
    Measurable (fun p : S.Ω × ℝ => ENNReal.ofReal (phi P.h2 P.p ((IL2c S R1 R2 Q n p.2 p.1 : ℤ) : ℝ))) := by
  have e : (fun p : S.Ω × ℝ => ENNReal.ofReal (phi P.h2 P.p ((IL2c S R1 R2 Q n p.2 p.1 : ℤ) : ℝ)))
      = (fun z : ℤ × ℤ => ENNReal.ofReal (phi P.h2 P.p ((sz Q R1 - (z.1 - ((mN Q n : ℕ) : ℤ)
          * ((z.2 + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) : ℤ) : ℝ)))
        ∘ (fun p : S.Ω × ℝ => (S.N p.2 p.1, S.N (p.2 + -P.L2) p.1)) := by
    funext p
    simp only [Function.comp_apply]
    unfold IL2c
    rw [IL2_eq', ← sub_eq_add_neg]
  rw [e]
  exact (measurable_of_countable _).comp (S.N_joint.prodMk (S.N_joint_shift (-P.L2)))

lemma gphi_meas : Measurable (gphi S R1 R2 Q n) :=
  ((IL2c_joint_meas S R1 R2 Q n).lintegral_prod_left').ennreal_toReal

theorem gphi_tendsto (hlam : 0 < P.lam) :
    Tendsto (gphi S R1 R2 Q n) atTop (𝓝 (∑ ρ ∈ Finset.Ico (0 : ℤ) (mN Q n),
      (1 / ((mN Q n : ℕ) : ℝ)) * Fimp P (((sz Q R1 + cz Q n R1 R2 - ρ : ℤ) : ℝ)))) := by
  have hm := mN_pos Q n
  have hx : Tendsto (fun t : ℝ => t - P.L2) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun b => ⟨b + P.L2, fun a ha => by linarith⟩)
  have hlim := tendsto_finsetSum (Finset.Ico (0 : ℤ) (mN Q n)) (fun ρ hρ =>
    ((S.shLaw_tendsto (mN Q n) hlam hm (cz Q n R1 R2) hρ).comp hx).mul_const
      (Fimp P (((sz Q R1 + cz Q n R1 R2 - ρ : ℤ) : ℝ))))
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop P.L2] with t ht
  unfold gphi
  rw [lintegral_phi_IL2 S R1 R2 Q n ht, ENNReal.toReal_sum (fun ρ _ =>
    ENNReal.mul_ne_top (S.shLaw_ne_top _ _ _ _) ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Fimp_nonneg P _)]
  rfl

lemma match_bdd {T : ℝ} (hT : 0 ≤ T) :
    |(∫⁻ ω, ENNReal.ofReal ((((Q : ℕ) : ℤ) * (Classical'.matchCount S (ctrl R1 R2 Q n) T ω
        - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω) : ℤ) : ℝ) ∂S.ν).toReal - P.lam * T|
      ≤ (((Q : ℕ) : ℝ) + |((cz Q n R1 R2 : ℤ) : ℝ)| + ((mN Q n : ℕ) : ℝ) + P.lam * P.L2) := by
  have hBc : 0 ≤ (((Q : ℕ) : ℝ) + |((cz Q n R1 R2 : ℤ) : ℝ)| + ((mN Q n : ℕ) : ℝ) + P.lam * P.L2) := by
    have := P.lam_nonneg; have := P.L2_nonneg; positivity
  have hB_ne : ∀ t, ∫⁻ ω, (ENNReal.ofReal (((S.N (t) ω % ((Q : ℕ) : ℤ) : ℤ)) : ℝ) + ENNReal.ofReal (((((Q : ℕ) : ℤ) * max ((S.N (t) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (t - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) / ((Q : ℕ) : ℤ)) 0 : ℤ)) : ℝ)) ∂S.ν ≠ ⊤ := fun t =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (lintegral_B_le S R1 R2 Q n t)
  obtain ⟨_, hM⟩ := toReal_add_eq (lintegral_match_id S R1 R2 Q n hT) (hB_ne T)
    ENNReal.ofReal_ne_top (hB_ne 0)
  rw [ENNReal.toReal_ofReal (mul_nonneg P.lam_nonneg hT)] at hM
  have hBT := ENNReal.toReal_le_of_le_ofReal hBc (lintegral_B_le S R1 R2 Q n T)
  have hB0 := ENNReal.toReal_le_of_le_ofReal hBc (lintegral_B_le S R1 R2 Q n 0)
  have hBT0 : 0 ≤ (∫⁻ ω, (ENNReal.ofReal (((S.N (T) ω % ((Q : ℕ) : ℤ) : ℤ)) : ℝ) + ENNReal.ofReal (((((Q : ℕ) : ℤ) * max ((S.N (T) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (T - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) / ((Q : ℕ) : ℤ)) 0 : ℤ)) : ℝ)) ∂S.ν).toReal := ENNReal.toReal_nonneg
  have hB00 : 0 ≤ (∫⁻ ω, (ENNReal.ofReal (((S.N (0) ω % ((Q : ℕ) : ℤ) : ℤ)) : ℝ) + ENNReal.ofReal (((((Q : ℕ) : ℤ) * max ((S.N (0) ω - ((mN Q n : ℕ) : ℤ) * ((S.N (0 - P.L2) ω + cz Q n R1 R2) / ((mN Q n : ℕ) : ℤ))) / ((Q : ℕ) : ℤ)) 0 : ℤ)) : ℝ)) ∂S.ν).toReal := ENNReal.toReal_nonneg
  rw [abs_le]; constructor <;> linarith

end Upstream

section LowerBound

variable {P : Params} (S : DemandSpace P) (R1 R2 : ℤ) (Q n : ℕ+)

theorem ship_lb_ctrl (hlam : 0 < P.lam) :
    ENNReal.ofReal (∑ ρ ∈ Finset.Ico (0 : ℤ) (mN Q n),
        (1 / ((mN Q n : ℕ) : ℝ)) * Fimp P (((sz Q R1 + cz Q n R1 R2 - ρ : ℤ) : ℝ))
      + P.K1 / ((mN Q n : ℕ) : ℝ) * P.lam)
      ≤ classicalShipCost P S (ctrl R1 R2 Q n) := by
  have hmR : (0 : ℝ) < ((mN Q n : ℕ) : ℝ) := by exact_mod_cast mN_pos Q n
  have hK : 0 ≤ P.K1 / ((mN Q n : ℕ) : ℝ) := div_nonneg P.K1_nonneg hmR.le
  have hgm := gphi_meas S R1 R2 Q n
  have hgb := gphi_bdd S R1 R2 Q n
  have hii := iiOfBdd hgm hgb
  have hces := cesaro_Ioc hgm hgb (gphi_tendsto S R1 R2 Q n hlam)
  have hut := tendsto_of_bdd (a := fun T => (∫⁻ ω, ENNReal.ofReal ((((Q : ℕ) : ℤ)
      * (Classical'.matchCount S (ctrl R1 R2 Q n) T ω
        - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω) : ℤ) : ℝ) ∂S.ν).toReal) (c := P.lam)
    (fun T hT => match_bdd S R1 R2 Q n hT)
  have hlim := hces.add (hut.const_mul (P.K1 / ((mN Q n : ℕ) : ℝ)))
  have hlim' : Tendsto (fun T => T⁻¹ * ((∫ t in Set.Ioc 0 T, gphi S R1 R2 Q n t)
      + P.K1 / ((mN Q n : ℕ) : ℝ) * (∫⁻ ω, ENNReal.ofReal ((((Q : ℕ) : ℤ)
      * (Classical'.matchCount S (ctrl R1 R2 Q n) T ω
        - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω) : ℤ) : ℝ) ∂S.ν).toReal)) atTop
      (𝓝 (∑ ρ ∈ Finset.Ico (0 : ℤ) (mN Q n),
        (1 / ((mN Q n : ℕ) : ℝ)) * Fimp P (((sz Q R1 + cz Q n R1 R2 - ρ : ℤ) : ℝ))
      + P.K1 / ((mN Q n : ℕ) : ℝ) * P.lam)) := by
    refine hlim.congr (fun T => ?_)
    ring
  unfold classicalShipCost longRunCost
  rw [← (ENNReal.tendsto_ofReal hlim').limsup_eq]
  refine Filter.limsup_le_limsup ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have hT' : 0 ≤ T⁻¹ := inv_nonneg.mpr hT.le
  have hgi : 0 ≤ ∫ t in Set.Ioc 0 T, gphi S R1 R2 Q n t :=
    integral_nonneg (fun t => ENNReal.toReal_nonneg)
  have hu0 : 0 ≤ (∫⁻ ω, ENNReal.ofReal ((((Q : ℕ) : ℤ)
      * (Classical'.matchCount S (ctrl R1 R2 Q n) T ω
        - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω) : ℤ) : ℝ) ∂S.ν).toReal := ENNReal.toReal_nonneg
  rw [ENNReal.ofReal_mul hT', ENNReal.ofReal_add hgi (mul_nonneg hK hu0), ENNReal.ofReal_mul hK]
  refine mul_le_mul' le_rfl ?_
  have hcm := cI_joint_meas S R1 R2 Q n
  rw [lintegral_add_left (Measurable.lintegral_prod_right' (ν := volume.restrict (Set.Ioc 0 T)) hcm)]
  refine add_le_add ?_ ?_
  ·
    have hint : Integrable (gphi S R1 R2 Q n) (volume.restrict (Set.Ioc 0 T)) := (hii 0 T).1
    rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun t => ENNReal.toReal_nonneg)),
      lintegral_lintegral_swap (μ := S.ν) (ν := volume.restrict (Set.Ioc 0 T))
        (f := fun ω t => ENNReal.ofReal (Classical'.cI S (ctrl R1 R2 Q n) t ω))
        (Measurable.aemeasurable hcm)]
    refine lintegral_mono (fun t => ?_)
    unfold gphi
    rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (lintegral_phi_IL2_le S R1 R2 Q n t))]
    exact lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal (phi_le_cI S R1 R2 Q n t ω))
  ·
    have hmm : Measurable (fun ω => ENNReal.ofReal ((((Q : ℕ) : ℤ)
        * (Classical'.matchCount S (ctrl R1 R2 Q n) T ω
          - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω) : ℤ) : ℝ)) := by
      have h := (measurable_of_countable (fun z : ℤ × ℤ => ENNReal.ofReal
        ((((Q : ℕ) : ℤ) * (z.1 - z.2) : ℤ) : ℝ))).comp
        ((match_meas S R1 R2 Q n T).prodMk (match_meas S R1 R2 Q n 0))
      exact h
    have hne : ∫⁻ ω, ENNReal.ofReal ((((Q : ℕ) : ℤ)
        * (Classical'.matchCount S (ctrl R1 R2 Q n) T ω
          - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω) : ℤ) : ℝ) ∂S.ν ≠ ⊤ := by
      have h := lintegral_match_id S R1 R2 Q n hT.le
      intro htop
      rw [htop, top_add] at h
      exact (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (lintegral_B_le S R1 R2 Q n 0)⟩) h.symm
    rw [ENNReal.ofReal_toReal hne, ← lintegral_const_mul _ hmm]
    refine lintegral_mono_ae ?_
    filter_upwards [U1_diff_le_jumps S R1 R2 Q n hT] with ω hω
    have hJ1 : (0 : ℝ) ≤ (jumpCount (fun t => Classical'.U2 S (ctrl R1 R2 Q n) t ω) T : ℝ) :=
      Nat.cast_nonneg _
    have hdq : Classical'.U1 S (ctrl R1 R2 Q n) T ω - Classical'.U1 S (ctrl R1 R2 Q n) 0 ω
        = ((Q : ℕ) : ℤ) * (Classical'.matchCount S (ctrl R1 R2 Q n) T ω
          - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω) := by
      show ((Q : ℕ) : ℤ) * Classical'.matchCount S (ctrl R1 R2 Q n) T ω
        - ((Q : ℕ) : ℤ) * Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω = _
      ring
    rw [hdq] at hω
    have hω' : ((((Q : ℕ) : ℤ) * (Classical'.matchCount S (ctrl R1 R2 Q n) T ω
          - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω) : ℤ) : ℝ)
        ≤ ((mN Q n : ℕ) : ℝ) * (jumpCount (fun t => Classical'.U1 S (ctrl R1 R2 Q n) t ω) T : ℝ) := by
      exact_mod_cast hω
    rw [← ENNReal.ofReal_mul hK]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : P.K1 / ((mN Q n : ℕ) : ℝ) * ((((Q : ℕ) : ℤ) * (Classical'.matchCount S (ctrl R1 R2 Q n) T ω
          - Classical'.matchCount S (ctrl R1 R2 Q n) 0 ω) : ℤ) : ℝ)
        ≤ P.K1 * (jumpCount (fun t => Classical'.U1 S (ctrl R1 R2 Q n) t ω) T : ℝ) := by
      calc _ ≤ P.K1 / ((mN Q n : ℕ) : ℝ) * (((mN Q n : ℕ) : ℝ)
            * (jumpCount (fun t => Classical'.U1 S (ctrl R1 R2 Q n) t ω) T : ℝ)) :=
          mul_le_mul_of_nonneg_left hω' hK
        _ = _ := by field_simp
    have h2 : 0 ≤ P.K2 * (jumpCount (fun t => Classical'.U2 S (ctrl R1 R2 Q n) t ω) T : ℝ) :=
      mul_nonneg P.K2_nonneg hJ1
    linarith

theorem ship_ge_reduce (c : ClassicalControls) :
    classicalShipCost P S (ctrl c.1.1 (c.1.2.1 - (c.1.2.2.2.2 : ℤ)) c.1.2.2.1 c.1.2.2.2.1)
      ≤ classicalShipCost P S c := by
  obtain ⟨⟨R1, R2, Q, n, ρ⟩, hρ⟩ := c
  have hO : ∀ t ω, Classical'.ordCount S ⟨(R1, R2, Q, n, ρ), hρ⟩ t ω
      = Classical'.ordCount S (ctrl R1 (R2 - (ρ : ℤ)) Q n) t ω := by
    intro t ω
    show ⌊(((S.N t ω : ℤ) : ℝ) + ((R2 - R1 : ℤ) : ℝ) - ((ρ : ℕ) : ℝ)
        + (((n : ℕ) : ℝ) - 1) * ((Q : ℕ) : ℝ)) / (((n : ℕ) : ℝ) * ((Q : ℕ) : ℝ))⌋
      = ⌊(((S.N t ω : ℤ) : ℝ) + ((R2 - (ρ : ℤ) - R1 : ℤ) : ℝ) - ((0 : ℕ) : ℝ)
        + (((n : ℕ) : ℝ) - 1) * ((Q : ℕ) : ℝ)) / (((n : ℕ) : ℝ) * ((Q : ℕ) : ℝ))⌋
    congr 1
    push_cast
    ring
  have hU1 : ∀ t ω, Classical'.U1 S ⟨(R1, R2, Q, n, ρ), hρ⟩ t ω
      = Classical'.U1 S (ctrl R1 (R2 - (ρ : ℤ)) Q n) t ω := by
    intro t ω
    unfold Classical'.U1 Classical'.matchCount Classical'.recvCount
    rw [hO]
    rfl
  have hU2 : ∀ t ω, Classical'.U2 S ⟨(R1, R2, Q, n, ρ), hρ⟩ t ω
      = Classical'.U2 S (ctrl R1 (R2 - (ρ : ℤ)) Q n) t ω := by
    intro t ω
    unfold Classical'.U2
    rw [hO]
    rfl
  have hcI : ∀ t ω, Classical'.cI S (ctrl R1 (R2 - (ρ : ℤ)) Q n) t ω
      ≤ Classical'.cI S ⟨(R1, R2, Q, n, ρ), hρ⟩ t ω := by
    intro t ω
    unfold Classical'.cI costRate netInv
    rw [hU1, hU2]
    have hx1 : Classical'.x1 S ⟨(R1, R2, Q, n, ρ), hρ⟩ ω
        = Classical'.x1 S (ctrl R1 (R2 - (ρ : ℤ)) Q n) ω := rfl
    have hx2 : Classical'.x2 S ⟨(R1, R2, Q, n, ρ), hρ⟩ ω
        = Classical'.x2 S (ctrl R1 (R2 - (ρ : ℤ)) Q n) ω + (ρ : ℤ) := by
      show R1 + ((Q : ℕ) : ℤ) + ((ρ : ℕ) : ℤ) = R1 + ((Q : ℕ) : ℤ) + ((0 : ℕ) : ℤ) + (ρ : ℤ)
      push_cast; ring
    rw [hx1, hx2]
    push_cast
    have : (0 : ℝ) ≤ (ρ : ℝ) := Nat.cast_nonneg ρ
    nlinarith [P.h2_nonneg]
  have hZ : (fun T ω => P.K1 * (jumpCount (fun t => Classical'.U1 S ⟨(R1, R2, Q, n, ρ), hρ⟩ t ω) T : ℝ)
        + P.K2 * (jumpCount (fun t => Classical'.U2 S ⟨(R1, R2, Q, n, ρ), hρ⟩ t ω) T : ℝ))
      = (fun T ω => P.K1 * (jumpCount (fun t => Classical'.U1 S (ctrl R1 (R2 - (ρ : ℤ)) Q n) t ω) T : ℝ)
        + P.K2 * (jumpCount (fun t => Classical'.U2 S (ctrl R1 (R2 - (ρ : ℤ)) Q n) t ω) T : ℝ)) := by
    funext T ω
    simp only [hU1, hU2]
  show longRunCost S.ν (Classical'.cI S (ctrl R1 (R2 - (ρ : ℤ)) Q n)) (fun T ω =>
      P.K1 * (jumpCount (fun t => Classical'.U1 S (ctrl R1 (R2 - (ρ : ℤ)) Q n) t ω) T : ℝ)
        + P.K2 * (jumpCount (fun t => Classical'.U2 S (ctrl R1 (R2 - (ρ : ℤ)) Q n) t ω) T : ℝ))
    ≤ longRunCost S.ν (Classical'.cI S ⟨(R1, R2, Q, n, ρ), hρ⟩) (fun T ω =>
      P.K1 * (jumpCount (fun t => Classical'.U1 S ⟨(R1, R2, Q, n, ρ), hρ⟩ t ω) T : ℝ)
        + P.K2 * (jumpCount (fun t => Classical'.U2 S ⟨(R1, R2, Q, n, ρ), hρ⟩ t ω) T : ℝ))
  rw [hZ]
  unfold longRunCost
  refine Filter.limsup_le_limsup (Eventually.of_forall (fun T => ?_))
  exact mul_le_mul' le_rfl (lintegral_mono (fun ω => add_le_add
    (lintegral_mono (fun t => ENNReal.ofReal_le_ofReal (hcI t ω))) le_rfl))

lemma sum_reindex (f : ℝ → ℝ) (A : ℤ) (m : ℕ) :
    ∑ ρ ∈ Finset.Ico (0 : ℤ) m, f (((A + m - ρ : ℤ) : ℝ))
      = ∑ j ∈ Finset.range m, f (((A + 1 + j : ℤ) : ℝ)) := by
  refine Finset.sum_nbij' (fun ρ => (((m : ℤ) - 1 - ρ).toNat)) (fun j => (m : ℤ) - 1 - j)
    ?_ ?_ ?_ ?_ ?_
  · intro ρ hρ
    simp only [Finset.mem_Ico] at hρ
    simp only [Finset.mem_range]
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    simp only [Finset.mem_Ico]
    omega
  · intro ρ hρ
    simp only [Finset.mem_Ico] at hρ
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    omega
  · intro ρ hρ
    simp only [Finset.mem_Ico] at hρ
    congr 2
    rw [Int.toNat_of_nonneg (by omega)]
    ring

theorem classical_ship_lb (hlam : 0 < P.lam) (c : ClassicalControls) :
    ∃ m : ℕ, 0 < m ∧ ∃ σ : ℤ,
      ENNReal.ofReal (P.lam * P.K1 / m + (∑ j ∈ Finset.range m, Fimp P ((σ + j : ℤ) : ℝ)) / m)
        ≤ classicalShipCost P S c := by
  set R1 := c.1.1
  set R2' := c.1.2.1 - (c.1.2.2.2.2 : ℤ)
  set Q := c.1.2.2.1
  set n := c.1.2.2.2.1
  refine ⟨mN Q n, mN_pos Q n, R2' + 1, le_trans (le_of_eq ?_)
    ((ship_lb_ctrl S R1 R2' Q n hlam).trans (ship_ge_reduce S c))⟩
  congr 1
  have hsc : sz Q R1 + cz Q n R1 R2' = R2' + ((mN Q n : ℕ) : ℤ) := by
    unfold sz cz; rw [mN_cast]; ring
  have e1 : ∑ ρ ∈ Finset.Ico (0 : ℤ) (mN Q n), (1 / ((mN Q n : ℕ) : ℝ))
      * Fimp P (((sz Q R1 + cz Q n R1 R2' - ρ : ℤ) : ℝ))
      = (∑ j ∈ Finset.range (mN Q n), Fimp P (((R2' + 1 + j : ℤ) : ℝ))) / ((mN Q n : ℕ) : ℝ) := by
    rw [← Finset.mul_sum, hsc, sum_reindex (Fimp P) R2' (mN Q n)]
    ring
  rw [e1]
  ring

end LowerBound

end Imp

end TwoStageRnQ

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace Imp

def hh (s : ℕ) : ℝ := poisW (1 / (s : ℝ)) s

def alp : ℝ := 2 - Real.sqrt 3

lemma hh_pos {s : ℕ} (hs : 0 < s) : 0 < hh s := by
  unfold hh poisW
  have : (0 : ℝ) < s := by exact_mod_cast hs
  positivity

lemma poisW_le_one {μ : ℝ} (hμ : 0 ≤ μ) (n : ℕ) : poisW μ n ≤ 1 := by
  rw [← tsum_poisW μ]
  exact (summable_poisW μ).le_tsum n (fun j _ => poisW_nonneg hμ j)

lemma hh_le_one (s : ℕ) : hh s ≤ 1 := poisW_le_one (by positivity) s

lemma sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

lemma sqrt3_lt_two : Real.sqrt 3 < 2 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma sqrt3_gt : (3 : ℝ) / 2 < Real.sqrt 3 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

lemma alp_pos : 0 < alp := by unfold alp; linarith [sqrt3_lt_two]

lemma alp_le_half : alp ≤ 1 / 2 := by unfold alp; linarith [sqrt3_gt]

def Pimp (s : ℕ) (hs : 0 < s) : Params where
  lam := 1
  L1 := hh s / 4
  L2 := 1 / s
  h1 := hh s / s
  h2 := hh s
  p := 1
  K1 := alp * hh s * (s : ℝ) ^ 2
  K2 := hh s
  lam_nonneg := zero_le_one
  L1_nonneg := (div_pos (hh_pos hs) (by norm_num)).le
  L2_nonneg := by positivity
  h1_nonneg := (div_pos (hh_pos hs) (by exact_mod_cast hs)).le
  h2_nonneg := (hh_pos hs).le
  p_nonneg := zero_le_one
  K1_nonneg := by have := alp_pos; have := hh_pos hs; positivity
  K2_nonneg := (hh_pos hs).le

lemma phi_ge_abs {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (x : ℝ) : a * |x| ≤ phi a b x := by
  unfold phi
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, max_eq_left hx, max_eq_right (by linarith : -x ≤ 0)]; linarith
  · rw [abs_of_nonpos hx, max_eq_right hx, max_eq_left (by linarith : 0 ≤ -x)]; nlinarith

theorem sum_abs_ge (m : ℕ) : ∀ y : ℝ, ((m : ℝ) ^ 2 - 1) / 4 ≤ ∑ j ∈ Finset.range m, |y + j| := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro y
    rcases m with _ | _ | m
    · simp; norm_num
    · simp
    · have h := ih m (by omega) (y + 1)
      rw [Finset.sum_range_succ, Finset.sum_range_succ']
      have e : ∀ j : ℕ, |y + ((j + 1 : ℕ) : ℝ)| = |(y + 1) + (j : ℝ)| := by
        intro j; push_cast; ring_nf
      simp_rw [e]
      have h2 : (m : ℝ) + 1 ≤ |y| + |(y + 1) + (m : ℝ)| := by
        have h4 := abs_sub ((y + 1) + (m : ℝ)) y
        have h3 : |(y + 1) + (m : ℝ) - y| = (m : ℝ) + 1 := by
          rw [show (y + 1) + (m : ℝ) - y = (m : ℝ) + 1 by ring]
          exact abs_of_nonneg (by positivity)
        linarith
      simp only [Nat.cast_zero, add_zero]
      push_cast at h ⊢
      linarith

lemma sum_range_cast (m : ℕ) : ∑ j ∈ Finset.range m, (j : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma poisW_two_ratio {s : ℕ} (hs : 2 ≤ s) :
    poisW (1 / (s : ℝ)) (s - 2) = hh s * (s : ℝ) ^ 3 * ((s : ℝ) - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 2 := ⟨s - 2, by omega⟩
  unfold hh
  rw [show k + 2 - 2 = k by omega]
  set μ := 1 / ((k + 2 : ℕ) : ℝ) with hμdef
  have h1 := poisW_succ_mul μ (k + 1)
  have h2 := poisW_succ_mul μ k
  have hμ : μ * ((k : ℝ) + 2) = 1 := by
    rw [hμdef]; push_cast; field_simp
  push_cast at h1 h2 ⊢
  have e : poisW μ (k + 2) * ((k : ℝ) + 2) * ((k : ℝ) + 1) = μ ^ 2 * poisW μ k := by
    have h1' : poisW μ (k + 1 + 1) * ((k : ℝ) + 1 + 1) = μ * poisW μ (k + 1) := h1
    rw [show k + 1 + 1 = k + 2 by omega] at h1'
    calc poisW μ (k + 2) * ((k : ℝ) + 2) * ((k : ℝ) + 1)
        = (poisW μ (k + 2) * ((k : ℝ) + 1 + 1)) * ((k : ℝ) + 1) := by ring
      _ = μ * poisW μ (k + 1) * ((k : ℝ) + 1) := by rw [h1']
      _ = μ * (poisW μ (k + 1) * ((k : ℝ) + 1)) := by ring
      _ = μ * (μ * poisW μ k) := by rw [h2]
      _ = μ ^ 2 * poisW μ k := by ring
  have hk2 : ((k : ℝ) + 2) ^ 2 * μ ^ 2 = 1 := by rw [← mul_pow, mul_comm, hμ, one_pow]
  calc poisW μ k = ((k : ℝ) + 2) ^ 2 * μ ^ 2 * poisW μ k := by rw [hk2, one_mul]
    _ = poisW μ (k + 2) * ((k : ℝ) + 2) ^ 3 * ((k : ℝ) + 2 - 1) := by
        rw [mul_assoc, ← e]; ring

section FBounds

variable {s : ℕ} (hs : 0 < s)

lemma Fimp_pint (z : ℝ) : PInt (Pimp s hs).mu2 (fun d : ℕ => phi (Pimp s hs).h2 (Pimp s hs).p (z - d)) :=
  (phi_linGrowth (Pimp s hs).h2_nonneg (Pimp s hs).p_nonneg z).pint (Pimp s hs).mu2_nonneg

lemma mu2_eq : (Pimp s hs).mu2 = 1 / (s : ℝ) := by
  show (1 : ℝ) * (1 / (s : ℝ)) = 1 / (s : ℝ); ring

lemma Fimp_ge_lin (z : ℝ) : hh s * (z - 1 / (s : ℝ)) ≤ Fimp (Pimp s hs) z := by
  have hμ := (Pimp s hs).mu2_nonneg
  have h1 : pexp (Pimp s hs).mu2 (fun d : ℕ => hh s * z - hh s * (d : ℝ))
      ≤ Fimp (Pimp s hs) z := by
    unfold Fimp
    refine pexp_mono hμ ((linGrowth_const _).sub (linGrowth_nat.const_mul _) |>.pint hμ)
      (Fimp_pint hs z) (fun d => ?_)
    have := phi_ge_left (Pimp s hs).h2_nonneg (Pimp s hs).p_nonneg (z - d)
    show hh s * z - hh s * (d : ℝ) ≤ phi (hh s) 1 (z - d)
    have e : hh s * z - hh s * (d : ℝ) = hh s * (z - d) := by ring
    rw [e]; exact this
  rw [pexp_sub hμ (pint_const _) (pint_nat.const_mul _), pexp_const, pexp_const_mul, pexp_nat,
    mu2_eq hs] at h1
  linarith

lemma Fimp_sum_ge_abs (m : ℕ) (σ : ℤ) :
    hh s * (((m : ℝ) ^ 2 - 1) / 4) ≤ ∑ j ∈ Finset.range m, Fimp (Pimp s hs) ((σ + j : ℤ) : ℝ) := by
  have hμ := (Pimp s hs).mu2_nonneg
  have hpi : ∀ j ∈ Finset.range m,
      PInt (Pimp s hs).mu2 (fun d : ℕ => phi (Pimp s hs).h2 (Pimp s hs).p (((σ + j : ℤ) : ℝ) - d)) :=
    fun j _ => Fimp_pint hs _
  unfold Fimp
  rw [← pexp_finset_sum hμ _ hpi]
  have h2 : pexp (Pimp s hs).mu2 (fun _ : ℕ => hh s * (((m : ℝ) ^ 2 - 1) / 4))
      ≤ pexp (Pimp s hs).mu2 (fun d : ℕ => ∑ j ∈ Finset.range m,
          phi (Pimp s hs).h2 (Pimp s hs).p (((σ + j : ℤ) : ℝ) - d)) := by
    refine pexp_mono hμ (pint_const _) (PInt.sum hμ _ hpi) (fun d => ?_)
    have hb := sum_abs_ge m ((σ : ℝ) - d)
    calc hh s * (((m : ℝ) ^ 2 - 1) / 4) ≤ hh s * ∑ j ∈ Finset.range m, |((σ : ℝ) - d) + j| :=
          mul_le_mul_of_nonneg_left hb (hh_pos hs).le
      _ = ∑ j ∈ Finset.range m, hh s * |(((σ + j : ℤ) : ℝ) - d)| := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          congr 2
          push_cast; ring
      _ ≤ _ := Finset.sum_le_sum (fun j _ =>
          phi_ge_abs (hh_pos hs).le (hh_le_one s) _)
  rwa [pexp_const] at h2

lemma Fimp_ge_short (h2s : 2 ≤ s) {σ : ℤ} (hσ : σ ≤ (s : ℤ) - 3) :
    hh s * (s : ℝ) ^ 3 * ((s : ℝ) - 1) ≤ Fimp (Pimp s hs) (σ : ℝ) := by
  have hμ := (Pimp s hs).mu2_nonneg
  rw [← poisW_two_ratio h2s, ← mu2_eq hs]
  unfold Fimp pexp
  have hsum := (Fimp_pint hs (σ : ℝ)).summable hμ
  have hterm := hsum.le_tsum (s - 2) (fun j _ => mul_nonneg (poisW_nonneg hμ j)
    (phi_nonneg (Pimp s hs).h2_nonneg (Pimp s hs).p_nonneg _))
  refine le_trans ?_ hterm
  have hphi : 1 ≤ phi (Pimp s hs).h2 (Pimp s hs).p ((σ : ℝ) - ((s - 2 : ℕ) : ℝ)) := by
    have h := phi_ge_right (Pimp s hs).h2_nonneg (Pimp s hs).p_nonneg ((σ : ℝ) - ((s - 2 : ℕ) : ℝ))
    have hc : ((s - 2 : ℕ) : ℝ) = (s : ℝ) - 2 := by
      rw [Nat.cast_sub h2s]; push_cast; ring
    have hσ' : (σ : ℝ) ≤ (s : ℝ) - 3 := by exact_mod_cast hσ
    show 1 ≤ phi (hh s) 1 ((σ : ℝ) - ((s - 2 : ℕ) : ℝ))
    have h' : -(1 * ((σ : ℝ) - ((s - 2 : ℕ) : ℝ))) ≤ phi (hh s) 1 ((σ : ℝ) - ((s - 2 : ℕ) : ℝ)) := h
    rw [hc] at h' ⊢
    linarith
  calc poisW (Pimp s hs).mu2 (s - 2) = poisW (Pimp s hs).mu2 (s - 2) * 1 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hphi (poisW_nonneg hμ _)

end FBounds

theorem cyc_lb {s : ℕ} (hs : 30 ≤ s) (m : ℕ) (hm : 0 < m) (σ : ℤ) :
    hh s * (Real.sqrt 3 * s - 5 / 2 - 1 / s)
      ≤ (Pimp s (by omega)).lam * (Pimp s (by omega)).K1 / m
        + (∑ j ∈ Finset.range m, Fimp (Pimp s (by omega)) ((σ + j : ℤ) : ℝ)) / m := by
  have hs0 : 0 < s := by omega
  have hsR : (30 : ℝ) ≤ s := by exact_mod_cast hs
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hh0 := hh_pos hs0
  have ha := alp_pos
  have hK : 0 ≤ (Pimp s hs0).lam * (Pimp s hs0).K1 / m :=
    div_nonneg (mul_nonneg (Pimp s hs0).lam_nonneg (Pimp s hs0).K1_nonneg) hmR.le
  have hFnn : ∀ j ∈ Finset.range m, 0 ≤ Fimp (Pimp s hs0) ((σ + j : ℤ) : ℝ) :=
    fun j _ => Fimp_nonneg _ _
  have hT2 : hh s * (Real.sqrt 3 * s - 5 / 2 - 1 / s) ≤ 2 * hh s * s := by
    have : Real.sqrt 3 * s - 5 / 2 - 1 / s ≤ 2 * s := by
      have h1 : 0 ≤ 1 / (s : ℝ) := by positivity
      nlinarith [sqrt3_lt_two]
    nlinarith
  by_cases hA : 12 * (s : ℝ) ≤ m
  ·
    have hsum := Fimp_sum_ge_abs hs0 m σ
    have hdiv : hh s * (((m : ℝ) ^ 2 - 1) / 4) / m ≤
        (∑ j ∈ Finset.range m, Fimp (Pimp s hs0) ((σ + j : ℤ) : ℝ)) / m :=
      div_le_div_of_nonneg_right hsum hmR.le
    have hb : 2 * hh s * s ≤ hh s * (((m : ℝ) ^ 2 - 1) / 4) / m := by
      rw [le_div_iff₀ hmR]
      have key : 2 * (s : ℝ) * m ≤ ((m : ℝ) ^ 2 - 1) / 4 := by nlinarith
      have := mul_le_mul_of_nonneg_left key hh0.le
      linarith
    linarith
  · push_neg at hA
    by_cases hB : σ ≤ (s : ℤ) - 3
    ·
      have h1 := Fimp_ge_short hs0 (by omega) hB
      have hsum : Fimp (Pimp s hs0) ((σ : ℤ) : ℝ)
          ≤ ∑ j ∈ Finset.range m, Fimp (Pimp s hs0) ((σ + j : ℤ) : ℝ) := by
        have := Finset.single_le_sum hFnn (Finset.mem_range.mpr hm)
        simpa using this
      have hdiv : hh s * (s : ℝ) ^ 3 * ((s : ℝ) - 1) / m ≤
          (∑ j ∈ Finset.range m, Fimp (Pimp s hs0) ((σ + j : ℤ) : ℝ)) / m :=
        div_le_div_of_nonneg_right (h1.trans hsum) hmR.le
      have hb : 2 * hh s * s ≤ hh s * (s : ℝ) ^ 3 * ((s : ℝ) - 1) / m := by
        rw [le_div_iff₀ hmR]
        have h3 : 2 * hh s * s * m ≤ 2 * hh s * s * (12 * s) := by
          apply mul_le_mul_of_nonneg_left hA.le; positivity
        have h4 : 2 * hh s * s * (12 * s) ≤ hh s * (s : ℝ) ^ 3 * ((s : ℝ) - 1) := by
          have h5 : (24 : ℝ) ≤ (s : ℝ) * ((s : ℝ) - 1) := by nlinarith
          have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ hh s * (s : ℝ) ^ 2)
          calc 2 * hh s * s * (12 * s) = hh s * (s : ℝ) ^ 2 * 24 := by ring
            _ ≤ hh s * (s : ℝ) ^ 2 * ((s : ℝ) * ((s : ℝ) - 1)) := h6
            _ = hh s * (s : ℝ) ^ 3 * ((s : ℝ) - 1) := by ring
        linarith
      linarith
    ·
      push_neg at hB
      have hσR : (s : ℝ) - 2 ≤ (σ : ℝ) := by
        have : (s : ℤ) - 2 ≤ σ := by omega
        exact_mod_cast this
      have hsum : hh s * ((m : ℝ) * σ + (m : ℝ) * ((m : ℝ) - 1) / 2 - m * (1 / (s : ℝ)))
          ≤ ∑ j ∈ Finset.range m, Fimp (Pimp s hs0) ((σ + j : ℤ) : ℝ) := by
        have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range m) =>
          Fimp_ge_lin hs0 ((σ + j : ℤ) : ℝ))
        refine le_trans (le_of_eq ?_) h
        rw [← Finset.mul_sum]
        congr 1
        push_cast
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_range_cast]
        simp
      have hdiv := div_le_div_of_nonneg_right hsum hmR.le
      have e1 : hh s * ((m : ℝ) * σ + (m : ℝ) * ((m : ℝ) - 1) / 2 - m * (1 / (s : ℝ))) / m
          = hh s * ((σ : ℝ) + ((m : ℝ) - 1) / 2 - 1 / (s : ℝ)) := by
        field_simp
      rw [e1] at hdiv
      have hK1 : (Pimp s hs0).lam * (Pimp s hs0).K1 / m = alp * hh s * (s : ℝ) ^ 2 / m := by
        show (1 : ℝ) * (alp * hh s * (s : ℝ) ^ 2) / m = _; ring
      rw [hK1]

      have hamgm : (Real.sqrt 3 - 1) * s ≤ alp * (s : ℝ) ^ 2 / m + (m : ℝ) / 2 := by
        rw [div_add_div _ _ hmR.ne' (by norm_num : (2 : ℝ) ≠ 0), le_div_iff₀ (by positivity)]
        have hsq := sqrt3_sq
        unfold alp
        nlinarith [sq_nonneg ((Real.sqrt 3 - 1) * s - m)]
      have hgoal : hh s * (Real.sqrt 3 * s - 5 / 2 - 1 / s)
          ≤ hh s * (alp * (s : ℝ) ^ 2 / m + ((σ : ℝ) + ((m : ℝ) - 1) / 2 - 1 / (s : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hh0.le
        linarith
      have e2 : hh s * (alp * (s : ℝ) ^ 2 / m + ((σ : ℝ) + ((m : ℝ) - 1) / 2 - 1 / (s : ℝ)))
          = alp * hh s * (s : ℝ) ^ 2 / m + hh s * ((σ : ℝ) + ((m : ℝ) - 1) / 2 - 1 / (s : ℝ)) := by
        ring
      linarith

end Imp

end TwoStageRnQ

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace Imp

open TwoStageRnQ.LB

section Policy

variable {P : Params} (S : DemandSpace P) (Sb : ℤ) (ε : ℝ)

def tg (j : ℕ) : ℝ := (j : ℝ) * ε

def uu : ℕ → S.Ω → ℤ
  | 0 => fun ω => S.N (-P.L2) ω
  | j + 1 => fun ω => if Sb + uu j ω - S.N (tg ε (j + 1)) ω < 0
      then S.N (tg ε (j + 1) - P.L2) ω else uu j ω

def U1c (t : ℝ) (ω : S.Ω) : ℤ :=
  if t < 0 then S.N (min t (-P.L2)) ω else uu S Sb ε ⌊t / ε⌋₊ ω

variable {S Sb ε}

lemma tg_zero : tg ε 0 = 0 := by simp [tg]

lemma tg_succ (j : ℕ) : tg ε (j + 1) = tg ε j + ε := by unfold tg; push_cast; ring

lemma tg_mono (hε : 0 ≤ ε) {i j : ℕ} (h : i ≤ j) : tg ε i ≤ tg ε j := by
  unfold tg
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) hε

lemma tg_nonneg (hε : 0 ≤ ε) (j : ℕ) : 0 ≤ tg ε j := by unfold tg; positivity

lemma floor_tg (hε : 0 < ε) (j : ℕ) : ⌊tg ε j / ε⌋₊ = j := by
  unfold tg; rw [mul_div_cancel_right₀ _ hε.ne', Nat.floor_natCast]

lemma tg_floor_le (hε : 0 < ε) {t : ℝ} (ht : 0 ≤ t) : tg ε ⌊t / ε⌋₊ ≤ t := by
  unfold tg
  have := Nat.floor_le (div_nonneg ht hε.le)
  calc (⌊t / ε⌋₊ : ℝ) * ε ≤ t / ε * ε := mul_le_mul_of_nonneg_right this hε.le
    _ = t := div_mul_cancel₀ t hε.ne'

lemma lt_tg_floor (hε : 0 < ε) (t : ℝ) : t < tg ε (⌊t / ε⌋₊ + 1) := by
  unfold tg
  have := Nat.lt_floor_add_one (t / ε)
  push_cast
  calc t = t / ε * ε := (div_mul_cancel₀ t hε.ne').symm
    _ < ((⌊t / ε⌋₊ : ℝ) + 1) * ε := mul_lt_mul_of_pos_right this hε

lemma floor_eq_of_mem (hε : 0 < ε) {t : ℝ} {j : ℕ} (h1 : tg ε j ≤ t) (h2 : t < tg ε (j + 1)) :
    ⌊t / ε⌋₊ = j := by
  unfold tg at h1 h2
  rw [Nat.floor_eq_iff (div_nonneg (le_trans (by positivity) h1) hε.le)]
  push_cast at h2
  constructor
  · rw [le_div_iff₀ hε]; exact h1
  · rw [div_lt_iff₀ hε]; exact h2

lemma U1c_nonneg_eq {t : ℝ} (ht : 0 ≤ t) (ω : S.Ω) :
    U1c S Sb ε t ω = uu S Sb ε ⌊t / ε⌋₊ ω := by
  unfold U1c; rw [if_neg (not_lt.mpr ht)]

lemma uu_succ (j : ℕ) (ω : S.Ω) :
    uu S Sb ε (j + 1) ω = if Sb + uu S Sb ε j ω - S.N (tg ε (j + 1)) ω < 0
      then S.N (tg ε (j + 1) - P.L2) ω else uu S Sb ε j ω := rfl

lemma uu_le (hε : 0 ≤ ε) (ω : S.Ω) : ∀ j, uu S Sb ε j ω ≤ S.N (tg ε j - P.L2) ω
  | 0 => by simp [uu, tg_zero]
  | j + 1 => by
    rw [uu_succ]
    split_ifs
    · exact le_rfl
    · have := uu_le hε ω j
      have h2 := S.N_mono ω (by linarith [tg_mono hε (Nat.le_succ j)] :
        tg ε j - P.L2 ≤ tg ε (j + 1) - P.L2)
      linarith

lemma uu_le_succ (hε : 0 ≤ ε) (ω : S.Ω) (j : ℕ) : uu S Sb ε j ω ≤ uu S Sb ε (j + 1) ω := by
  rw [uu_succ]
  split_ifs
  · have := uu_le (Sb := Sb) hε ω j
    have h2 := S.N_mono ω (by linarith [tg_mono hε (Nat.le_succ j)] :
      tg ε j - P.L2 ≤ tg ε (j + 1) - P.L2)
    linarith
  · exact le_rfl

lemma uu_mono (hε : 0 ≤ ε) (ω : S.Ω) : Monotone (fun j => uu S Sb ε j ω) :=
  monotone_nat_of_le_succ (uu_le_succ hε ω)

lemma post (ω : S.Ω) : ∀ j, uu S Sb ε j ω = S.N (tg ε j - P.L2) ω
    ∨ 0 ≤ Sb + uu S Sb ε j ω - S.N (tg ε j) ω
  | 0 => Or.inl (by simp [uu, tg_zero])
  | j + 1 => by
    rw [uu_succ]
    split_ifs with h
    · exact Or.inl rfl
    · exact Or.inr (by push_neg at h; exact h)

lemma uu_meas (hε : 0 ≤ ε) : ∀ j, Measurable[S.𝓕 (tg ε j)] (uu S Sb ε j)
  | 0 => by
    show Measurable[S.𝓕 (tg ε 0)] (fun ω => S.N (-P.L2) ω)
    rw [tg_zero]
    exact (S.N_adapted (-P.L2)).mono (S.𝓕.mono (by linarith [P.L2_nonneg])) le_rfl
  | j + 1 => by
    have hle : tg ε j ≤ tg ε (j + 1) := tg_mono hε (Nat.le_succ j)
    have h1 : Measurable[S.𝓕 (tg ε (j + 1))] (uu S Sb ε j) :=
      (uu_meas hε j).mono (S.𝓕.mono hle) le_rfl
    have h2 : Measurable[S.𝓕 (tg ε (j + 1))] (S.N (tg ε (j + 1))) := S.N_adapted _
    have h3 : Measurable[S.𝓕 (tg ε (j + 1))] (S.N (tg ε (j + 1) - P.L2)) :=
      (S.N_adapted _).mono (S.𝓕.mono (by linarith [P.L2_nonneg])) le_rfl
    have hset : MeasurableSet[S.𝓕 (tg ε (j + 1))]
        {ω | Sb + uu S Sb ε j ω - S.N (tg ε (j + 1)) ω < 0} := by
      have := (measurable_of_countable (fun z : ℤ × ℤ => decide (Sb + z.1 - z.2 < 0))).comp
        (h1.prodMk h2)
      have h' := this (measurableSet_singleton true)
      convert h' using 1
      ext ω; simp
    exact Measurable.ite hset h3 h1

lemma U1c_adapted (hε : 0 < ε) (t : ℝ) : Measurable[S.𝓕 t] (U1c S Sb ε t) := by
  by_cases ht : t < 0
  · have e : U1c S Sb ε t = fun ω => S.N (min t (-P.L2)) ω := by
      funext ω; unfold U1c; rw [if_pos ht]
    rw [e]
    exact (S.N_adapted _).mono (S.𝓕.mono (min_le_left _ _)) le_rfl
  · push_neg at ht
    have e : U1c S Sb ε t = uu S Sb ε ⌊t / ε⌋₊ := funext (fun ω => U1c_nonneg_eq ht ω)
    rw [e]
    exact (uu_meas hε.le _).mono (S.𝓕.mono (tg_floor_le hε ht)) le_rfl

lemma U1c_mono (hε : 0 < ε) (ω : S.Ω) : Monotone (fun t => U1c S Sb ε t ω) := by
  intro s t hst
  simp only
  by_cases hs : s < 0
  · unfold U1c
    rw [if_pos hs]
    by_cases ht : t < 0
    · rw [if_pos ht]; exact S.N_mono ω (min_le_min_right _ hst)
    · rw [if_neg ht]
      have h1 : S.N (min s (-P.L2)) ω ≤ S.N (-P.L2) ω := S.N_mono ω (min_le_right _ _)
      have h2 : uu S Sb ε 0 ω ≤ uu S Sb ε ⌊t / ε⌋₊ ω := uu_mono hε.le ω (Nat.zero_le _)
      have h0 : uu S Sb ε 0 ω = S.N (-P.L2) ω := rfl
      linarith
  · push_neg at hs
    rw [U1c_nonneg_eq hs, U1c_nonneg_eq (le_trans hs hst)]
    exact uu_mono hε.le ω (Nat.floor_mono (div_le_div_of_nonneg_right hst hε.le))

lemma U1c_rcont (hε : 0 < ε) (ω : S.Ω) (t : ℝ) :
    ∃ δ > 0, ∀ s, t ≤ s → s < t + δ → U1c S Sb ε s ω = U1c S Sb ε t ω := by
  by_cases ht : t < 0
  · by_cases ht2 : t < -P.L2
    · obtain ⟨δ, hδ, h⟩ := S.N_rcont ω t
      refine ⟨min δ (-P.L2 - t), lt_min hδ (by linarith), fun s h1 h2 => ?_⟩
      have hs : s < -P.L2 := by linarith [min_le_right δ (-P.L2 - t)]
      unfold U1c
      rw [if_pos (by linarith [P.L2_nonneg]), if_pos ht, min_eq_left hs.le, min_eq_left ht2.le]
      exact h s h1 (by linarith [min_le_left δ (-P.L2 - t)])
    · push_neg at ht2
      refine ⟨-t, by linarith, fun s h1 h2 => ?_⟩
      unfold U1c
      rw [if_pos (by linarith), if_pos ht, min_eq_right (by linarith), min_eq_right ht2]
  · push_neg at ht
    refine ⟨tg ε (⌊t / ε⌋₊ + 1) - t, by linarith [lt_tg_floor hε t], fun s h1 h2 => ?_⟩
    rw [U1c_nonneg_eq (le_trans ht h1), U1c_nonneg_eq ht,
      floor_eq_of_mem hε (le_trans (tg_floor_le hε ht) h1) (by linarith)]

lemma U1c_le (hε : 0 < ε) {t : ℝ} (ht : 0 ≤ t) (ω : S.Ω) : U1c S Sb ε t ω ≤ S.N (t - P.L2) ω := by
  rw [U1c_nonneg_eq ht]
  have := uu_le (Sb := Sb) hε.le ω ⌊t / ε⌋₊
  have h2 := S.N_mono ω (by linarith [tg_floor_le hε ht] : tg ε ⌊t / ε⌋₊ - P.L2 ≤ t - P.L2)
  linarith

lemma U1c_zero (hε : 0 < ε) (ω : S.Ω) : U1c S Sb ε 0 ω = S.N (-P.L2) ω := by
  rw [U1c_nonneg_eq le_rfl, zero_div, Nat.floor_zero]; rfl

def pol (hε : 0 < ε) : ShipmentPolicy P S where
  x1 := fun _ => Sb
  x2 := fun _ => Sb
  U1 := U1c S Sb ε
  U2 := S.N
  x1_meas := measurable_const
  x2_meas := measurable_const
  U1_adapted := U1c_adapted hε
  U2_adapted := S.N_adapted
  U1_mono := U1c_mono hε
  U2_mono := S.N_mono
  U1_rcont := U1c_rcont hε
  U2_rcont := S.N_rcont
  material := fun ω t ht => by
    show Sb + U1c S Sb ε t ω ≤ Sb + S.N (t - P.L2) ω
    linarith [U1c_le (Sb := Sb) hε ht ω]

def Dg (t : ℝ) (ω : S.Ω) : ℤ :=
  (S.N (tg ε (⌊t / ε⌋₊ + 1)) ω - S.N (tg ε ⌊t / ε⌋₊) ω)
    + (S.N (tg ε (⌊t / ε⌋₊ + 1) - P.L2) ω - S.N (tg ε ⌊t / ε⌋₊ - P.L2) ω)

lemma Dg_nonneg (hε : 0 < ε) (t : ℝ) (ω : S.Ω) : 0 ≤ Dg (S := S) (ε := ε) t ω := by
  unfold Dg
  have h := tg_mono hε.le (Nat.le_succ ⌊t / ε⌋₊)
  have h1 := S.N_mono ω h
  have h2 := S.N_mono ω (by linarith : tg ε ⌊t / ε⌋₊ - P.L2 ≤ tg ε (⌊t / ε⌋₊ + 1) - P.L2)
  linarith

lemma Xneg_le (hε : 0 < ε) {t : ℝ} (ht : 0 ≤ t) (ω : S.Ω) :
    max (-(Sb + U1c S Sb ε t ω - S.N t ω)) 0
      ≤ max (-(Sb + S.N (t - P.L2) ω - S.N t ω)) 0 + Dg (S := S) (ε := ε) t ω := by
  set j := ⌊t / ε⌋₊ with hj
  have h1 := tg_floor_le hε ht
  have h2 := lt_tg_floor hε t
  rw [← hj] at h1 h2
  rw [U1c_nonneg_eq ht, ← hj]
  unfold Dg
  rw [← hj]
  have m1 := S.N_mono ω h1
  have m2 := S.N_mono ω h2.le
  have m3 := S.N_mono ω (by linarith : tg ε j - P.L2 ≤ t - P.L2)
  have m4 := S.N_mono ω (by linarith : t - P.L2 ≤ tg ε (j + 1) - P.L2)
  rcases post (S := S) (Sb := Sb) (ε := ε) ω j with h | h
  · rw [h]
    have : -(Sb + S.N (tg ε j - P.L2) ω - S.N t ω) ≤ -(Sb + S.N (t - P.L2) ω - S.N t ω)
        + (S.N (tg ε (j + 1) - P.L2) ω - S.N (tg ε j - P.L2) ω) := by linarith
    have hm := le_max_left (-(Sb + S.N (t - P.L2) ω - S.N t ω)) 0
    have hm0 := le_max_right (-(Sb + S.N (t - P.L2) ω - S.N t ω)) 0
    rcases le_total (-(Sb + S.N (tg ε j - P.L2) ω - S.N t ω)) 0 with h' | h'
    · rw [max_eq_right h']; linarith
    · rw [max_eq_left h']; linarith
  · have : -(Sb + uu S Sb ε j ω - S.N t ω) ≤ S.N (tg ε (j + 1)) ω - S.N (tg ε j) ω := by linarith
    have hm0 := le_max_right (-(Sb + S.N (t - P.L2) ω - S.N t ω)) 0
    rcases le_total (-(Sb + uu S Sb ε j ω - S.N t ω)) 0 with h' | h'
    · rw [max_eq_right h']; linarith
    · rw [max_eq_left h']; linarith

theorem cI_le (hε : 0 < ε) (hSb : 0 ≤ Sb) {t : ℝ} (ht : 0 ≤ t) (ω : S.Ω) :
    (pol (S := S) (Sb := Sb) hε).cI t ω
      ≤ phi P.h2 P.p ((Sb + S.N (t - P.L2) ω - S.N t ω : ℤ) : ℝ) + P.h1 * Sb
        + (P.h2 + P.p) * (((Dg (S := S) (ε := ε) t ω : ℤ) : ℝ)
          + ((U1c S Sb ε t ω - U1c S Sb ε (t - P.L1) ω : ℤ) : ℝ)) := by
  have hX := Xneg_le (S := S) (Sb := Sb) hε ht ω
  have hW := U1c_le (S := S) (Sb := Sb) hε ht ω
  have hP1 := U1c_mono (S := S) (Sb := Sb) hε ω (by linarith [P.L1_nonneg] : t - P.L1 ≤ t)
  have hN := S.N_mono ω (by linarith [P.L2_nonneg] : t - P.L2 ≤ t)
  have hD := Dg_nonneg (S := S) (ε := ε) hε t ω
  show costRate P (fun _ => Sb) (fun _ => Sb) (U1c S Sb ε) S.N S.N t ω ≤ _
  unfold costRate netInv phi
  simp only
  set a : ℝ := ((Sb + U1c S Sb ε (t - P.L1) ω - S.N t ω : ℤ) : ℝ)
  set y : ℝ := ((Sb + S.N (t - P.L2) ω - S.N t ω : ℤ) : ℝ)
  set x : ℝ := ((Sb + U1c S Sb ε t ω - S.N t ω : ℤ) : ℝ)
  set d : ℝ := ((Dg (S := S) (ε := ε) t ω : ℤ) : ℝ)
  set q : ℝ := ((U1c S Sb ε t ω - U1c S Sb ε (t - P.L1) ω : ℤ) : ℝ)
  have hax : a = x - q := by simp only [a, x, q]; push_cast; ring
  have hxy : x ≤ y := by simp only [x, y]; exact_mod_cast (by linarith : Sb + U1c S Sb ε t ω - S.N t ω ≤ Sb + S.N (t - P.L2) ω - S.N t ω)
  have hyS : y ≤ (Sb : ℝ) := by simp only [y]; push_cast; exact_mod_cast (by linarith : Sb + S.N (t - P.L2) ω - S.N t ω ≤ Sb)
  have hq : 0 ≤ q := by simp only [q]; exact_mod_cast (by linarith : (0 : ℤ) ≤ U1c S Sb ε t ω - U1c S Sb ε (t - P.L1) ω)
  have hd : 0 ≤ d := by simp only [d]; exact_mod_cast hD
  have hX' : max (-x) 0 ≤ max (-y) 0 + d := by
    simp only [x, y, d]; push_cast at hX ⊢; exact_mod_cast hX
  have h1 := P.h1_nonneg
  have h2 := P.h2_nonneg
  have hp := P.p_nonneg

  have hapos : max a 0 ≤ (Sb : ℝ) := by
    rcases le_total a 0 with h | h
    · rw [max_eq_right h]; exact_mod_cast hSb
    · rw [max_eq_left h]; linarith
  have haneg : max (-a) 0 ≤ max (-y) 0 + d + q := by
    have : max (-a) 0 ≤ max (-x) 0 + q := by
      rcases le_total (-a) 0 with h | h
      · rw [max_eq_right h]; linarith [le_max_right (-x) 0]
      · rw [max_eq_left h]; rw [hax]; linarith [le_max_left (-x) 0]
    linarith
  have hphi : P.h2 * max y 0 + P.p * max (-y) 0 = P.h2 * y + (P.h2 + P.p) * max (-y) 0 := by
    rcases le_total y 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ -y)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith : -y ≤ 0)]; ring
  have e1 : P.h1 * max a 0 ≤ P.h1 * Sb := mul_le_mul_of_nonneg_left hapos h1
  have e2 : (P.h2 + P.p) * max (-a) 0 ≤ (P.h2 + P.p) * (max (-y) 0 + d + q) :=
    mul_le_mul_of_nonneg_left haneg (by linarith)
  nlinarith

end Policy

end Imp

end TwoStageRnQ

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace Imp

open TwoStageRnQ.LB

section PathFacts

variable {P : Params} {S : DemandSpace P} {Sb : ℤ} {ε : ℝ}

lemma U1c_nonpos {t : ℝ} (ht : t ≤ 0) (ω : S.Ω) :
    U1c S Sb ε t ω = S.N (min t (-P.L2)) ω := by
  rcases lt_or_eq_of_le ht with h | h
  · unfold U1c; rw [if_pos h]
  · subst h
    unfold U1c
    rw [if_neg (lt_irrefl 0), zero_div, Nat.floor_zero, min_eq_right (by linarith [P.L2_nonneg])]
    rfl

lemma U1c_ge (hε : 0 < ε) (hSb : 0 ≤ Sb) (t : ℝ) (ω : S.Ω) :
    S.N (t - (ε + P.L2)) ω - Sb ≤ U1c S Sb ε t ω := by
  by_cases ht : t < 0
  · rw [U1c_nonpos ht.le]
    have := S.N_mono ω (show t - (ε + P.L2) ≤ min t (-P.L2) from
      le_min (by linarith [P.L2_nonneg]) (by linarith))
    linarith
  · push_neg at ht
    rw [U1c_nonneg_eq ht]
    have h1 := tg_floor_le hε ht
    have h2 := lt_tg_floor hε t
    rw [tg_succ] at h2
    rcases post (S := S) (Sb := Sb) (ε := ε) ω ⌊t / ε⌋₊ with h | h
    · rw [h]
      have := S.N_mono ω (show t - (ε + P.L2) ≤ tg ε ⌊t / ε⌋₊ - P.L2 by linarith)
      linarith
    · have := S.N_mono ω (show t - (ε + P.L2) ≤ tg ε ⌊t / ε⌋₊ by linarith [P.L2_nonneg])
      linarith

lemma U1c_le_N (hε : 0 < ε) (t : ℝ) (ω : S.Ω) : U1c S Sb ε t ω ≤ S.N t ω := by
  by_cases ht : t < 0
  · rw [U1c_nonpos ht.le]; exact S.N_mono ω (min_le_left _ _)
  · push_neg at ht
    have := U1c_le (Sb := Sb) hε ht ω
    have h2 := S.N_mono ω (show t - P.L2 ≤ t by linarith [P.L2_nonneg])
    linarith

lemma IL1_ge (hε : 0 < ε) (hSb : 0 ≤ Sb) (T : ℝ) (ω : S.Ω) :
    -(S.N T ω - S.N (T - (P.L1 + (ε + P.L2))) ω)
      ≤ netInv P.L1 (fun _ => Sb) (U1c S Sb ε) S.N T ω := by
  unfold netInv
  have := U1c_ge (S := S) hε hSb (T - P.L1) ω
  have e : T - P.L1 - (ε + P.L2) = T - (P.L1 + (ε + P.L2)) := by ring
  rw [e] at this
  linarith

lemma IL1_le (hε : 0 < ε) (T : ℝ) (ω : S.Ω) :
    netInv P.L1 (fun _ => Sb) (U1c S Sb ε) S.N T ω ≤ Sb := by
  unfold netInv
  have := U1c_le_N (Sb := Sb) hε (T - P.L1) ω
  have h2 := S.N_mono ω (show T - P.L1 ≤ T by linarith [P.L1_nonneg])
  linarith

lemma jump_grid (hε : 0 < ε) (ω : S.Ω) {t : ℝ} (ht : 0 < t)
    (hj : ∀ s < t, U1c S Sb ε s ω < U1c S Sb ε t ω) :
    t = tg ε ⌊t / ε⌋₊ ∧ 1 ≤ ⌊t / ε⌋₊ ∧
      uu S Sb ε (⌊t / ε⌋₊ - 1) ω < uu S Sb ε ⌊t / ε⌋₊ ω := by
  have h1 : tg ε ⌊t / ε⌋₊ ≤ t := tg_floor_le hε ht.le
  have hUt : U1c S Sb ε t ω = uu S Sb ε ⌊t / ε⌋₊ ω := U1c_nonneg_eq ht.le ω
  have heq : t = tg ε ⌊t / ε⌋₊ := by
    by_contra hne
    have hlt : tg ε ⌊t / ε⌋₊ < t := lt_of_le_of_ne h1 (Ne.symm hne)
    have hs := hj (tg ε ⌊t / ε⌋₊) hlt
    rw [U1c_nonneg_eq (tg_nonneg hε.le _), floor_tg hε, hUt] at hs
    exact lt_irrefl _ hs
  have hj1 : 1 ≤ ⌊t / ε⌋₊ := by
    by_contra h0
    push_neg at h0
    have h00 : ⌊t / ε⌋₊ = 0 := by omega
    rw [h00, tg_zero] at heq
    linarith
  refine ⟨heq, hj1, ?_⟩
  have e : tg ε ⌊t / ε⌋₊ = tg ε (⌊t / ε⌋₊ - 1) + ε := by
    rw [← tg_succ]; congr 1; omega
  have hs := hj (tg ε (⌊t / ε⌋₊ - 1)) (by linarith)
  rw [U1c_nonneg_eq (tg_nonneg hε.le _), floor_tg hε, hUt] at hs
  exact hs

lemma jumpCount_U1c_le (hε : 0 < ε) (ω : S.Ω) (T : ℝ) :
    jumpCount (fun t => U1c S Sb ε t ω) T
      ≤ ((Finset.Icc 1 ⌊T / ε⌋₊).filter
          (fun j => uu S Sb ε (j - 1) ω < uu S Sb ε j ω)).card := by
  unfold jumpCount
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard_of_injOn (fun t => ⌊t / ε⌋₊) ?_ ?_ (Finset.finite_toSet _)
  · rintro t ⟨⟨ht0, htT⟩, hj⟩
    obtain ⟨-, hj1, hlt⟩ := jump_grid hε ω ht0 hj
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_setOf_eq]
    exact ⟨⟨hj1, Nat.floor_mono (div_le_div_of_nonneg_right htT hε.le)⟩, hlt⟩
  · rintro t1 ⟨⟨h10, _⟩, hj1⟩ t2 ⟨⟨h20, _⟩, hj2⟩ he
    obtain ⟨e1, -, -⟩ := jump_grid hε ω h10 hj1
    obtain ⟨e2, -, -⟩ := jump_grid hε ω h20 hj2
    simp only at he
    rw [e1, e2, he]

lemma jump_ineq (hε : 0 < ε) (hεL : ε ≤ P.L2) (hSb : 0 ≤ Sb) (i : ℕ) (ω : S.Ω) :
    Sb * (if uu S Sb ε i ω < uu S Sb ε (i + 1) ω then 1 else 0)
      ≤ (uu S Sb ε (i + 1) ω - uu S Sb ε i ω)
        + (S.N (tg ε (i + 1)) ω - S.N (tg ε i) ω) * (S.N (tg ε (i + 1)) ω - S.N (tg ε i) ω - 1)
        + (S.N (tg ε (i + 1)) ω - S.N (tg ε i) ω)
            * (S.N (tg ε i) ω - S.N (tg ε (i + 1) - P.L2) ω)
        + Sb * (if 2 ≤ S.N (tg ε (i + 1) - P.L2) ω - S.N (tg ε i - P.L2) ω then 1 else 0)
        + (S.N (tg ε (i + 1) - P.L2) ω - S.N (tg ε i - P.L2) ω)
            * (S.N (tg ε i) ω - S.N (tg ε (i + 1) - P.L2) ω) := by
  have hsucc := tg_succ (ε := ε) i
  have m1 : S.N (tg ε i) ω ≤ S.N (tg ε (i + 1)) ω := S.N_mono ω (show tg ε i ≤ tg ε (i + 1) by linarith)
  have m2 : S.N (tg ε (i + 1) - P.L2) ω ≤ S.N (tg ε i) ω :=
    S.N_mono ω (show tg ε (i + 1) - P.L2 ≤ tg ε i by linarith)
  have m3 : S.N (tg ε i - P.L2) ω ≤ S.N (tg ε (i + 1) - P.L2) ω :=
    S.N_mono ω (show tg ε i - P.L2 ≤ tg ε (i + 1) - P.L2 by linarith)
  have hsz := uu_le_succ (Sb := Sb) (S := S) hε.le ω i
  set c := S.N (tg ε (i + 1)) ω - S.N (tg ε i) ω with hc
  set B := S.N (tg ε i) ω - S.N (tg ε (i + 1) - P.L2) ω with hB
  set r := S.N (tg ε (i + 1) - P.L2) ω - S.N (tg ε i - P.L2) ω with hr
  have hc0 : 0 ≤ c := by omega
  have hB0 : 0 ≤ B := by omega
  have hr0 : 0 ≤ r := by omega
  have hcc : 0 ≤ c * (c - 1) := by
    rcases (show c = 0 ∨ 1 ≤ c by omega) with h | h
    · rw [h]; norm_num
    · exact mul_nonneg hc0 (by omega)
  have hcB : 0 ≤ c * B := mul_nonneg hc0 hB0
  have hrB : 0 ≤ r * B := mul_nonneg hr0 hB0
  have hI : 0 ≤ Sb * (if 2 ≤ r then 1 else 0) := by
    split_ifs <;> simp [hSb]
  by_cases hjump : uu S Sb ε i ω < uu S Sb ε (i + 1) ω
  · rw [if_pos hjump]
    have hu := uu_succ (S := S) (Sb := Sb) (ε := ε) i ω
    by_cases hcond : Sb + uu S Sb ε i ω - S.N (tg ε (i + 1)) ω < 0
    · rw [if_pos hcond] at hu
      have key : Sb ≤ (uu S Sb ε (i + 1) ω - uu S Sb ε i ω) + c + B - 1 := by
        rw [hu]; omega
      rcases (show c = 0 ∨ 1 ≤ c by omega) with h0 | h1
      · rcases post (S := S) (Sb := Sb) (ε := ε) ω i with hA | hA
        · have hsize : uu S Sb ε (i + 1) ω - uu S Sb ε i ω = r := by rw [hu, hA, hr]
          have hrpos : 1 ≤ r := by omega
          rw [hsize] at key ⊢
          rcases (show 2 ≤ r ∨ r = 1 by omega) with hr2 | hr1
          · rw [if_pos hr2]
            nlinarith
          · rw [if_neg (by omega), hr1]
            rw [h0] at key
            nlinarith
        · exfalso
          omega
      · have e1 : c - 1 ≤ c * (c - 1) := by nlinarith
        have e2 : B ≤ c * B := by nlinarith
        nlinarith
    · rw [if_neg hcond] at hu
      omega
  · rw [if_neg hjump]
    nlinarith

end PathFacts

section ShiftIntegral

lemma integral_shift_le {f : ℝ → ℝ} (hf : Monotone f) {a b L : ℝ} (hab : a ≤ b) (hL : 0 ≤ L) :
    ∫ t in a..b, (f t - f (t - L)) ≤ L * (f b - f (a - L)) := by
  have hf' : Monotone (fun t => f (t - L)) := fun x y h => hf (by linarith)
  have i1 : ∀ x y : ℝ, IntervalIntegrable f MeasureTheory.volume x y :=
    fun x y => hf.intervalIntegrable
  have i2 : ∀ x y : ℝ, IntervalIntegrable (fun t => f (t - L)) MeasureTheory.volume x y :=
    fun x y => hf'.intervalIntegrable
  rw [intervalIntegral.integral_sub (i1 a b) (i2 a b), intervalIntegral.integral_comp_sub_right f L]
  have e1 := intervalIntegral.integral_add_adjacent_intervals (i1 (a - L) (b - L)) (i1 (b - L) b)
  have e2 := intervalIntegral.integral_add_adjacent_intervals (i1 (a - L) a) (i1 a b)
  have h3 : ∫ t in (b - L)..b, f t ≤ L * f b := by
    have := intervalIntegral.integral_mono_on (show b - L ≤ b by linarith) (i1 _ _)
      (intervalIntegrable_const (c := f b)) (fun x hx => hf hx.2)
    simpa [intervalIntegral.integral_const] using this
  have h4 : L * f (a - L) ≤ ∫ t in (a - L)..a, f t := by
    have := intervalIntegral.integral_mono_on (show a - L ≤ a by linarith)
      (intervalIntegrable_const (c := f (a - L))) (i1 _ _) (fun x hx => hf hx.1)
    simpa [intervalIntegral.integral_const] using this
  linarith

lemma lintegral_shift_le {f : ℝ → ℝ} (hf : Monotone f) {a b L : ℝ} (hab : a ≤ b) (hL : 0 ≤ L) :
    ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (f t - f (t - L))
      ≤ ENNReal.ofReal (L * (f b - f (a - L))) := by
  have hf' : Monotone (fun t => f (t - L)) := fun x y h => hf (by linarith)
  have hint : IntervalIntegrable (fun t => f t - f (t - L)) MeasureTheory.volume a b :=
    hf.intervalIntegrable.sub hf'.intervalIntegrable
  have hint' : IntegrableOn (fun t => f t - f (t - L)) (Set.Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hint
  rw [← ofReal_integral_eq_lintegral_ofReal hint'
    (ae_of_all _ (fun t => sub_nonneg.mpr (hf (by linarith))))]
  rw [← intervalIntegral.integral_of_le hab]
  exact ENNReal.ofReal_le_ofReal (integral_shift_le hf hab hL)

end ShiftIntegral

end Imp

end TwoStageRnQ

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace Imp

section PoisFacts

lemma hasSum_poisW_fact2 (μ : ℝ) :
    HasSum (fun n : ℕ => poisW μ n * ((n : ℝ) * ((n : ℝ) - 1))) (μ ^ 2) := by
  have e : ∀ n : ℕ, poisW μ (n + 2) * (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1))
      = μ ^ 2 * poisW μ n := by
    intro n
    have h1 := poisW_succ_mul μ (n + 1)
    have h2 := poisW_succ_mul μ n
    have e1 : (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1))
        = ((n + 1 + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e1, show n + 2 = n + 1 + 1 by ring]
    calc poisW μ (n + 1 + 1) * (((n + 1 + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ))
        = (poisW μ (n + 1 + 1) * ((n + 1 + 1 : ℕ) : ℝ)) * ((n + 1 : ℕ) : ℝ) := by ring
      _ = μ * (poisW μ (n + 1) * ((n + 1 : ℕ) : ℝ)) := by rw [h1]; ring
      _ = μ ^ 2 * poisW μ n := by rw [h2]; ring
  have h2 : HasSum (fun n : ℕ => (fun n : ℕ => poisW μ n * ((n : ℝ) * ((n : ℝ) - 1))) (n + 2))
      (μ ^ 2 - ∑ i ∈ Finset.range 2, (fun n : ℕ => poisW μ n * ((n : ℝ) * ((n : ℝ) - 1))) i) := by
    have hz : ∑ i ∈ Finset.range 2, (fun n : ℕ => poisW μ n * ((n : ℝ) * ((n : ℝ) - 1))) i = 0 := by
      simp [Finset.sum_range_succ]
    rw [hz, sub_zero]
    have := (hasSum_poisW μ).mul_left (μ ^ 2)
    rw [mul_one] at this
    have hfun : (fun n : ℕ => (fun n : ℕ => poisW μ n * ((n : ℝ) * ((n : ℝ) - 1))) (n + 2))
        = (fun i : ℕ => μ ^ 2 * poisW μ i) := funext e
    rw [hfun]
    exact this
  exact (hasSum_nat_add_iff' 2).mp h2

lemma fact2_nonneg (d : ℕ) : 0 ≤ (d : ℝ) * ((d : ℝ) - 1) := by
  rcases Nat.eq_zero_or_pos d with h | h
  · simp [h]
  · have : (1 : ℝ) ≤ d := by exact_mod_cast h
    nlinarith

lemma tsum_pois_fact2 {μ : ℝ} (hμ : 0 ≤ μ) :
    ∑' d : ℕ, ENNReal.ofReal (poisW μ d) * ENNReal.ofReal ((d : ℝ) * ((d : ℝ) - 1))
      = ENNReal.ofReal (μ ^ 2) := by
  rw [← (hasSum_poisW_fact2 μ).tsum_eq, ENNReal.ofReal_tsum_of_nonneg
    (fun d => mul_nonneg (poisW_nonneg hμ d) (fact2_nonneg d)) (hasSum_poisW_fact2 μ).summable]
  refine tsum_congr (fun d => ?_)
  rw [ENNReal.ofReal_mul (poisW_nonneg hμ d)]

lemma poisW_succ_le {μ : ℝ} (hμ : 0 ≤ μ) (m : ℕ) : poisW μ (m + 1) ≤ μ * poisW μ m := by
  have h := poisW_succ_mul μ m
  have hp := poisW_nonneg hμ (m + 1)
  have h1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  nlinarith

lemma poisW_add_le {μ : ℝ} (hμ : 0 ≤ μ) (n : ℕ) : ∀ k : ℕ, poisW μ (k + n) ≤ μ ^ k * poisW μ n
  | 0 => by simp
  | k + 1 => by
    have h1 := poisW_succ_le hμ (k + n)
    have h2 := poisW_add_le hμ n k
    rw [show k + 1 + n = (k + n) + 1 by ring, pow_succ]
    calc poisW μ (k + n + 1) ≤ μ * poisW μ (k + n) := h1
      _ ≤ μ * (μ ^ k * poisW μ n) := mul_le_mul_of_nonneg_left h2 hμ
      _ = μ ^ k * μ * poisW μ n := by ring

lemma tsum_tail_le {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ < 1) (n : ℕ) :
    ∑' d : ℕ, poisW μ d * max ((d : ℝ) - n) 0 ≤ poisW μ n * (μ / (1 - μ) ^ 2) := by
  set f : ℕ → ℝ := fun d => poisW μ d * max ((d : ℝ) - n) 0 with hf
  have hf0 : ∀ d, 0 ≤ f d := fun d => mul_nonneg (poisW_nonneg hμ d) (le_max_right _ _)
  have hfs : Summable f := by
    refine Summable.of_nonneg_of_le hf0 (fun d => ?_) (summable_poisW_mul_nat μ)
    exact mul_le_mul_of_nonneg_left (max_le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      (Nat.cast_nonneg d)) (poisW_nonneg hμ d)
  rw [← hfs.sum_add_tsum_nat_add n]
  have hz : ∑ i ∈ Finset.range n, f i = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have : (i : ℝ) < n := by exact_mod_cast Finset.mem_range.mp hi
    simp only [hf]
    rw [max_eq_right (by linarith), mul_zero]
  rw [hz, zero_add]
  have hgeo := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := μ)
    (by rw [Real.norm_eq_abs, abs_of_nonneg hμ]; exact hμ1)
  have e : ∀ k : ℕ, f (k + n) = poisW μ (k + n) * (k : ℝ) := by
    intro k
    simp only [hf]
    push_cast
    rw [show (k : ℝ) + n - n = k by ring, max_eq_left (Nat.cast_nonneg k)]
  have hle : ∀ k : ℕ, f (k + n) ≤ poisW μ n * ((k : ℝ) * μ ^ k) := by
    intro k
    rw [e k]
    have := poisW_add_le hμ n k
    calc poisW μ (k + n) * (k : ℝ) ≤ μ ^ k * poisW μ n * (k : ℝ) :=
          mul_le_mul_of_nonneg_right this (Nat.cast_nonneg k)
      _ = poisW μ n * ((k : ℝ) * μ ^ k) := by ring
  have hs2 : Summable (fun k : ℕ => poisW μ n * ((k : ℝ) * μ ^ k)) := hgeo.summable.mul_left _
  calc ∑' k : ℕ, f (k + n) ≤ ∑' k : ℕ, poisW μ n * ((k : ℝ) * μ ^ k) :=
        Summable.tsum_le_tsum hle ((summable_nat_add_iff n).mpr hfs) hs2
    _ = poisW μ n * (μ / (1 - μ) ^ 2) := by rw [tsum_mul_left, hgeo.tsum_eq]

lemma phi_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {z : ℝ} (hz : 0 ≤ z) {d : ℝ} (hd : 0 ≤ d) :
    phi a b (z - d) ≤ a * z + b * max (d - z) 0 := by
  rw [phi_eq_max ha hb]
  have m1 := le_max_left (d - z) 0
  have m2 := le_max_right (d - z) 0
  apply max_le
  · nlinarith
  · nlinarith

end PoisFacts

section Expect

variable {P : Params} (S : DemandSpace P)

lemma lintegral_fn_incr {v t : ℝ} (h : v ≤ t) (g : ℕ → ℝ≥0∞) :
    ∫⁻ ω, g (S.N t ω - S.N v ω).toNat ∂S.ν
      = ∑' d : ℕ, ENNReal.ofReal (poisW (P.lam * (t - v)) d) * g d := by
  have hYm : Measurable (fun ω => (S.N t ω - S.N v ω).toNat) :=
    (measurable_of_countable (fun z : ℤ => z.toNat)).comp ((S.N_meas t).sub (S.N_meas v))
  refine (S.lintegral_comp' hYm g).trans (tsum_congr (fun k => ?_))
  have : (fun ω => (S.N t ω - S.N v ω).toNat) ⁻¹' {k} = {ω | S.N t ω - S.N v ω = (k : ℤ)} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · intro hk; rw [← hk, Int.toNat_of_nonneg (S.incr_nonneg h ω)]
    · intro hk; rw [hk]; simp
  rw [this, S.N_law v t h k]

lemma toNat_cast_eq {v t : ℝ} (h : v ≤ t) (ω : S.Ω) :
    (((S.N t ω - S.N v ω).toNat : ℕ) : ℝ) = ((S.N t ω - S.N v ω : ℤ) : ℝ) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (S.incr_nonneg h ω)]

lemma lintegral_fact2 {v t : ℝ} (h : v ≤ t) :
    ∫⁻ ω, ENNReal.ofReal (((S.N t ω - S.N v ω : ℤ) : ℝ) * (((S.N t ω - S.N v ω : ℤ) : ℝ) - 1)) ∂S.ν
      = ENNReal.ofReal ((P.lam * (t - v)) ^ 2) := by
  have e : ∀ ω, ENNReal.ofReal (((S.N t ω - S.N v ω : ℤ) : ℝ) * (((S.N t ω - S.N v ω : ℤ) : ℝ) - 1))
      = (fun d : ℕ => ENNReal.ofReal ((d : ℝ) * ((d : ℝ) - 1))) (S.N t ω - S.N v ω).toNat := by
    intro ω
    simp only
    rw [toNat_cast_eq S h ω]
  rw [lintegral_congr e, lintegral_fn_incr S h (fun d : ℕ => ENNReal.ofReal ((d : ℝ) * ((d : ℝ) - 1)))]
  exact tsum_pois_fact2 (mul_nonneg P.lam_nonneg (by linarith))

lemma lintegral_sq_incr {v t : ℝ} (h : v ≤ t) :
    ∫⁻ ω, ENNReal.ofReal (((S.N t ω - S.N v ω : ℤ) : ℝ) ^ 2) ∂S.ν
      = ENNReal.ofReal ((P.lam * (t - v)) ^ 2 + P.lam * (t - v)) := by
  have hμ : 0 ≤ P.lam * (t - v) := mul_nonneg P.lam_nonneg (by linarith)
  have e : ∀ ω, ENNReal.ofReal (((S.N t ω - S.N v ω : ℤ) : ℝ) ^ 2)
      = ENNReal.ofReal (((S.N t ω - S.N v ω : ℤ) : ℝ) * (((S.N t ω - S.N v ω : ℤ) : ℝ) - 1))
        + ENNReal.ofReal (((S.N t ω - S.N v ω : ℤ) : ℝ)) := by
    intro ω
    have hx : (0 : ℝ) ≤ ((S.N t ω - S.N v ω : ℤ) : ℝ) := by exact_mod_cast S.incr_nonneg h ω
    have hf := toNat_cast_eq S h ω
    have hnn := fact2_nonneg (S.N t ω - S.N v ω).toNat
    rw [hf] at hnn
    rw [← ENNReal.ofReal_add hnn hx]
    congr 1
    ring
  have hm1 : Measurable (fun ω => ENNReal.ofReal
      (((S.N t ω - S.N v ω : ℤ) : ℝ) * (((S.N t ω - S.N v ω : ℤ) : ℝ) - 1))) :=
    (measurable_of_countable (fun z : ℤ => ENNReal.ofReal ((z : ℝ) * ((z : ℝ) - 1)))).comp
      ((S.N_meas t).sub (S.N_meas v))
  rw [lintegral_congr e, lintegral_add_left hm1, lintegral_fact2 S h, S.lintegral_incr_val h,
    ← ENNReal.ofReal_add (sq_nonneg _) hμ]

lemma lintegral_phi_incr_le {v t : ℝ} (h : v ≤ t) (n : ℕ) (hμ1 : P.lam * (t - v) < 1) :
    ∫⁻ ω, ENNReal.ofReal (phi P.h2 P.p ((((n : ℤ) - (S.N t ω - S.N v ω) : ℤ) : ℝ))) ∂S.ν
      ≤ ENNReal.ofReal (P.h2 * n + P.p * (poisW (P.lam * (t - v)) n
          * (P.lam * (t - v) / (1 - P.lam * (t - v)) ^ 2))) := by
  set μ := P.lam * (t - v) with hμdef
  have hμ : 0 ≤ μ := mul_nonneg P.lam_nonneg (by linarith)
  have e : ∀ ω, ENNReal.ofReal (phi P.h2 P.p ((((n : ℤ) - (S.N t ω - S.N v ω) : ℤ) : ℝ)))
      = (fun d : ℕ => ENNReal.ofReal (phi P.h2 P.p ((n : ℝ) - d))) (S.N t ω - S.N v ω).toNat := by
    intro ω
    simp only
    rw [toNat_cast_eq S h ω]
    push_cast
    ring_nf
  rw [lintegral_congr e, lintegral_fn_incr S h (fun d : ℕ => ENNReal.ofReal (phi P.h2 P.p ((n : ℝ) - d)))]
  have hb : ∀ d : ℕ, ENNReal.ofReal (poisW μ d) * ENNReal.ofReal (phi P.h2 P.p ((n : ℝ) - d))
      ≤ ENNReal.ofReal (poisW μ d * (P.h2 * n))
        + ENNReal.ofReal P.p * ENNReal.ofReal (poisW μ d * max ((d : ℝ) - n) 0) := by
    intro d
    have hp := poisW_nonneg hμ d
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [← ENNReal.ofReal_mul hp, ← ENNReal.ofReal_mul P.p_nonneg,
      ← ENNReal.ofReal_add (mul_nonneg hp (mul_nonneg P.h2_nonneg hn))
        (mul_nonneg P.p_nonneg (mul_nonneg hp (le_max_right _ _)))]
    apply ENNReal.ofReal_le_ofReal
    have := phi_sub_le P.h2_nonneg P.p_nonneg hn (Nat.cast_nonneg d)
    have e2 : poisW μ d * (P.h2 * n) + P.p * (poisW μ d * max ((d : ℝ) - n) 0)
        = poisW μ d * (P.h2 * n + P.p * max ((d : ℝ) - n) 0) := by ring
    rw [e2]
    exact mul_le_mul_of_nonneg_left this hp
  have hs1 : Summable (fun d : ℕ => poisW μ d * (P.h2 * n)) := (summable_poisW μ).mul_right _
  have hsum1 : ∑' d : ℕ, ENNReal.ofReal (poisW μ d * (P.h2 * n)) = ENNReal.ofReal (P.h2 * n) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun d => mul_nonneg (poisW_nonneg hμ d) (mul_nonneg P.h2_nonneg (Nat.cast_nonneg n))) hs1,
      tsum_mul_right, tsum_poisW, one_mul]
  have hs2 : Summable (fun d : ℕ => poisW μ d * max ((d : ℝ) - n) 0) := by
    refine Summable.of_nonneg_of_le (fun d => mul_nonneg (poisW_nonneg hμ d) (le_max_right _ _))
      (fun d => ?_) (summable_poisW_mul_nat μ)
    exact mul_le_mul_of_nonneg_left (max_le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      (Nat.cast_nonneg d)) (poisW_nonneg hμ d)
  calc ∑' d : ℕ, ENNReal.ofReal (poisW μ d) * ENNReal.ofReal (phi P.h2 P.p ((n : ℝ) - d))
      ≤ ∑' d : ℕ, (ENNReal.ofReal (poisW μ d * (P.h2 * n))
          + ENNReal.ofReal P.p * ENNReal.ofReal (poisW μ d * max ((d : ℝ) - n) 0)) :=
        ENNReal.tsum_le_tsum hb
    _ = ENNReal.ofReal (P.h2 * n)
          + ENNReal.ofReal P.p * ENNReal.ofReal (∑' d : ℕ, poisW μ d * max ((d : ℝ) - n) 0) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, hsum1, ENNReal.ofReal_tsum_of_nonneg
          (fun d => mul_nonneg (poisW_nonneg hμ d) (le_max_right _ _)) hs2]
    _ ≤ ENNReal.ofReal (P.h2 * n) + ENNReal.ofReal P.p * ENNReal.ofReal (poisW μ n * (μ / (1 - μ) ^ 2)) := by
        gcongr
        exact tsum_tail_le hμ hμ1 n
    _ = ENNReal.ofReal (P.h2 * n + P.p * (poisW μ n * (μ / (1 - μ) ^ 2))) := by
        rw [← ENNReal.ofReal_mul P.p_nonneg, ← ENNReal.ofReal_add
          (mul_nonneg P.h2_nonneg (Nat.cast_nonneg n))]
        exact mul_nonneg P.p_nonneg (mul_nonneg (poisW_nonneg hμ n)
          (div_nonneg hμ (sq_nonneg _)))

lemma lintegral_mul_incr' {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) {Y : S.Ω → ℤ}
    (hY : Measurable[S.𝓕 v] Y) :
    ∫⁻ ω, ENNReal.ofReal ((Y ω : ℝ) * ((S.N w ω - S.N v ω : ℤ) : ℝ)) ∂S.ν
      = (∫⁻ ω, ENNReal.ofReal (Y ω : ℝ) ∂S.ν) * ENNReal.ofReal (P.lam * (w - v)) := by
  have e : ∀ ω, ENNReal.ofReal ((Y ω : ℝ) * ((S.N w ω - S.N v ω : ℤ) : ℝ))
      = (fun y : ℤ => ENNReal.ofReal (y : ℝ)) (Y ω) * ENNReal.ofReal ((S.N w ω - S.N v ω : ℤ) : ℝ) := by
    intro ω
    simp only
    rcases le_total 0 (Y ω : ℝ) with hy | hy
    · rw [ENNReal.ofReal_mul hy]
    · have h0 : (0 : ℝ) ≤ ((S.N w ω - S.N v ω : ℤ) : ℝ) := by exact_mod_cast S.incr_nonneg hvw ω
      rw [ENNReal.ofReal_of_nonpos hy, zero_mul, ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hy h0)]
  rw [lintegral_congr e, LBP.lintegral_mul_incr hv hvw hY (fun y : ℤ => ENNReal.ofReal (y : ℝ))]

end Expect

end Imp

end TwoStageRnQ

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace Imp

open TwoStageRnQ.LB

section Cost

variable {P : Params} {S : DemandSpace P} {Sb : ℤ} {ε : ℝ}

lemma Dg_le (hε : 0 < ε) {t : ℝ} (ht : 0 ≤ t) (ω : S.Ω) :
    Dg (S := S) (ε := ε) t ω ≤ (S.N (t + ε) ω - S.N (t - ε) ω)
      + (S.N (t + ε - P.L2) ω - S.N (t - ε - P.L2) ω) := by
  unfold Dg
  have h1 := tg_floor_le hε ht
  have h2 := lt_tg_floor hε t
  rw [tg_succ] at h2 ⊢
  have m1 : S.N (tg ε ⌊t / ε⌋₊ + ε) ω ≤ S.N (t + ε) ω := S.N_mono ω (by linarith)
  have m2 : S.N (t - ε) ω ≤ S.N (tg ε ⌊t / ε⌋₊) ω := S.N_mono ω (by linarith)
  have m3 : S.N (tg ε ⌊t / ε⌋₊ + ε - P.L2) ω ≤ S.N (t + ε - P.L2) ω := S.N_mono ω (by linarith)
  have m4 : S.N (t - ε - P.L2) ω ≤ S.N (tg ε ⌊t / ε⌋₊ - P.L2) ω := S.N_mono ω (by linarith)
  linarith

def Gn (S : DemandSpace P) (Sb : ℤ) (ε : ℝ) (ω : S.Ω) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (phi P.h2 P.p ((Sb + S.N (t - P.L2) ω - S.N t ω : ℤ) : ℝ))
    + ENNReal.ofReal (P.h1 * Sb)
    + ENNReal.ofReal (P.h2 + P.p) * ENNReal.ofReal ((S.N (t + ε) ω - S.N (t - ε) ω : ℤ) : ℝ)
    + ENNReal.ofReal (P.h2 + P.p)
      * ENNReal.ofReal ((S.N (t + ε - P.L2) ω - S.N (t - ε - P.L2) ω : ℤ) : ℝ)

lemma cI_le_ennreal (hε : 0 < ε) (hSb : 0 ≤ Sb) {t : ℝ} (ht : 0 ≤ t) (ω : S.Ω) :
    ENNReal.ofReal ((pol (S := S) (Sb := Sb) hε).cI t ω)
      ≤ Gn S Sb ε ω t + ENNReal.ofReal (P.h2 + P.p)
          * ENNReal.ofReal ((U1c S Sb ε t ω : ℝ) - (U1c S Sb ε (t - P.L1) ω : ℝ)) := by
  have hc := cI_le (S := S) (Sb := Sb) hε hSb ht ω
  have hD := Dg_le (S := S) hε ht ω
  have hab : 0 ≤ P.h2 + P.p := add_nonneg P.h2_nonneg P.p_nonneg
  have n1 : 0 ≤ phi P.h2 P.p ((Sb + S.N (t - P.L2) ω - S.N t ω : ℤ) : ℝ) :=
    phi_nonneg P.h2_nonneg P.p_nonneg _
  have n2 : 0 ≤ P.h1 * (Sb : ℝ) := mul_nonneg P.h1_nonneg (by exact_mod_cast hSb)
  have i3 : (0 : ℝ) ≤ ((S.N (t + ε) ω - S.N (t - ε) ω : ℤ) : ℝ) := by
    exact_mod_cast S.incr_nonneg (by linarith) ω
  have i4 : (0 : ℝ) ≤ ((S.N (t + ε - P.L2) ω - S.N (t - ε - P.L2) ω : ℤ) : ℝ) := by
    exact_mod_cast S.incr_nonneg (by linarith) ω
  have i5 : (0 : ℝ) ≤ (U1c S Sb ε t ω : ℝ) - (U1c S Sb ε (t - P.L1) ω : ℝ) := by
    have h := U1c_mono (S := S) (Sb := Sb) hε ω (show t - P.L1 ≤ t by linarith [P.L1_nonneg])
    simp only at h
    have : ((U1c S Sb ε (t - P.L1) ω : ℤ) : ℝ) ≤ ((U1c S Sb ε t ω : ℤ) : ℝ) := by exact_mod_cast h
    linarith
  have hDr : ((Dg (S := S) (ε := ε) t ω : ℤ) : ℝ) ≤ ((S.N (t + ε) ω - S.N (t - ε) ω : ℤ) : ℝ)
      + ((S.N (t + ε - P.L2) ω - S.N (t - ε - P.L2) ω : ℤ) : ℝ) := by
    exact_mod_cast hD
  have hq : ((U1c S Sb ε t ω - U1c S Sb ε (t - P.L1) ω : ℤ) : ℝ)
      = (U1c S Sb ε t ω : ℝ) - (U1c S Sb ε (t - P.L1) ω : ℝ) := by push_cast; ring
  rw [hq] at hc
  unfold Gn
  rw [← ENNReal.ofReal_mul hab, ← ENNReal.ofReal_mul hab, ← ENNReal.ofReal_mul hab,
    ← ENNReal.ofReal_add n1 n2, ← ENNReal.ofReal_add (add_nonneg n1 n2) (mul_nonneg hab i3),
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg n1 n2) (mul_nonneg hab i3)) (mul_nonneg hab i4),
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg (add_nonneg n1 n2) (mul_nonneg hab i3))
      (mul_nonneg hab i4)) (mul_nonneg hab i5)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith

lemma Gn_meas (S : DemandSpace P) (Sb : ℤ) (ε : ℝ) :
    Measurable (fun p : S.Ω × ℝ => Gn S Sb ε p.1 p.2) := by
  have a1 : Measurable (fun p : S.Ω × ℝ => S.N (p.2 - P.L2) p.1) := by
    have h := S.N_joint.comp (measurable_fst.prodMk (measurable_snd.sub_const P.L2)); exact h
  have a2 : Measurable (fun p : S.Ω × ℝ => S.N p.2 p.1) := S.N_joint
  have a3 : Measurable (fun p : S.Ω × ℝ => S.N (p.2 + ε) p.1) := by
    have h := S.N_joint.comp (measurable_fst.prodMk (measurable_snd.add_const ε)); exact h
  have a4 : Measurable (fun p : S.Ω × ℝ => S.N (p.2 - ε) p.1) := by
    have h := S.N_joint.comp (measurable_fst.prodMk (measurable_snd.sub_const ε)); exact h
  have a5 : Measurable (fun p : S.Ω × ℝ => S.N (p.2 + ε - P.L2) p.1) := by
    have h := S.N_joint.comp (measurable_fst.prodMk ((measurable_snd.add_const ε).sub_const P.L2))
    exact h
  have a6 : Measurable (fun p : S.Ω × ℝ => S.N (p.2 - ε - P.L2) p.1) := by
    have h := S.N_joint.comp (measurable_fst.prodMk ((measurable_snd.sub_const ε).sub_const P.L2))
    exact h
  have t1 : Measurable (fun p : S.Ω × ℝ =>
      ENNReal.ofReal (phi P.h2 P.p ((Sb + S.N (p.2 - P.L2) p.1 - S.N p.2 p.1 : ℤ) : ℝ))) := by
    have h := (measurable_of_countable (fun z : ℤ × ℤ =>
      ENNReal.ofReal (phi P.h2 P.p ((Sb + z.1 - z.2 : ℤ) : ℝ)))).comp (a1.prodMk a2)
    exact h
  have t3 : Measurable (fun p : S.Ω × ℝ => ENNReal.ofReal (P.h2 + P.p)
      * ENNReal.ofReal ((S.N (p.2 + ε) p.1 - S.N (p.2 - ε) p.1 : ℤ) : ℝ)) := by
    have h := (measurable_of_countable (fun z : ℤ × ℤ =>
      ENNReal.ofReal (P.h2 + P.p) * ENNReal.ofReal ((z.1 - z.2 : ℤ) : ℝ))).comp (a3.prodMk a4)
    exact h
  have t4 : Measurable (fun p : S.Ω × ℝ => ENNReal.ofReal (P.h2 + P.p)
      * ENNReal.ofReal ((S.N (p.2 + ε - P.L2) p.1 - S.N (p.2 - ε - P.L2) p.1 : ℤ) : ℝ)) := by
    have h := (measurable_of_countable (fun z : ℤ × ℤ =>
      ENNReal.ofReal (P.h2 + P.p) * ENNReal.ofReal ((z.1 - z.2 : ℤ) : ℝ))).comp (a5.prodMk a6)
    exact h
  have t2 : Measurable (fun _ : S.Ω × ℝ => ENNReal.ofReal (P.h1 * Sb)) := measurable_const
  have h := ((t1.add t2).add t3).add t4
  exact h

lemma lintegral_Gn_le (S : DemandSpace P) (Sb : ℤ) {ε : ℝ} (hε : 0 < ε) (hSb : 0 ≤ Sb) {Φ : ℝ}
    (hΦ : ∀ t, ∫⁻ ω, ENNReal.ofReal (phi P.h2 P.p ((Sb + S.N (t - P.L2) ω - S.N t ω : ℤ) : ℝ)) ∂S.ν
      ≤ ENNReal.ofReal Φ) (t : ℝ) :
    ∫⁻ ω, Gn S Sb ε ω t ∂S.ν
      ≤ ENNReal.ofReal Φ + ENNReal.ofReal (P.h1 * Sb + 4 * (P.h2 + P.p) * P.lam * ε) := by
  have hab : 0 ≤ P.h2 + P.p := add_nonneg P.h2_nonneg P.p_nonneg
  have m1 : Measurable (fun ω => ENNReal.ofReal (phi P.h2 P.p ((Sb + S.N (t - P.L2) ω - S.N t ω : ℤ) : ℝ))) := by
    have h := Prop1.meas_N2 S (fun z : ℤ × ℤ => ENNReal.ofReal (phi P.h2 P.p ((Sb + z.1 - z.2 : ℤ) : ℝ)))
      (t - P.L2) t
    exact h
  have m3 : Measurable (fun ω => ENNReal.ofReal ((S.N (t + ε) ω - S.N (t - ε) ω : ℤ) : ℝ)) := by
    have h := Prop1.meas_N2 S (fun z : ℤ × ℤ => ENNReal.ofReal ((z.1 - z.2 : ℤ) : ℝ)) (t + ε) (t - ε)
    exact h
  have m4 : Measurable (fun ω => ENNReal.ofReal ((S.N (t + ε - P.L2) ω - S.N (t - ε - P.L2) ω : ℤ) : ℝ)) := by
    have h := Prop1.meas_N2 S (fun z : ℤ × ℤ => ENNReal.ofReal ((z.1 - z.2 : ℤ) : ℝ))
      (t + ε - P.L2) (t - ε - P.L2)
    exact h
  have mAB : Measurable (fun ω => ENNReal.ofReal (phi P.h2 P.p ((Sb + S.N (t - P.L2) ω - S.N t ω : ℤ) : ℝ))
      + ENNReal.ofReal (P.h1 * Sb)) := by
    have h := m1.add (measurable_const (a := ENNReal.ofReal (P.h1 * Sb))); exact h
  have mABC : Measurable (fun ω => ENNReal.ofReal (phi P.h2 P.p ((Sb + S.N (t - P.L2) ω - S.N t ω : ℤ) : ℝ))
      + ENNReal.ofReal (P.h1 * Sb)
      + ENNReal.ofReal (P.h2 + P.p) * ENNReal.ofReal ((S.N (t + ε) ω - S.N (t - ε) ω : ℤ) : ℝ)) := by
    have h := mAB.add (m3.const_mul (ENNReal.ofReal (P.h2 + P.p))); exact h
  unfold Gn
  rw [lintegral_add_left mABC, lintegral_add_left mAB, lintegral_add_left m1, lintegral_const,
    measure_univ, mul_one, lintegral_const_mul _ m3, lintegral_const_mul _ m4,
    S.lintegral_incr_val (by linarith), S.lintegral_incr_val (by linarith)]
  have e1 : P.lam * (t + ε - (t - ε)) = 2 * P.lam * ε := by ring
  have e2 : P.lam * (t + ε - P.L2 - (t - ε - P.L2)) = 2 * P.lam * ε := by ring
  rw [e1, e2]
  have hle := hΦ t
  have k0 : 0 ≤ P.h1 * (Sb : ℝ) := mul_nonneg P.h1_nonneg (by exact_mod_cast hSb)
  have k1 : 0 ≤ 2 * P.lam * ε := by have := P.lam_nonneg; positivity
  rw [← ENNReal.ofReal_mul hab, add_assoc, add_assoc]
  gcongr
  rw [← ENNReal.ofReal_add (mul_nonneg hab k1) (mul_nonneg hab k1),
    ← ENNReal.ofReal_add k0 (add_nonneg (mul_nonneg hab k1) (mul_nonneg hab k1))]
  apply le_of_eq
  congr 1
  ring

theorem lintegral_cost_add_le (hε : 0 < ε) (hSb : 0 ≤ Sb) {Φ : ℝ} (hΦ0 : 0 ≤ Φ)
    (hΦ : ∀ t, ∫⁻ ω, ENNReal.ofReal (phi P.h2 P.p ((Sb + S.N (t - P.L2) ω - S.N t ω : ℤ) : ℝ)) ∂S.ν
      ≤ ENNReal.ofReal Φ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (g : S.Ω → ℝ≥0∞) :
    ∫⁻ ω, ((∫⁻ t in Set.Ioc a b, ENNReal.ofReal ((pol (S := S) (Sb := Sb) hε).cI t ω)) + g ω) ∂S.ν
      ≤ ENNReal.ofReal ((Φ + P.h1 * Sb + 4 * (P.h2 + P.p) * P.lam * ε) * (b - a)
          + (P.h2 + P.p) * (P.L1 * (Sb + P.lam * (b - a + P.L1 + ε)))) + ∫⁻ ω, g ω ∂S.ν := by
  have hhp : 0 ≤ P.h2 + P.p := add_nonneg P.h2_nonneg P.p_nonneg
  have hG := Gn_meas S Sb ε
  have hSbr : (0 : ℝ) ≤ Sb := by exact_mod_cast hSb

  have hpath : ∀ ω, ∫⁻ t in Set.Ioc a b, ENNReal.ofReal ((pol (S := S) (Sb := Sb) hε).cI t ω)
      ≤ (∫⁻ t in Set.Ioc a b, Gn S Sb ε ω t)
        + ENNReal.ofReal (P.h2 + P.p) * ENNReal.ofReal (P.L1 * ((U1c S Sb ε b ω : ℝ)
          - (U1c S Sb ε (a - P.L1) ω : ℝ))) := by
    intro ω
    have hmono : Monotone (fun t => (U1c S Sb ε t ω : ℝ)) := fun x y hxy => by
      have := U1c_mono (S := S) (Sb := Sb) hε ω hxy
      simp only at this
      show (U1c S Sb ε x ω : ℝ) ≤ (U1c S Sb ε y ω : ℝ)
      exact_mod_cast this
    have hGt : Measurable (fun t => Gn S Sb ε ω t) := by
      have h1 : Measurable (fun t : ℝ => ((ω, t) : S.Ω × ℝ)) := measurable_const.prodMk measurable_id
      have h := hG.comp h1
      exact h
    calc ∫⁻ t in Set.Ioc a b, ENNReal.ofReal ((pol (S := S) (Sb := Sb) hε).cI t ω)
        ≤ ∫⁻ t in Set.Ioc a b, (Gn S Sb ε ω t + ENNReal.ofReal (P.h2 + P.p)
            * ENNReal.ofReal ((U1c S Sb ε t ω : ℝ) - (U1c S Sb ε (t - P.L1) ω : ℝ))) :=
          setLIntegral_mono' measurableSet_Ioc (fun t ht =>
            cI_le_ennreal hε hSb (le_trans ha ht.1.le) ω)
      _ = (∫⁻ t in Set.Ioc a b, Gn S Sb ε ω t) + ENNReal.ofReal (P.h2 + P.p)
            * ∫⁻ t in Set.Ioc a b, ENNReal.ofReal ((U1c S Sb ε t ω : ℝ)
              - (U1c S Sb ε (t - P.L1) ω : ℝ)) := by
          rw [lintegral_add_left hGt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ _ := by
          gcongr
          exact lintegral_shift_le hmono hab P.L1_nonneg
  have hA : Measurable (fun ω => ∫⁻ t in Set.Ioc a b, Gn S Sb ε ω t) := by
    have h := Measurable.lintegral_prod_right' (ν := MeasureTheory.volume.restrict (Set.Ioc a b))
      (f := fun p : S.Ω × ℝ => Gn S Sb ε p.1 p.2) hG
    exact h

  have hpart1 : ∫⁻ ω, (∫⁻ t in Set.Ioc a b, Gn S Sb ε ω t) ∂S.ν
      ≤ ENNReal.ofReal ((Φ + P.h1 * Sb + 4 * (P.h2 + P.p) * P.lam * ε) * (b - a)) := by
    rw [lintegral_lintegral_swap (f := fun ω t => Gn S Sb ε ω t) hG.aemeasurable]
    calc ∫⁻ t in Set.Ioc a b, ∫⁻ ω, Gn S Sb ε ω t ∂S.ν
        ≤ ∫⁻ t in Set.Ioc a b, (ENNReal.ofReal Φ
            + ENNReal.ofReal (P.h1 * Sb + 4 * (P.h2 + P.p) * P.lam * ε)) :=
          lintegral_mono (fun t => lintegral_Gn_le S Sb hε hSb hΦ t)
      _ = _ := by
          have k0 : 0 ≤ P.h1 * (Sb : ℝ) + 4 * (P.h2 + P.p) * P.lam * ε := by
            have := P.lam_nonneg; have := P.h1_nonneg
            positivity
          rw [setLIntegral_const, Real.volume_Ioc, ← ENNReal.ofReal_add hΦ0 k0,
            ← ENNReal.ofReal_mul (add_nonneg hΦ0 k0)]
          congr 1
          ring

  have hpart2 : ∫⁻ ω, ENNReal.ofReal (P.h2 + P.p) * ENNReal.ofReal (P.L1 * ((U1c S Sb ε b ω : ℝ)
        - (U1c S Sb ε (a - P.L1) ω : ℝ))) ∂S.ν
      ≤ ENNReal.ofReal ((P.h2 + P.p) * (P.L1 * (Sb + P.lam * (b - a + P.L1 + ε)))) := by
    have hv : a - P.L1 - (ε + P.L2) ≤ b - P.L2 := by linarith [P.L1_nonneg]
    have hle : ∀ ω, ENNReal.ofReal (P.h2 + P.p) * ENNReal.ofReal (P.L1 * ((U1c S Sb ε b ω : ℝ)
        - (U1c S Sb ε (a - P.L1) ω : ℝ)))
        ≤ ENNReal.ofReal ((P.h2 + P.p) * P.L1) * (ENNReal.ofReal Sb
          + ENNReal.ofReal ((S.N (b - P.L2) ω - S.N (a - P.L1 - (ε + P.L2)) ω : ℤ) : ℝ)) := by
      intro ω
      have u1 := U1c_le (Sb := Sb) (S := S) hε (le_trans ha hab) ω
      have u2 := U1c_ge (S := S) (Sb := Sb) hε hSb (a - P.L1) ω
      have hD : (0 : ℝ) ≤ ((S.N (b - P.L2) ω - S.N (a - P.L1 - (ε + P.L2)) ω : ℤ) : ℝ) := by
        exact_mod_cast S.incr_nonneg hv ω
      rw [← ENNReal.ofReal_add hSbr hD, ← ENNReal.ofReal_mul hhp,
        ← ENNReal.ofReal_mul (mul_nonneg hhp P.L1_nonneg)]
      apply ENNReal.ofReal_le_ofReal
      have hz : (U1c S Sb ε b ω : ℝ) - (U1c S Sb ε (a - P.L1) ω : ℝ)
          ≤ (Sb : ℝ) + ((S.N (b - P.L2) ω - S.N (a - P.L1 - (ε + P.L2)) ω : ℤ) : ℝ) := by
        have h1 : ((U1c S Sb ε b ω : ℤ) : ℝ) ≤ ((S.N (b - P.L2) ω : ℤ) : ℝ) := by exact_mod_cast u1
        have h2 : ((S.N (a - P.L1 - (ε + P.L2)) ω : ℤ) : ℝ) - (Sb : ℝ)
            ≤ ((U1c S Sb ε (a - P.L1) ω : ℤ) : ℝ) := by exact_mod_cast u2
        push_cast
        linarith
      have := mul_le_mul_of_nonneg_left hz (mul_nonneg hhp P.L1_nonneg)
      nlinarith
    have hDm : Measurable (fun ω => ENNReal.ofReal
        ((S.N (b - P.L2) ω - S.N (a - P.L1 - (ε + P.L2)) ω : ℤ) : ℝ)) :=
      Prop1.meas_N2 S (fun z : ℤ × ℤ => ENNReal.ofReal ((z.1 - z.2 : ℤ) : ℝ)) _ _
    calc _ ≤ ∫⁻ ω, ENNReal.ofReal ((P.h2 + P.p) * P.L1) * (ENNReal.ofReal Sb
          + ENNReal.ofReal ((S.N (b - P.L2) ω - S.N (a - P.L1 - (ε + P.L2)) ω : ℤ) : ℝ)) ∂S.ν :=
          lintegral_mono hle
      _ = ENNReal.ofReal ((P.h2 + P.p) * P.L1) * (ENNReal.ofReal Sb
          + ENNReal.ofReal (P.lam * (b - P.L2 - (a - P.L1 - (ε + P.L2))))) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            S.lintegral_incr_val hv]
      _ = _ := by
          have k1 : 0 ≤ P.lam * (b - P.L2 - (a - P.L1 - (ε + P.L2))) :=
            mul_nonneg P.lam_nonneg (by linarith)
          rw [← ENNReal.ofReal_add hSbr k1, ← ENNReal.ofReal_mul (mul_nonneg hhp P.L1_nonneg)]
          congr 1
          ring
  have hk1 : 0 ≤ (Φ + P.h1 * Sb + 4 * (P.h2 + P.p) * P.lam * ε) * (b - a) := by
    have := P.lam_nonneg; have := P.h1_nonneg
    have : 0 ≤ b - a := by linarith
    positivity
  have hk2 : 0 ≤ (P.h2 + P.p) * (P.L1 * (Sb + P.lam * (b - a + P.L1 + ε))) := by
    have := P.lam_nonneg; have := P.L1_nonneg
    have : 0 ≤ b - a := by linarith
    positivity
  have hB : Measurable (fun ω => ENNReal.ofReal (P.h2 + P.p) * ENNReal.ofReal (P.L1
      * ((U1c S Sb ε b ω : ℝ) - (U1c S Sb ε (a - P.L1) ω : ℝ)))) := by
    have h := (measurable_of_countable (fun z : ℤ × ℤ => ENNReal.ofReal (P.h2 + P.p)
      * ENNReal.ofReal (P.L1 * ((z.1 : ℝ) - (z.2 : ℝ))))).comp
      (((U1c_adapted (S := S) (Sb := Sb) hε b).mono (S.𝓕.le b) le_rfl).prodMk
        ((U1c_adapted (S := S) (Sb := Sb) hε (a - P.L1)).mono (S.𝓕.le _) le_rfl))
    exact h
  have hAB : Measurable (fun ω => (∫⁻ t in Set.Ioc a b, Gn S Sb ε ω t)
      + ENNReal.ofReal (P.h2 + P.p) * ENNReal.ofReal (P.L1
        * ((U1c S Sb ε b ω : ℝ) - (U1c S Sb ε (a - P.L1) ω : ℝ)))) := by
    have h := hA.add hB; exact h
  calc ∫⁻ ω, ((∫⁻ t in Set.Ioc a b, ENNReal.ofReal ((pol (S := S) (Sb := Sb) hε).cI t ω)) + g ω) ∂S.ν
      ≤ ∫⁻ ω, (((∫⁻ t in Set.Ioc a b, Gn S Sb ε ω t)
          + ENNReal.ofReal (P.h2 + P.p) * ENNReal.ofReal (P.L1 * ((U1c S Sb ε b ω : ℝ)
            - (U1c S Sb ε (a - P.L1) ω : ℝ)))) + g ω) ∂S.ν :=
        lintegral_mono (fun ω => add_le_add (hpath ω) le_rfl)
    _ = ∫⁻ ω, (∫⁻ t in Set.Ioc a b, Gn S Sb ε ω t) ∂S.ν
          + ∫⁻ ω, ENNReal.ofReal (P.h2 + P.p) * ENNReal.ofReal (P.L1 * ((U1c S Sb ε b ω : ℝ)
            - (U1c S Sb ε (a - P.L1) ω : ℝ))) ∂S.ν + ∫⁻ ω, g ω ∂S.ν := by
        rw [lintegral_add_left hAB, lintegral_add_left hA]
    _ ≤ ENNReal.ofReal ((Φ + P.h1 * Sb + 4 * (P.h2 + P.p) * P.lam * ε) * (b - a))
          + ENNReal.ofReal ((P.h2 + P.p) * (P.L1 * (Sb + P.lam * (b - a + P.L1 + ε))))
          + ∫⁻ ω, g ω ∂S.ν :=
        add_le_add (add_le_add hpart1 hpart2) le_rfl
    _ = _ := by rw [(ENNReal.ofReal_add hk1 hk2).symm]

theorem lintegral_cost_le (hε : 0 < ε) (hSb : 0 ≤ Sb) {Φ : ℝ} (hΦ0 : 0 ≤ Φ)
    (hΦ : ∀ t, ∫⁻ ω, ENNReal.ofReal (phi P.h2 P.p ((Sb + S.N (t - P.L2) ω - S.N t ω : ℤ) : ℝ)) ∂S.ν
      ≤ ENNReal.ofReal Φ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫⁻ ω, (∫⁻ t in Set.Ioc a b, ENNReal.ofReal ((pol (S := S) (Sb := Sb) hε).cI t ω)) ∂S.ν
      ≤ ENNReal.ofReal ((Φ + P.h1 * Sb + 4 * (P.h2 + P.p) * P.lam * ε) * (b - a)
          + (P.h2 + P.p) * (P.L1 * (Sb + P.lam * (b - a + P.L1 + ε)))) := by
  have h := lintegral_cost_add_le (S := S) hε hSb hΦ0 hΦ ha hab (fun _ => 0)
  simp only [add_zero, lintegral_const, zero_mul] at h
  exact h

end Cost

end Imp

end TwoStageRnQ

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace Imp

open TwoStageRnQ.LB

section Setup

variable {P : Params} (S : DemandSpace P) (Sb : ℤ) (ε : ℝ)

def cc (i : ℕ) (ω : S.Ω) : ℤ := S.N (tg ε (i + 1)) ω - S.N (tg ε i) ω

def bb (i : ℕ) (ω : S.Ω) : ℤ := S.N (tg ε i) ω - S.N (tg ε (i + 1) - P.L2) ω

def rr (i : ℕ) (ω : S.Ω) : ℤ := S.N (tg ε (i + 1) - P.L2) ω - S.N (tg ε i - P.L2) ω

def hreal (i : ℕ) (ω : S.Ω) : ℝ :=
  (cc S ε i ω : ℝ) * ((cc S ε i ω : ℝ) - 1) + (bb S ε i ω : ℝ) * (cc S ε i ω : ℝ)
    + (Sb : ℝ) * (if 2 ≤ rr S ε i ω then 1 else 0) + (rr S ε i ω : ℝ) * (bb S ε i ω : ℝ)

variable {S Sb ε}

lemma cc_nonneg (hε : 0 < ε) (i : ℕ) (ω : S.Ω) : 0 ≤ cc S ε i ω := by
  unfold cc
  exact S.incr_nonneg (by rw [tg_succ]; linarith) ω

lemma bb_nonneg (hεL : ε ≤ P.L2) (i : ℕ) (ω : S.Ω) : 0 ≤ bb S ε i ω := by
  unfold bb
  exact S.incr_nonneg (by rw [tg_succ]; linarith) ω

lemma rr_nonneg (hε : 0 < ε) (i : ℕ) (ω : S.Ω) : 0 ≤ rr S ε i ω := by
  unfold rr
  exact S.incr_nonneg (by rw [tg_succ]; linarith) ω

lemma hreal_nonneg (hε : 0 < ε) (hεL : ε ≤ P.L2) (hSb : 0 ≤ Sb) (i : ℕ) (ω : S.Ω) :
    0 ≤ hreal S Sb ε i ω := by
  unfold hreal
  have h1 : (0 : ℝ) ≤ cc S ε i ω := by exact_mod_cast cc_nonneg hε i ω
  have h2 : (0 : ℝ) ≤ bb S ε i ω := by exact_mod_cast bb_nonneg hεL i ω
  have h3 : (0 : ℝ) ≤ rr S ε i ω := by exact_mod_cast rr_nonneg hε i ω
  have hS : (0 : ℝ) ≤ Sb := by exact_mod_cast hSb
  have h4 : (0 : ℝ) ≤ (cc S ε i ω : ℝ) * ((cc S ε i ω : ℝ) - 1) := by
    have := fact2_nonneg (cc S ε i ω).toNat
    rwa [← Int.cast_natCast, Int.toNat_of_nonneg (cc_nonneg hε i ω)] at this
  have h5 : (0 : ℝ) ≤ (Sb : ℝ) * (if 2 ≤ rr S ε i ω then 1 else 0) := by
    split_ifs <;> simp [hS]
  have := mul_nonneg h2 h1
  have := mul_nonneg h3 h2
  linarith

lemma jump_ineq_real (hε : 0 < ε) (hεL : ε ≤ P.L2) (hSb : 0 ≤ Sb) (i : ℕ) (ω : S.Ω) :
    (Sb : ℝ) * (if uu S Sb ε i ω < uu S Sb ε (i + 1) ω then 1 else 0)
      ≤ ((uu S Sb ε (i + 1) ω - uu S Sb ε i ω : ℤ) : ℝ) + hreal S Sb ε i ω := by
  have h := jump_ineq (S := S) hε hεL hSb i ω
  have h' := (Int.cast_le (R := ℝ)).mpr h
  unfold hreal cc bb rr
  push_cast at h' ⊢
  split_ifs at h' ⊢ <;> linarith

lemma jumpCount_U1c_le' (hε : 0 < ε) (ω : S.Ω) (T : ℝ) :
    jumpCount (fun t => U1c S Sb ε t ω) T
      ≤ ((Finset.range ⌊T / ε⌋₊).filter
          (fun i => uu S Sb ε i ω < uu S Sb ε (i + 1) ω)).card := by
  refine (jumpCount_U1c_le (Sb := Sb) hε ω T).trans (le_of_eq ?_)
  refine Finset.card_bij (fun j _ => j - 1) ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hj ⊢
    refine ⟨by omega, ?_⟩
    rw [show j - 1 + 1 = j by omega]
    exact hj.2
  · intro j1 hj1 j2 hj2 he
    simp only [Finset.mem_filter, Finset.mem_Icc] at hj1 hj2
    omega
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    refine ⟨i + 1, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [show i + 1 - 1 = i by omega]
    exact hi.2

lemma jumps_path (hε : 0 < ε) (hεL : ε ≤ P.L2) (hSb : 0 ≤ Sb) (i0 K : ℕ) (ω : S.Ω) :
    (Sb : ℝ) * ((Finset.range K).filter (fun i => uu S Sb ε i ω < uu S Sb ε (i + 1) ω)).card
      ≤ ((uu S Sb ε K ω - uu S Sb ε 0 ω : ℤ) : ℝ)
        + ∑ i ∈ Finset.range K, (if i < i0 then (Sb : ℝ) else hreal S Sb ε i ω) := by
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  have htel : ((uu S Sb ε K ω - uu S Sb ε 0 ω : ℤ) : ℝ)
      = ∑ i ∈ Finset.range K, ((uu S Sb ε (i + 1) ω - uu S Sb ε i ω : ℤ) : ℝ) := by
    push_cast
    exact (Finset.sum_range_sub (fun i => ((uu S Sb ε i ω : ℤ) : ℝ)) K).symm
  rw [htel, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hS : (0 : ℝ) ≤ Sb := by exact_mod_cast hSb
  have hsz : (0 : ℝ) ≤ ((uu S Sb ε (i + 1) ω - uu S Sb ε i ω : ℤ) : ℝ) := by
    have := uu_le_succ (S := S) (Sb := Sb) hε.le ω i
    exact_mod_cast (by omega : (0 : ℤ) ≤ uu S Sb ε (i + 1) ω - uu S Sb ε i ω)
  have hj := jump_ineq_real (S := S) hε hεL hSb i ω
  have hh := hreal_nonneg (S := S) (Sb := Sb) hε hεL hSb i ω
  push_cast at hsz hj ⊢
  split_ifs at hj ⊢ <;> linarith

end Setup

section SetupExp

variable {P : Params} {S : DemandSpace P} {Sb : ℤ} {ε : ℝ}

lemma hreal_meas (i : ℕ) : Measurable (fun ω => ENNReal.ofReal (hreal S Sb ε i ω)) := by
  have h := (measurable_of_countable (fun z : ℤ × ℤ × ℤ × ℤ => ENNReal.ofReal
      (((z.1 - z.2.1 : ℤ) : ℝ) * (((z.1 - z.2.1 : ℤ) : ℝ) - 1)
        + ((z.2.1 - z.2.2.1 : ℤ) : ℝ) * ((z.1 - z.2.1 : ℤ) : ℝ)
        + (Sb : ℝ) * (if 2 ≤ z.2.2.1 - z.2.2.2 then 1 else 0)
        + ((z.2.2.1 - z.2.2.2 : ℤ) : ℝ) * ((z.2.1 - z.2.2.1 : ℤ) : ℝ)))).comp
    ((S.N_meas (tg ε (i + 1))).prodMk ((S.N_meas (tg ε i)).prodMk
      ((S.N_meas (tg ε (i + 1) - P.L2)).prodMk (S.N_meas (tg ε i - P.L2)))))
  unfold hreal cc bb rr
  exact h

lemma lintegral_hreal_le (hε : 0 < ε) (hεL : ε ≤ P.L2) (hSb : 0 ≤ Sb) {i : ℕ}
    (hi : P.L2 ≤ tg ε (i + 1)) :
    ∫⁻ ω, ENNReal.ofReal (hreal S Sb ε i ω) ∂S.ν
      ≤ ENNReal.ofReal ((P.lam * ε) ^ 2 + P.lam * (P.L2 - ε) * (P.lam * ε)
          + Sb * (P.lam * ε) ^ 2 + P.lam * ε * (P.lam * (P.L2 - ε))) := by
  have hS : (0 : ℝ) ≤ Sb := by exact_mod_cast hSb
  have hsucc := tg_succ (ε := ε) i
  have hti := tg_nonneg hε.le i
  have hc : ∀ ω, (0 : ℝ) ≤ cc S ε i ω := fun ω => by exact_mod_cast cc_nonneg hε i ω
  have hb : ∀ ω, (0 : ℝ) ≤ bb S ε i ω := fun ω => by exact_mod_cast bb_nonneg hεL i ω
  have hr : ∀ ω, (0 : ℝ) ≤ rr S ε i ω := fun ω => by exact_mod_cast rr_nonneg hε i ω
  have hcc : ∀ ω, (0 : ℝ) ≤ (cc S ε i ω : ℝ) * ((cc S ε i ω : ℝ) - 1) := fun ω => by
    have := fact2_nonneg (cc S ε i ω).toNat
    rwa [← Int.cast_natCast, Int.toNat_of_nonneg (cc_nonneg hε i ω)] at this
  set A : S.Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal ((cc S ε i ω : ℝ) * ((cc S ε i ω : ℝ) - 1)) with hA
  set B : S.Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal ((bb S ε i ω : ℝ) * (cc S ε i ω : ℝ)) with hB
  set C : S.Ω → ℝ≥0∞ := fun ω => {ω' | 2 ≤ rr S ε i ω'}.indicator (fun _ => ENNReal.ofReal Sb) ω
    with hC
  set D : S.Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal ((rr S ε i ω : ℝ) * (bb S ε i ω : ℝ)) with hD
  have e : ∀ ω, ENNReal.ofReal (hreal S Sb ε i ω) = A ω + B ω + C ω + D ω := by
    intro ω
    have hCv : C ω = ENNReal.ofReal ((Sb : ℝ) * (if 2 ≤ rr S ε i ω then 1 else 0)) := by
      simp only [hC, Set.indicator, Set.mem_setOf_eq]
      split_ifs <;> simp
    rw [hCv]
    unfold hreal
    have h5 : (0 : ℝ) ≤ (Sb : ℝ) * (if 2 ≤ rr S ε i ω then 1 else 0) := by split_ifs <;> simp [hS]
    rw [ENNReal.ofReal_add (by have := mul_nonneg (hb ω) (hc ω); have := hcc ω; positivity)
        (mul_nonneg (hr ω) (hb ω)),
      ENNReal.ofReal_add (by have := mul_nonneg (hb ω) (hc ω); have := hcc ω; positivity) h5,
      ENNReal.ofReal_add (hcc ω) (mul_nonneg (hb ω) (hc ω))]
  have hrm : Measurable (rr S ε i) := (S.N_meas _).sub (S.N_meas _)
  have hset : MeasurableSet {ω' | 2 ≤ rr S ε i ω'} := measurableSet_le measurable_const hrm
  have mA : Measurable A := by
    have h := (measurable_of_countable (fun z : ℤ => ENNReal.ofReal ((z : ℝ) * ((z : ℝ) - 1)))).comp
      ((S.N_meas (tg ε (i + 1))).sub (S.N_meas (tg ε i)))
    simp only [hA]; unfold cc; exact h
  have mB : Measurable B := by
    have h := (measurable_of_countable (fun z : ℤ × ℤ => ENNReal.ofReal ((z.1 : ℝ) * (z.2 : ℝ)))).comp
      (((S.N_meas (tg ε i)).sub (S.N_meas (tg ε (i + 1) - P.L2))).prodMk
        ((S.N_meas (tg ε (i + 1))).sub (S.N_meas (tg ε i))))
    simp only [hB]; unfold bb cc; exact h
  have mC : Measurable C := (measurable_const.indicator hset)
  have mAB : Measurable (fun ω => A ω + B ω) := by have h := mA.add mB; exact h
  have mABC : Measurable (fun ω => A ω + B ω + C ω) := by have h := mAB.add mC; exact h
  rw [lintegral_congr e, lintegral_add_left mABC, lintegral_add_left mAB, lintegral_add_left mA]

  have iA : ∫⁻ ω, A ω ∂S.ν = ENNReal.ofReal ((P.lam * ε) ^ 2) := by
    simp only [hA]; unfold cc
    rw [lintegral_fact2 S (show tg ε i ≤ tg ε (i + 1) by linarith), hsucc]
    congr 2; ring
  have iB : ∫⁻ ω, B ω ∂S.ν = ENNReal.ofReal (P.lam * (P.L2 - ε)) * ENNReal.ofReal (P.lam * ε) := by
    have hY : Measurable[S.𝓕 (tg ε i)] (bb S ε i) := by
      unfold bb
      exact (S.N_adapted _).sub (S.N_meas_le (by linarith))
    have h := lintegral_mul_incr' S hti (show tg ε i ≤ tg ε (i + 1) by linarith) hY
    simp only [hB]; unfold cc
    rw [h]
    have h2 : ∫⁻ ω, ENNReal.ofReal ((bb S ε i ω : ℤ) : ℝ) ∂S.ν = ENNReal.ofReal (P.lam * (P.L2 - ε)) := by
      unfold bb
      rw [S.lintegral_incr_val (by linarith), hsucc]
      congr 2; ring
    rw [h2, hsucc]
    congr 2; ring
  have iC : ∫⁻ ω, C ω ∂S.ν ≤ ENNReal.ofReal Sb * ENNReal.ofReal ((P.lam * ε) ^ 2) := by
    simp only [hC]
    rw [lintegral_indicator_const hset]
    gcongr
    have h := LBP.pois_two S (show tg ε i - P.L2 ≤ tg ε (i + 1) - P.L2 by linarith)
    unfold rr
    refine h.trans (le_of_eq ?_)
    rw [hsucc]
    congr 2; ring
  have iD : ∫⁻ ω, D ω ∂S.ν = ENNReal.ofReal (P.lam * ε) * ENNReal.ofReal (P.lam * (P.L2 - ε)) := by
    have hv0 : 0 ≤ tg ε (i + 1) - P.L2 := by linarith
    have hY : Measurable[S.𝓕 (tg ε (i + 1) - P.L2)] (rr S ε i) := by
      unfold rr
      exact (S.N_adapted _).sub (S.N_meas_le (by linarith))
    have h := lintegral_mul_incr' S hv0 (show tg ε (i + 1) - P.L2 ≤ tg ε i by linarith) hY
    simp only [hD]; unfold bb
    rw [h]
    have h2 : ∫⁻ ω, ENNReal.ofReal ((rr S ε i ω : ℤ) : ℝ) ∂S.ν = ENNReal.ofReal (P.lam * ε) := by
      unfold rr
      rw [S.lintegral_incr_val (by linarith), hsucc]
      congr 2; ring
    rw [h2, hsucc]
    congr 2; ring
  rw [iA, iB, iD]
  have hl := P.lam_nonneg
  have k1 : 0 ≤ P.lam * (P.L2 - ε) := mul_nonneg hl (by linarith)
  have k2 : 0 ≤ P.lam * ε := mul_nonneg hl hε.le
  calc ENNReal.ofReal ((P.lam * ε) ^ 2) + ENNReal.ofReal (P.lam * (P.L2 - ε)) * ENNReal.ofReal (P.lam * ε)
        + ∫⁻ ω, C ω ∂S.ν + ENNReal.ofReal (P.lam * ε) * ENNReal.ofReal (P.lam * (P.L2 - ε))
      ≤ ENNReal.ofReal ((P.lam * ε) ^ 2) + ENNReal.ofReal (P.lam * (P.L2 - ε)) * ENNReal.ofReal (P.lam * ε)
        + ENNReal.ofReal Sb * ENNReal.ofReal ((P.lam * ε) ^ 2)
        + ENNReal.ofReal (P.lam * ε) * ENNReal.ofReal (P.lam * (P.L2 - ε)) := by gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul k1, ← ENNReal.ofReal_mul hS, ← ENNReal.ofReal_mul k2,
        ← ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg k1 k2),
        ← ENNReal.ofReal_add (add_nonneg (sq_nonneg _) (mul_nonneg k1 k2)) (mul_nonneg hS (sq_nonneg _)),
        ← ENNReal.ofReal_add (add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg k1 k2))
          (mul_nonneg hS (sq_nonneg _))) (mul_nonneg k2 k1)]

end SetupExp

section SetupTotal

variable {P : Params} {S : DemandSpace P} {Sb : ℤ} {ε : ℝ}

theorem lintegral_jumps_le (hε : 0 < ε) (hεL : ε ≤ P.L2) (hSb : 0 < Sb) {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ ω, ENNReal.ofReal (jumpCount (fun t => U1c S Sb ε t ω) T : ℝ) ∂S.ν
      ≤ ENNReal.ofReal ((P.lam * T + (⌈P.L2 / ε⌉₊ : ℝ) * Sb
          + T * P.lam ^ 2 * (2 * P.L2 + Sb * ε)) / Sb) := by
  set K := ⌊T / ε⌋₊ with hK
  set i0 := ⌈P.L2 / ε⌉₊ with hi0
  have hS : (0 : ℝ) < Sb := by exact_mod_cast hSb
  have hl := P.lam_nonneg
  set hval : ℝ := (P.lam * ε) ^ 2 + P.lam * (P.L2 - ε) * (P.lam * ε)
      + Sb * (P.lam * ε) ^ 2 + P.lam * ε * (P.lam * (P.L2 - ε)) with hhval
  have k1 : 0 ≤ P.lam * (P.L2 - ε) := mul_nonneg hl (by linarith)
  have k2 : 0 ≤ P.lam * ε := mul_nonneg hl hε.le
  have hval0 : 0 ≤ hval := by
    have := mul_nonneg k1 k2; have := mul_nonneg hS.le (sq_nonneg (P.lam * ε))
    have := mul_nonneg k2 k1; have := sq_nonneg (P.lam * ε)
    linarith

  have hterm : ∀ i ω, 0 ≤ (if i < i0 then (Sb : ℝ) else hreal S Sb ε i ω) := by
    intro i ω
    split_ifs
    · exact hS.le
    · exact hreal_nonneg hε hεL hSb.le i ω
  have hpath : ∀ ω, ENNReal.ofReal Sb * ENNReal.ofReal (jumpCount (fun t => U1c S Sb ε t ω) T : ℝ)
      ≤ ENNReal.ofReal ((uu S Sb ε K ω - uu S Sb ε 0 ω : ℤ) : ℝ)
        + ∑ i ∈ Finset.range K, ENNReal.ofReal (if i < i0 then (Sb : ℝ) else hreal S Sb ε i ω) := by
    intro ω
    have h1 := jumpCount_U1c_le' (Sb := Sb) hε ω T
    have h2 := jumps_path (S := S) hε hεL hSb.le i0 K ω
    have h1' : (jumpCount (fun t => U1c S Sb ε t ω) T : ℝ)
        ≤ (((Finset.range K).filter (fun i => uu S Sb ε i ω < uu S Sb ε (i + 1) ω)).card : ℝ) := by
      exact_mod_cast h1
    have hu : (0 : ℝ) ≤ ((uu S Sb ε K ω - uu S Sb ε 0 ω : ℤ) : ℝ) := by
      have := uu_mono (S := S) (Sb := Sb) hε.le ω (Nat.zero_le K)
      simp only at this
      exact_mod_cast (by omega : (0 : ℤ) ≤ uu S Sb ε K ω - uu S Sb ε 0 ω)
    rw [← ENNReal.ofReal_mul hS.le, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hterm i ω),
      ← ENNReal.ofReal_add hu (Finset.sum_nonneg (fun i _ => hterm i ω))]
    apply ENNReal.ofReal_le_ofReal
    have := mul_le_mul_of_nonneg_left h1' hS.le
    linarith

  have hmu : Measurable (fun ω => ENNReal.ofReal ((uu S Sb ε K ω - uu S Sb ε 0 ω : ℤ) : ℝ)) := by
    have h := (measurable_of_countable (fun z : ℤ => ENNReal.ofReal (z : ℝ))).comp
      (((uu_meas (S := S) (Sb := Sb) hε.le K).mono (S.𝓕.le _) le_rfl).sub
        ((uu_meas (S := S) (Sb := Sb) hε.le 0).mono (S.𝓕.le _) le_rfl))
    exact h
  have hmt : ∀ i ∈ Finset.range K, Measurable
      (fun ω => ENNReal.ofReal (if i < i0 then (Sb : ℝ) else hreal S Sb ε i ω)) := by
    intro i _
    by_cases h : i < i0
    · simp only [h, if_true]; exact measurable_const
    · simp only [h, if_false]; exact hreal_meas i

  have hE1 : ∫⁻ ω, ENNReal.ofReal ((uu S Sb ε K ω - uu S Sb ε 0 ω : ℤ) : ℝ) ∂S.ν
      ≤ ENNReal.ofReal (P.lam * T) := by
    have hKT : tg ε K ≤ T := by
      unfold tg
      have := Nat.floor_le (div_nonneg hT hε.le)
      calc (K : ℝ) * ε ≤ T / ε * ε := mul_le_mul_of_nonneg_right this hε.le
        _ = T := div_mul_cancel₀ T hε.ne'
    calc _ ≤ ∫⁻ ω, ENNReal.ofReal ((S.N (tg ε K - P.L2) ω - S.N (-P.L2) ω : ℤ) : ℝ) ∂S.ν := by
          refine lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal ?_)
          have := uu_le (S := S) (Sb := Sb) hε.le ω K
          have h0 : uu S Sb ε 0 ω = S.N (-P.L2) ω := rfl
          exact_mod_cast (by omega : uu S Sb ε K ω - uu S Sb ε 0 ω
            ≤ S.N (tg ε K - P.L2) ω - S.N (-P.L2) ω)
      _ = ENNReal.ofReal (P.lam * (tg ε K - P.L2 - -P.L2)) :=
          S.lintegral_incr_val (by linarith [tg_nonneg hε.le K])
      _ ≤ ENNReal.ofReal (P.lam * T) := by
          apply ENNReal.ofReal_le_ofReal
          have : tg ε K - P.L2 - -P.L2 = tg ε K := by ring
          rw [this]
          exact mul_le_mul_of_nonneg_left hKT hl
  have hE2 : ∀ i ∈ Finset.range K,
      ∫⁻ ω, ENNReal.ofReal (if i < i0 then (Sb : ℝ) else hreal S Sb ε i ω) ∂S.ν
        ≤ ENNReal.ofReal (if i < i0 then (Sb : ℝ) else hval) := by
    intro i _
    by_cases h : i < i0
    · simp only [h, if_true, lintegral_const, measure_univ, mul_one, le_refl]
    · simp only [h, if_false]
      have hi : P.L2 ≤ tg ε (i + 1) := by
        push_neg at h
        unfold tg
        have hc := Nat.le_ceil (P.L2 / ε)
        have : (i0 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : i0 ≤ i + 1)
        calc P.L2 = P.L2 / ε * ε := (div_mul_cancel₀ _ hε.ne').symm
          _ ≤ (i0 : ℝ) * ε := mul_le_mul_of_nonneg_right hc hε.le
          _ ≤ ((i + 1 : ℕ) : ℝ) * ε := mul_le_mul_of_nonneg_right this hε.le
      exact lintegral_hreal_le hε hεL hSb.le hi
  have hsum : ∑ i ∈ Finset.range K, (if i < i0 then (Sb : ℝ) else hval)
      ≤ (i0 : ℝ) * Sb + K * hval := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have c1 : ((Finset.range K).filter (fun i => i < i0)).card ≤ i0 := by
      calc _ ≤ (Finset.range i0).card := Finset.card_le_card (fun i hi => by
            simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢; omega)
        _ = i0 := Finset.card_range i0
    have c2 : ((Finset.range K).filter (fun i => ¬ i < i0)).card ≤ K :=
      (Finset.card_filter_le _ _).trans (Finset.card_range K).le
    have c1' : (((Finset.range K).filter (fun i => i < i0)).card : ℝ) ≤ i0 := by exact_mod_cast c1
    have c2' : (((Finset.range K).filter (fun i => ¬ i < i0)).card : ℝ) ≤ K := by exact_mod_cast c2
    have := mul_le_mul_of_nonneg_right c1' hS.le
    have := mul_le_mul_of_nonneg_right c2' hval0
    linarith
  have hKval : (K : ℝ) * hval ≤ T * P.lam ^ 2 * (2 * P.L2 + Sb * ε) := by
    have hKle : (K : ℝ) ≤ T / ε := Nat.floor_le (div_nonneg hT hε.le)
    have e : T / ε * hval = T * P.lam ^ 2 * (2 * P.L2 - ε + Sb * ε) := by
      rw [hhval]; field_simp; ring
    have h2 : T * P.lam ^ 2 * (2 * P.L2 - ε + Sb * ε) ≤ T * P.lam ^ 2 * (2 * P.L2 + Sb * ε) := by
      have : 0 ≤ T * P.lam ^ 2 := by positivity
      nlinarith
    calc (K : ℝ) * hval ≤ T / ε * hval := mul_le_mul_of_nonneg_right hKle hval0
      _ = _ := e
      _ ≤ _ := h2

  have hmain : ENNReal.ofReal Sb * ∫⁻ ω, ENNReal.ofReal (jumpCount (fun t => U1c S Sb ε t ω) T : ℝ) ∂S.ν
      ≤ ENNReal.ofReal (P.lam * T + (i0 : ℝ) * Sb + T * P.lam ^ 2 * (2 * P.L2 + Sb * ε)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc _ ≤ ∫⁻ ω, (ENNReal.ofReal ((uu S Sb ε K ω - uu S Sb ε 0 ω : ℤ) : ℝ)
          + ∑ i ∈ Finset.range K, ENNReal.ofReal (if i < i0 then (Sb : ℝ) else hreal S Sb ε i ω)) ∂S.ν :=
          lintegral_mono hpath
      _ = ∫⁻ ω, ENNReal.ofReal ((uu S Sb ε K ω - uu S Sb ε 0 ω : ℤ) : ℝ) ∂S.ν
          + ∑ i ∈ Finset.range K, ∫⁻ ω, ENNReal.ofReal (if i < i0 then (Sb : ℝ) else hreal S Sb ε i ω) ∂S.ν := by
          rw [lintegral_add_left hmu, lintegral_finsetSum _ hmt]
      _ ≤ ENNReal.ofReal (P.lam * T) + ∑ i ∈ Finset.range K, ENNReal.ofReal (if i < i0 then (Sb : ℝ) else hval) :=
          add_le_add hE1 (Finset.sum_le_sum hE2)
      _ = ENNReal.ofReal (P.lam * T + ∑ i ∈ Finset.range K, (if i < i0 then (Sb : ℝ) else hval)) := by
          rw [ENNReal.ofReal_add (mul_nonneg hl hT) (Finset.sum_nonneg (fun i _ => by
              split_ifs; exact hS.le; exact hval0)),
            ENNReal.ofReal_sum_of_nonneg (fun i _ => by split_ifs; exact hS.le; exact hval0)]
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          linarith
  rw [ENNReal.ofReal_div_of_pos hS, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hS))
    (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact hmain

end SetupTotal

end Imp

end TwoStageRnQ

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace Imp

open TwoStageRnQ.LB

lemma jumpCount_le_diff {f : ℝ → ℤ} (hf : Monotone f) {T : ℝ} (hT : 0 ≤ T) :
    (jumpCount f T : ℤ) ≤ f T - f 0 := by
  have hfin := jumps_finite hf T
  have e : {t | t ∈ Set.Ioc 0 T ∧ ∀ s < t, f s < f t} = {t | t ∈ Set.Ioc 0 T ∧ IsJump f t} := by
    ext t
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, (jump_iff hf t).mp h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, (jump_iff hf t).mpr h2⟩
  unfold jumpCount
  rw [e, Set.ncard_eq_toFinset_card _ hfin]
  exact jumps_card hf hfin.toFinset T hT (fun t ht => by
    rw [Set.Finite.mem_toFinset] at ht; exact ⟨ht.1.1, ht.1.2, ht.2⟩)

lemma limsup_le_of_affine {f : ℝ → ℝ≥0∞} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ T, 0 < T → f T ≤ ENNReal.ofReal (A * T + B)) :
    limsup (fun T : ℝ => ENNReal.ofReal T⁻¹ * f T) atTop ≤ ENNReal.ofReal A := by
  have hlim : Tendsto (fun T : ℝ => ENNReal.ofReal (A + B * T⁻¹)) atTop (𝓝 (ENNReal.ofReal A)) := by
    have : Tendsto (fun T : ℝ => A + B * T⁻¹) atTop (𝓝 (A + B * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_inv_atTop_zero)
    rw [mul_zero, add_zero] at this
    exact ENNReal.tendsto_ofReal this
  calc limsup (fun T : ℝ => ENNReal.ofReal T⁻¹ * f T) atTop
      ≤ limsup (fun T : ℝ => ENNReal.ofReal (A + B * T⁻¹)) atTop := by
        refine Filter.limsup_le_limsup ?_
        filter_upwards [eventually_gt_atTop 0] with T hT
        calc ENNReal.ofReal T⁻¹ * f T ≤ ENNReal.ofReal T⁻¹ * ENNReal.ofReal (A * T + B) := by
              gcongr; exact h T hT
          _ = ENNReal.ofReal (A + B * T⁻¹) := by
              rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hT.le)]
              congr 1
              field_simp
    _ = ENNReal.ofReal A := hlim.limsup_eq

section Total

variable {P : Params} {S : DemandSpace P} {Sb : ℤ} {ε : ℝ}

def costA (P : Params) (Sb : ℤ) (ε Φ : ℝ) : ℝ :=
  Φ + P.h1 * Sb + 4 * (P.h2 + P.p) * P.lam * ε + (P.h2 + P.p) * P.L1 * P.lam
    + P.K1 * (P.lam + P.lam ^ 2 * (2 * P.L2 + Sb * ε)) / Sb + P.K2 * P.lam

def costB (P : Params) (Sb : ℤ) (ε : ℝ) : ℝ :=
  (P.h2 + P.p) * (P.L1 * (Sb + P.lam * (P.L1 + ε))) + P.K1 * (⌈P.L2 / ε⌉₊ : ℝ)

lemma costB_nonneg (hε : 0 < ε) (hSb : 0 ≤ Sb) : 0 ≤ costB P Sb ε := by
  unfold costB
  have := P.lam_nonneg; have := P.L1_nonneg; have := P.h2_nonneg; have := P.p_nonneg
  have := P.K1_nonneg
  have hS : (0 : ℝ) ≤ Sb := by exact_mod_cast hSb
  positivity

lemma costA_nonneg (hε : 0 < ε) (hSb : 0 < Sb) {Φ : ℝ} (hΦ0 : 0 ≤ Φ) : 0 ≤ costA P Sb ε Φ := by
  unfold costA
  have := P.lam_nonneg; have := P.L1_nonneg; have := P.h2_nonneg; have := P.p_nonneg
  have := P.K1_nonneg; have := P.K2_nonneg; have := P.h1_nonneg; have := P.L2_nonneg
  have hS : (0 : ℝ) < Sb := by exact_mod_cast hSb
  positivity

theorem expected_total_le (hε : 0 < ε) (hεL : ε ≤ P.L2) (hSb : 0 < Sb) {Φ : ℝ} (hΦ0 : 0 ≤ Φ)
    (hΦ : ∀ t, ∫⁻ ω, ENNReal.ofReal (phi P.h2 P.p ((Sb + S.N (t - P.L2) ω - S.N t ω : ℤ) : ℝ)) ∂S.ν
      ≤ ENNReal.ofReal Φ) {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ ω, ((∫⁻ t in Set.Ioc 0 T, ENNReal.ofReal ((pol (S := S) (Sb := Sb) hε).cI t ω))
        + ENNReal.ofReal ((pol (S := S) (Sb := Sb) hε).shipSetup T ω)) ∂S.ν
      ≤ ENNReal.ofReal (costA P Sb ε Φ * T + costB P Sb ε) := by
  have hS : (0 : ℝ) < Sb := by exact_mod_cast hSb
  have hl := P.lam_nonneg
  have hK1 := P.K1_nonneg
  have hK2 := P.K2_nonneg
  have h1 := lintegral_cost_add_le (S := S) hε hSb.le hΦ0 hΦ le_rfl hT
    (fun ω => ENNReal.ofReal ((pol (S := S) (Sb := Sb) hε).shipSetup T ω))
  refine h1.trans ?_

  have hsetup : ∀ ω, ENNReal.ofReal ((pol (S := S) (Sb := Sb) hε).shipSetup T ω)
      ≤ ENNReal.ofReal P.K1 * ENNReal.ofReal (jumpCount (fun t => U1c S Sb ε t ω) T : ℝ)
        + ENNReal.ofReal P.K2 * ENNReal.ofReal ((S.N T ω - S.N 0 ω : ℤ) : ℝ) := by
    intro ω
    have hj := jumpCount_le_diff (S.N_mono ω) hT
    have hj' : (jumpCount (fun t => S.N t ω) T : ℝ) ≤ ((S.N T ω - S.N 0 ω : ℤ) : ℝ) := by
      exact_mod_cast hj
    have hJ1 : (0 : ℝ) ≤ (jumpCount (fun t => U1c S Sb ε t ω) T : ℝ) := Nat.cast_nonneg _
    have hJ2 : (0 : ℝ) ≤ ((S.N T ω - S.N 0 ω : ℤ) : ℝ) := by exact_mod_cast S.incr_nonneg hT ω
    rw [← ENNReal.ofReal_mul hK1, ← ENNReal.ofReal_mul hK2,
      ← ENNReal.ofReal_add (mul_nonneg hK1 hJ1) (mul_nonneg hK2 hJ2)]
    apply ENNReal.ofReal_le_ofReal
    show P.K1 * (jumpCount (fun t => U1c S Sb ε t ω) T : ℝ)
        + P.K2 * (jumpCount (fun t => S.N t ω) T : ℝ) ≤ _
    have := mul_le_mul_of_nonneg_left hj' hK2
    linarith
  have hm2 : Measurable (fun ω => ENNReal.ofReal P.K2 * ENNReal.ofReal ((S.N T ω - S.N 0 ω : ℤ) : ℝ)) := by
    have h := (measurable_of_countable (fun z : ℤ × ℤ => ENNReal.ofReal P.K2
      * ENNReal.ofReal ((z.1 - z.2 : ℤ) : ℝ))).comp ((S.N_meas T).prodMk (S.N_meas 0))
    exact h
  have hE : ∫⁻ ω, ENNReal.ofReal ((pol (S := S) (Sb := Sb) hε).shipSetup T ω) ∂S.ν
      ≤ ENNReal.ofReal P.K1 * ENNReal.ofReal ((P.lam * T + (⌈P.L2 / ε⌉₊ : ℝ) * Sb
          + T * P.lam ^ 2 * (2 * P.L2 + Sb * ε)) / Sb)
        + ENNReal.ofReal P.K2 * ENNReal.ofReal (P.lam * T) := by
    calc _ ≤ ∫⁻ ω, (ENNReal.ofReal P.K1 * ENNReal.ofReal (jumpCount (fun t => U1c S Sb ε t ω) T : ℝ)
          + ENNReal.ofReal P.K2 * ENNReal.ofReal ((S.N T ω - S.N 0 ω : ℤ) : ℝ)) ∂S.ν :=
          lintegral_mono hsetup
      _ = ENNReal.ofReal P.K1 * ∫⁻ ω, ENNReal.ofReal (jumpCount (fun t => U1c S Sb ε t ω) T : ℝ) ∂S.ν
          + ENNReal.ofReal P.K2 * ∫⁻ ω, ENNReal.ofReal ((S.N T ω - S.N 0 ω : ℤ) : ℝ) ∂S.ν := by
          rw [lintegral_add_right _ hm2, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ _ := by
          gcongr
          · exact lintegral_jumps_le hε hεL hSb hT
          · rw [S.lintegral_incr_val hT, sub_zero]
  calc _ ≤ ENNReal.ofReal ((Φ + P.h1 * Sb + 4 * (P.h2 + P.p) * P.lam * ε) * (T - 0)
          + (P.h2 + P.p) * (P.L1 * (Sb + P.lam * (T - 0 + P.L1 + ε))))
        + (ENNReal.ofReal P.K1 * ENNReal.ofReal ((P.lam * T + (⌈P.L2 / ε⌉₊ : ℝ) * Sb
          + T * P.lam ^ 2 * (2 * P.L2 + Sb * ε)) / Sb)
          + ENNReal.ofReal P.K2 * ENNReal.ofReal (P.lam * T)) := add_le_add le_rfl hE
    _ = ENNReal.ofReal (costA P Sb ε Φ * T + costB P Sb ε) := by
        have k0 : 0 ≤ (Φ + P.h1 * Sb + 4 * (P.h2 + P.p) * P.lam * ε) * (T - 0)
            + (P.h2 + P.p) * (P.L1 * (Sb + P.lam * (T - 0 + P.L1 + ε))) := by
          have := P.L1_nonneg; have := P.h2_nonneg; have := P.p_nonneg; have := P.h1_nonneg
          rw [sub_zero]
          positivity
        have k1 : 0 ≤ (P.lam * T + (⌈P.L2 / ε⌉₊ : ℝ) * Sb
            + T * P.lam ^ 2 * (2 * P.L2 + Sb * ε)) / Sb := by
          have := P.L2_nonneg
          positivity
        rw [← ENNReal.ofReal_mul hK1, ← ENNReal.ofReal_mul hK2,
          ← ENNReal.ofReal_add (mul_nonneg hK1 k1) (mul_nonneg hK2 (mul_nonneg hl hT)),
          ← ENNReal.ofReal_add k0 (add_nonneg (mul_nonneg hK1 k1) (mul_nonneg hK2 (mul_nonneg hl hT)))]
        congr 1
        unfold costA costB
        field_simp
        ring

theorem shipCost_pol_le (hε : 0 < ε) (hεL : ε ≤ P.L2) (hSb : 0 < Sb) {Φ : ℝ} (hΦ0 : 0 ≤ Φ)
    (hΦ : ∀ t, ∫⁻ ω, ENNReal.ofReal (phi P.h2 P.p ((Sb + S.N (t - P.L2) ω - S.N t ω : ℤ) : ℝ)) ∂S.ν
      ≤ ENNReal.ofReal Φ) :
    (pol (S := S) (Sb := Sb) hε).shipCost ≤ ENNReal.ofReal (costA P Sb ε Φ) := by
  unfold ShipmentPolicy.shipCost longRunCost
  exact limsup_le_of_affine (costA_nonneg hε hSb hΦ0) (costB_nonneg hε hSb.le)
    (fun T hT => expected_total_le hε hεL hSb hΦ0 hΦ hT.le)

end Total

end Imp

end TwoStageRnQ

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace Imp

open TwoStageRnQ.LB

section Unfinished

lemma loopErase_sub : ∀ p : List ℤ, ∀ y ∈ loopErase p, y ∈ p := by
  intro p
  induction p using List.reverseRecOn with
  | nil => intro y hy; simp [loopErase] at hy
  | append_singleton p s ih =>
    intro y hy
    rw [loopErase_snoc] at hy
    unfold loopEraseStep at hy
    rw [List.mem_append, List.mem_singleton]
    split_ifs at hy with hs
    · rw [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | hy
      · exact Or.inl (ih y ((List.takeWhile_sublist _).subset hy))
      · exact Or.inr hy
    · rw [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | hy
      · exact Or.inl (ih y hy)
      · exact Or.inr hy

lemma downCount_le_range (l : List ℤ) (hnd : l.Nodup) (lo hi : ℤ)
    (hb : ∀ y ∈ l, lo ≤ y ∧ y ≤ hi) : downCount l ≤ (hi - lo).toNat := by
  rw [downCount_eq_length]
  have hsub : (dstates l).Sublist l := (dstates_sub_dropLast l).trans (List.dropLast_sublist l)
  have hnd2 : (dstates l).Nodup := hnd.sublist hsub
  rw [← List.toFinset_card_of_nodup hnd2, ← Int.card_Ioc]
  refine Finset.card_le_card (fun y hy => ?_)
  rw [List.mem_toFinset] at hy
  obtain ⟨h1, h2⟩ := mem_dstates hy
  have b1 := hb y h1
  have b2 := hb (y - 1) h2
  rw [Finset.mem_Ioc]
  omega

lemma fold_bounds (x : ℤ) (U N : ℝ → ℤ) (hU : Monotone U) (hUr : RCont U)
    (hN : Monotone N) (hNr : RCont N) (T : ℝ) (lo hi : ℤ)
    (h1 : ∀ τ ∈ Set.Ioc 0 T, lo ≤ x + leftVal U τ - N τ)
    (h2 : ∀ τ ∈ Set.Ioc 0 T, x + leftVal U τ - leftVal N τ ≤ hi)
    (h3 : ∀ τ ∈ Set.Ioc 0 T, x + U τ - N τ ≤ hi) :
    ∀ (L : List ℝ) (p : ℝ) (acc : List ℤ × ℤ),
      0 ≤ p → p ≤ T → L.Pairwise (· < ·) → (∀ t ∈ L, p < t ∧ t ≤ T) →
      (∀ t, p < t → t ≤ T → ((IsJump N t ∨ IsJump U t) ↔ t ∈ L)) →
      acc.2 = x + U p - N p → (∀ y ∈ acc.1, lo ≤ y ∧ y ≤ hi) →
      ∀ y ∈ (L.foldl (cstep U N) acc).1, lo ≤ y ∧ y ≤ hi := by
  intro L
  induction L with
  | nil =>
    intro p acc _ _ _ _ _ _ hacc
    simpa using hacc
  | cons τ L ih =>
    intro p acc hp0 hpT hpw hmem hev hx hacc
    rw [List.pairwise_cons] at hpw
    have hτ := hmem τ List.mem_cons_self
    have hno : ∀ t, p < t → t < τ → ¬ (IsJump N t ∨ IsJump U t) := by
      intro t ht1 ht2 ht3
      have h4 := (hev t ht1 (by linarith [hτ.2])).mp ht3
      rcases List.mem_cons.mp h4 with h5 | h5
      · linarith
      · have := hpw.1 t h5; linarith
    have hlU : leftVal U τ = U p :=
      lv_noJump hU hUr hτ.1 (fun t ht1 ht2 ht3 => hno t ht1 ht2 (Or.inr ht3))
    have hlN : leftVal N τ = N p :=
      lv_noJump hN hNr hτ.1 (fun t ht1 ht2 ht3 => hno t ht1 ht2 (Or.inl ht3))
    have hdu : 0 ≤ U τ - leftVal U τ := by have := lv_le hU τ; omega
    have hdn : 0 ≤ N τ - leftVal N τ := by have := lv_le hN τ; omega
    have hτI : τ ∈ Set.Ioc 0 T := ⟨by linarith [hτ.1], hτ.2⟩
    have b1 := h1 τ hτI
    have b2 := h2 τ hτI
    have b3 := h3 τ hτI
    have hacc2 : acc.2 = x + leftVal U τ - leftVal N τ := by rw [hx, hlU, hlN]

    have hstep2 : (cstep U N acc τ).2 = x + U τ - N τ := by
      unfold cstep
      simp only
      split_ifs with hpos
      · rw [hacc2, Int.toNat_of_nonneg hdn]; ring
      · rw [hacc2, Int.toNat_of_nonneg hdn]
        have : U τ - leftVal U τ = 0 := by omega
        omega
    have hstep1 : ∀ y ∈ (cstep U N acc τ).1, lo ≤ y ∧ y ≤ hi := by
      intro y hy
      unfold cstep at hy
      simp only at hy
      rw [coe_range_map] at hy
      have hdown : ∀ y ∈ (List.range (N τ - leftVal N τ).toNat).map
          (fun j : ℕ => acc.2 - ((j : ℤ) + 1)), lo ≤ y ∧ y ≤ hi := by
        intro y hy
        rw [List.mem_map] at hy
        obtain ⟨j, hj, rfl⟩ := hy
        rw [List.mem_range] at hj
        have hj' : (j : ℤ) < N τ - leftVal N τ := by
          have := Int.toNat_of_nonneg hdn
          omega
        rw [hacc2]
        constructor <;> omega
      split_ifs at hy with hpos
      · rw [List.mem_append, List.mem_append, List.mem_singleton] at hy
        rcases hy with (hy | hy) | hy
        · exact hacc y hy
        · exact hdown y hy
        · rw [hy, hacc2, Int.toNat_of_nonneg hdn]
          have := lv_le hU τ
          constructor <;> omega
      · rw [List.mem_append] at hy
        rcases hy with hy | hy
        · exact hacc y hy
        · exact hdown y hy
    rw [List.foldl_cons]
    exact ih τ (cstep U N acc τ) (by linarith [hτ.1]) hτ.2 hpw.2
      (fun t ht => ⟨hpw.1 t ht, (hmem t (List.mem_cons_of_mem _ ht)).2⟩)
      (fun t ht1 ht2 => by
        rw [hev t (by linarith [hτ.1]) ht2, List.mem_cons]
        constructor
        · rintro (h | h)
          · linarith
          · exact h
        · exact fun h => Or.inr h)
      hstep2 hstep1

theorem chronPath_bounds (x : ℤ) (U N : ℝ → ℤ) (hU : Monotone U) (hUr : RCont U)
    (hN : Monotone N) (hNr : RCont N) {T : ℝ} (hT : 0 ≤ T) (lo hi : ℤ)
    (h0 : lo ≤ x + U 0 - N 0 ∧ x + U 0 - N 0 ≤ hi)
    (h1 : ∀ τ ∈ Set.Ioc 0 T, lo ≤ x + leftVal U τ - N τ)
    (h2 : ∀ τ ∈ Set.Ioc 0 T, x + leftVal U τ - leftVal N τ ≤ hi)
    (h3 : ∀ τ ∈ Set.Ioc 0 T, x + U τ - N τ ≤ hi) :
    ∀ y ∈ chronPath x U N T, lo ≤ y ∧ y ≤ hi := by
  have hE := evSet_finite hU hN T
  have hpw : (hE.toFinset.sort (· ≤ ·)).Pairwise (· < ·) := by
    have q1 := Finset.pairwise_sort hE.toFinset (· ≤ ·)
    have q2 := Finset.sort_nodup hE.toFinset (· ≤ ·)
    exact (q1.and q2).imp (fun h => lt_of_le_of_ne h.1 h.2)
  have hmemL : ∀ t, t ∈ hE.toFinset.sort (· ≤ ·) ↔ t ∈ evSet U N T := by
    intro t
    rw [Finset.mem_sort, Set.Finite.mem_toFinset]
  rw [chronPath_eq x U N T hE]
  refine fold_bounds x U N hU hUr hN hNr T lo hi h1 h2 h3 _ 0 _ le_rfl hT hpw
    (fun t ht => by
      have := (hmemL t).mp ht
      exact ⟨this.1.1, this.1.2⟩)
    (fun t ht1 ht2 => by
      rw [hmemL t]
      exact ⟨fun h => ⟨⟨ht1, ht2⟩, h⟩, fun h => h.2⟩)
    rfl ?_
  intro y hy
  simp only [List.mem_singleton] at hy
  rw [hy]
  exact h0

theorem unfinished_le (x : ℤ) (U N : ℝ → ℤ) (hU : Monotone U) (hUr : RCont U)
    (hN : Monotone N) (hNr : RCont N) {T : ℝ} (hT : 0 ≤ T) (lo hi : ℤ)
    (h0 : lo ≤ x + U 0 - N 0 ∧ x + U 0 - N 0 ≤ hi)
    (h1 : ∀ τ ∈ Set.Ioc 0 T, lo ≤ x + leftVal U τ - N τ)
    (h2 : ∀ τ ∈ Set.Ioc 0 T, x + leftVal U τ - leftVal N τ ≤ hi)
    (h3 : ∀ τ ∈ Set.Ioc 0 T, x + U τ - N τ ≤ hi) :
    unfinishedCount x U N T ≤ (hi - lo).toNat := by
  unfold unfinishedCount
  have hch := (chron_spec (fun _ => (0 : ℝ)) 0 x U N hU hUr hN hNr hT).1
  have hnd := (erase_bound (fun _ => (0 : ℝ)) 0 (fun _ => le_rfl) le_rfl (C := 0)
    (fun m s _ => by simp) (chronPath x U N T) hch).1
  have hb := chronPath_bounds x U N hU hUr hN hNr hT lo hi h0 h1 h2 h3
  exact downCount_le_range _ hnd lo hi (fun y hy => hb y (loopErase_sub _ y hy))

end Unfinished

end Imp

end TwoStageRnQ

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace Imp

open TwoStageRnQ.LB

section Limits

lemma ennreal_rate {f : ℝ → ℝ≥0∞} {c B : ℝ} (hc : 0 ≤ c) (hB : 0 ≤ B)
    (hup : ∀ T, 0 ≤ T → f T ≤ ENNReal.ofReal (c * T + B))
    (hlo : ∀ T, 0 ≤ T → ENNReal.ofReal (c * T) ≤ f T + ENNReal.ofReal B) :
    Tendsto (fun T : ℝ => ENNReal.ofReal T⁻¹ * f T) atTop (𝓝 (ENNReal.ofReal c)) := by
  set g : ℝ → ℝ := fun T => (f T).toReal with hg
  have hfin : ∀ T, 0 ≤ T → f T ≠ ⊤ := fun T hT =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hup T hT)
  have hfg : ∀ T, 0 ≤ T → f T = ENNReal.ofReal (g T) := fun T hT =>
    (ENNReal.ofReal_toReal (hfin T hT)).symm
  have hbd : ∀ T, 0 ≤ T → |g T - c * T| ≤ B := by
    intro T hT
    have h1 := hup T hT
    have h2 := hlo T hT
    rw [hfg T hT] at h1 h2
    have hcT : 0 ≤ c * T := mul_nonneg hc hT
    have hgT : 0 ≤ g T := ENNReal.toReal_nonneg
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    rw [← ENNReal.ofReal_add hgT hB, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
    rw [abs_le]; constructor <;> linarith
  have hlim := ENNReal.tendsto_ofReal (Prop1.tendsto_of_bdd hbd)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with T hT
  rw [hfg T hT, ENNReal.ofReal_mul (inv_nonneg.mpr hT)]

lemma ennreal_o {f : ℝ → ℝ≥0∞} {B : ℝ} (hup : ∀ T, 0 ≤ T → f T ≤ ENNReal.ofReal B) :
    Tendsto (fun T : ℝ => ENNReal.ofReal T⁻¹ * f T) atTop (𝓝 0) := by
  have hlim : Tendsto (fun T : ℝ => ENNReal.ofReal (T⁻¹ * B)) atTop (𝓝 0) := by
    have : Tendsto (fun T : ℝ => T⁻¹ * B) atTop (𝓝 (0 * B)) := tendsto_inv_atTop_zero.mul_const B
    rw [zero_mul] at this
    have h := ENNReal.tendsto_ofReal this
    rwa [ENNReal.ofReal_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun T => zero_le)) ?_
  filter_upwards [eventually_ge_atTop 0] with T hT
  calc ENNReal.ofReal T⁻¹ * f T ≤ ENNReal.ofReal T⁻¹ * ENNReal.ofReal B := by
        gcongr; exact hup T hT
    _ = ENNReal.ofReal (T⁻¹ * B) := (ENNReal.ofReal_mul (inv_nonneg.mpr hT)).symm

lemma ennreal_o' {f : ℝ → ℝ≥0∞} {g : ℝ → ℝ} (hup : ∀ᶠ T in atTop, f T ≤ ENNReal.ofReal (g T))
    (hg : Tendsto (fun T => T⁻¹ * g T) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => ENNReal.ofReal T⁻¹ * f T) atTop (𝓝 0) := by
  have hlim : Tendsto (fun T : ℝ => ENNReal.ofReal (T⁻¹ * g T)) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal hg
    rwa [ENNReal.ofReal_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall (fun T => zero_le)) ?_
  filter_upwards [eventually_ge_atTop 0, hup] with T hT hf
  calc ENNReal.ofReal T⁻¹ * f T ≤ ENNReal.ofReal T⁻¹ * ENNReal.ofReal (g T) := by gcongr
    _ = ENNReal.ofReal (T⁻¹ * g T) := (ENNReal.ofReal_mul (inv_nonneg.mpr hT)).symm

lemma tendsto_sqrt_bound (a b c : ℝ) :
    Tendsto (fun T : ℝ => T⁻¹ * (a + √T + (b * T + c) / √T)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h2 : Tendsto (fun T : ℝ => (√T)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have h3 : Tendsto (fun T : ℝ => a * T⁻¹ + (√T)⁻¹ + b * (√T)⁻¹ + c * (T⁻¹ * (√T)⁻¹)) atTop
      (𝓝 (a * 0 + 0 + b * 0 + c * (0 * 0))) :=
    (((h1.const_mul a).add h2).add (h2.const_mul b)).add ((h1.mul h2).const_mul c)
  simp only [mul_zero, add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  have hs : 0 < √T := Real.sqrt_pos.mpr hT
  have hss : √T * √T = T := Real.mul_self_sqrt hT.le
  generalize √T = u at hs hss ⊢
  subst hss
  field_simp
  ring

end Limits

section Window

variable {P : Params} (S : DemandSpace P)

def Vk (v : ℝ) (k : ℕ) (ω : S.Ω) : ℤ := S.N (((k : ℝ) + 1) * v) ω - S.N (((k : ℝ) - 1) * v) ω

def Mx (v T : ℝ) (ω : S.Ω) : ℕ := (Finset.range (⌊T / v⌋₊ + 1)).sup (fun k => (Vk S v k ω).toNat)

variable {S}

lemma Vk_nonneg {v : ℝ} (hv : 0 < v) (k : ℕ) (ω : S.Ω) : 0 ≤ Vk S v k ω := by
  unfold Vk
  exact S.incr_nonneg (by nlinarith) ω

lemma window_le_Mx {v : ℝ} (hv : 0 < v) {T τ : ℝ} (hτ0 : 0 ≤ τ) (hτT : τ ≤ T) (ω : S.Ω) :
    S.N τ ω - S.N (τ - v) ω ≤ (Mx S v T ω : ℤ) := by
  set k := ⌊τ / v⌋₊ with hk
  have hk1 : (k : ℝ) * v ≤ τ := by
    have := Nat.floor_le (div_nonneg hτ0 hv.le)
    calc (k : ℝ) * v ≤ τ / v * v := mul_le_mul_of_nonneg_right this hv.le
      _ = τ := div_mul_cancel₀ τ hv.ne'
  have hk2 : τ < ((k : ℝ) + 1) * v := by
    have := Nat.lt_floor_add_one (τ / v)
    calc τ = τ / v * v := (div_mul_cancel₀ τ hv.ne').symm
      _ < ((k : ℝ) + 1) * v := mul_lt_mul_of_pos_right this hv
  have hkK : k ∈ Finset.range (⌊T / v⌋₊ + 1) := by
    rw [Finset.mem_range]
    have := Nat.floor_mono (div_le_div_of_nonneg_right hτT hv.le)
    omega
  have m1 := S.N_mono ω hk2.le
  have m2 := S.N_mono ω (show ((k : ℝ) - 1) * v ≤ τ - v by nlinarith)
  simp only at m1 m2
  have hV : S.N τ ω - S.N (τ - v) ω ≤ Vk S v k ω := by unfold Vk; omega
  have hsup : (Vk S v k ω).toNat ≤ Mx S v T ω :=
    Finset.le_sup (f := fun k => (Vk S v k ω).toNat) hkK
  have := Int.toNat_of_nonneg (Vk_nonneg hv k ω)
  omega

lemma Mx_le {v : ℝ} (hv : 0 < v) (T : ℝ) {m : ℝ} (hm : 0 < m) (ω : S.Ω) :
    (Mx S v T ω : ℝ) ≤ m + ∑ k ∈ Finset.range (⌊T / v⌋₊ + 1), ((Vk S v k ω : ℝ) ^ 2 / m) := by
  obtain ⟨k, hk, he⟩ := Finset.exists_mem_eq_sup (Finset.range (⌊T / v⌋₊ + 1))
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩ (fun k => (Vk S v k ω).toNat)
  unfold Mx
  rw [he]
  have hV := Vk_nonneg hv k ω
  have e : (((Vk S v k ω).toNat : ℕ) : ℝ) = (Vk S v k ω : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hV]
  rw [e]
  have hsum : (Vk S v k ω : ℝ) ^ 2 / m ≤ ∑ k ∈ Finset.range (⌊T / v⌋₊ + 1), ((Vk S v k ω : ℝ) ^ 2 / m) :=
    Finset.single_le_sum (f := fun k => (Vk S v k ω : ℝ) ^ 2 / m)
      (fun i _ => div_nonneg (sq_nonneg _) hm.le) hk
  have hsum0 : 0 ≤ ∑ k ∈ Finset.range (⌊T / v⌋₊ + 1), ((Vk S v k ω : ℝ) ^ 2 / m) :=
    Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) hm.le)
  by_cases h : (Vk S v k ω : ℝ) ≤ m
  · linarith
  · push_neg at h
    have : (Vk S v k ω : ℝ) ≤ (Vk S v k ω : ℝ) ^ 2 / m := by
      rw [le_div_iff₀ hm]; nlinarith
    linarith

lemma lintegral_Mx_le {v : ℝ} (hv : 0 < v) (T : ℝ) {m : ℝ} (hm : 0 < m) :
    ∫⁻ ω, ENNReal.ofReal (Mx S v T ω : ℝ) ∂S.ν
      ≤ ENNReal.ofReal (m + (⌊T / v⌋₊ + 1 : ℝ) * (((P.lam * (2 * v)) ^ 2 + P.lam * (2 * v)) / m)) := by
  have hμ : 0 ≤ (P.lam * (2 * v)) ^ 2 + P.lam * (2 * v) := by
    have := P.lam_nonneg; positivity
  calc ∫⁻ ω, ENNReal.ofReal (Mx S v T ω : ℝ) ∂S.ν
      ≤ ∫⁻ ω, (ENNReal.ofReal m + ∑ k ∈ Finset.range (⌊T / v⌋₊ + 1),
          ENNReal.ofReal ((Vk S v k ω : ℝ) ^ 2 / m)) ∂S.ν := by
        refine lintegral_mono (fun ω => ?_)
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => div_nonneg (sq_nonneg _) hm.le),
          ← ENNReal.ofReal_add hm.le (Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) hm.le))]
        exact ENNReal.ofReal_le_ofReal (Mx_le hv T hm ω)
    _ = ENNReal.ofReal m + ∑ k ∈ Finset.range (⌊T / v⌋₊ + 1),
          ∫⁻ ω, ENNReal.ofReal ((Vk S v k ω : ℝ) ^ 2 / m) ∂S.ν := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_finsetSum _ (fun k _ => by
            have h := Prop1.meas_N2 S (fun z : ℤ × ℤ => ENNReal.ofReal (((z.1 - z.2 : ℤ) : ℝ) ^ 2 / m))
              (((k : ℝ) + 1) * v) (((k : ℝ) - 1) * v)
            unfold Vk; exact h)]
    _ = ENNReal.ofReal m + ∑ k ∈ Finset.range (⌊T / v⌋₊ + 1),
          ENNReal.ofReal (((P.lam * (2 * v)) ^ 2 + P.lam * (2 * v)) / m) := by
        congr 1
        refine Finset.sum_congr rfl (fun k _ => ?_)
        have e : ∀ ω, ENNReal.ofReal ((Vk S v k ω : ℝ) ^ 2 / m)
            = ENNReal.ofReal m⁻¹ * ENNReal.ofReal ((Vk S v k ω : ℝ) ^ 2) := by
          intro ω
          rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hm.le), div_eq_mul_inv, mul_comm]
        rw [lintegral_congr e, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        unfold Vk
        rw [lintegral_sq_incr S (by nlinarith), ← ENNReal.ofReal_mul (inv_nonneg.mpr hm.le)]
        congr 1
        rw [show ((k : ℝ) + 1) * v - ((k : ℝ) - 1) * v = 2 * v by ring]
        field_simp
    _ = ENNReal.ofReal (m + (⌊T / v⌋₊ + 1 : ℝ) * (((P.lam * (2 * v)) ^ 2 + P.lam * (2 * v)) / m)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add hm.le (by positivity)]
        push_cast
        ring_nf

end Window

end Imp

end TwoStageRnQ

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace Imp

open TwoStageRnQ.LB

section Fields

variable {P : Params} {S : DemandSpace P} {Sb : ℤ} {ε : ℝ} (hε : 0 < ε)

local notation "πc" => pol (S := S) (Sb := Sb) hε

lemma meas_incr (S : DemandSpace P) (a b : ℝ) :
    Measurable (fun ω => ENNReal.ofReal ((S.N a ω - S.N b ω : ℤ) : ℝ)) := by
  have h := Prop1.meas_N2 S (fun z : ℤ × ℤ => ENNReal.ofReal ((z.1 - z.2 : ℤ) : ℝ)) a b
  exact h

lemma incr_real_nonneg (S : DemandSpace P) {a b : ℝ} (h : b ≤ a) (ω : S.Ω) :
    (0 : ℝ) ≤ ((S.N a ω - S.N b ω : ℤ) : ℝ) := by
  exact_mod_cast S.incr_nonneg h ω

include hε in
lemma adm_init (hSb : 0 ≤ Sb) :
    ∫⁻ ω, ENNReal.ofReal
      (|(netInv P.L1 (πc).x1 (πc).U1 S.N 0 ω : ℝ)| + |(netInv P.L2 (πc).x2 (πc).U2 S.N 0 ω : ℝ)|
        + (((πc).U1 0 ω - (πc).U1 (-P.L1) ω : ℤ) : ℝ) + (((πc).U2 0 ω - (πc).U2 (-P.L2) ω : ℤ) : ℝ))
      ∂S.ν < ⊤ := by
  have hS : (0 : ℝ) ≤ Sb := by exact_mod_cast hSb
  have hL1 := P.L1_nonneg
  have hL2 := P.L2_nonneg
  have hbound : ∀ ω, ENNReal.ofReal
      (|(netInv P.L1 (πc).x1 (πc).U1 S.N 0 ω : ℝ)| + |(netInv P.L2 (πc).x2 (πc).U2 S.N 0 ω : ℝ)|
        + (((πc).U1 0 ω - (πc).U1 (-P.L1) ω : ℤ) : ℝ) + (((πc).U2 0 ω - (πc).U2 (-P.L2) ω : ℤ) : ℝ))
      ≤ ENNReal.ofReal (2 * Sb)
        + ENNReal.ofReal 4 * ENNReal.ofReal ((S.N 0 ω - S.N (-(P.L1 + P.L2)) ω : ℤ) : ℝ) := by
    intro ω
    show ENNReal.ofReal (|((Sb + U1c S Sb ε (0 - P.L1) ω - S.N 0 ω : ℤ) : ℝ)|
        + |((Sb + S.N (0 - P.L2) ω - S.N 0 ω : ℤ) : ℝ)|
        + ((U1c S Sb ε 0 ω - U1c S Sb ε (-P.L1) ω : ℤ) : ℝ) + ((S.N 0 ω - S.N (-P.L2) ω : ℤ) : ℝ)) ≤ _
    have e1 : U1c S Sb ε (0 - P.L1) ω = S.N (min (-P.L1) (-P.L2)) ω := by
      rw [zero_sub]; exact U1c_nonpos (by linarith) ω
    have e1' : U1c S Sb ε (-P.L1) ω = S.N (min (-P.L1) (-P.L2)) ω := U1c_nonpos (by linarith) ω
    have e0 : U1c S Sb ε 0 ω = S.N (-P.L2) ω := U1c_zero hε ω
    have m1 : S.N (-(P.L1 + P.L2)) ω ≤ S.N (min (-P.L1) (-P.L2)) ω :=
      S.N_mono ω (le_min (by linarith) (by linarith))
    have m2 : S.N (min (-P.L1) (-P.L2)) ω ≤ S.N (-P.L2) ω := S.N_mono ω (min_le_right _ _)
    have m3 : S.N (-P.L2) ω ≤ S.N 0 ω := S.N_mono ω (by linarith)
    have m4 : S.N (0 - P.L2) ω = S.N (-P.L2) ω := by rw [zero_sub]
    have hz : |Sb + U1c S Sb ε (0 - P.L1) ω - S.N 0 ω| + |Sb + S.N (0 - P.L2) ω - S.N 0 ω|
        + (U1c S Sb ε 0 ω - U1c S Sb ε (-P.L1) ω) + (S.N 0 ω - S.N (-P.L2) ω)
        ≤ 2 * Sb + 4 * (S.N 0 ω - S.N (-(P.L1 + P.L2)) ω) := by
      rw [e1, e1', e0, m4]
      have a1 : |Sb + S.N (min (-P.L1) (-P.L2)) ω - S.N 0 ω|
          ≤ Sb + (S.N 0 ω - S.N (-(P.L1 + P.L2)) ω) := by
        rw [abs_le]; constructor <;> linarith
      have a2 : |Sb + S.N (-P.L2) ω - S.N 0 ω| ≤ Sb + (S.N 0 ω - S.N (-(P.L1 + P.L2)) ω) := by
        rw [abs_le]; constructor <;> linarith
      linarith
    have hr : |((Sb + U1c S Sb ε (0 - P.L1) ω - S.N 0 ω : ℤ) : ℝ)|
        + |((Sb + S.N (0 - P.L2) ω - S.N 0 ω : ℤ) : ℝ)|
        + ((U1c S Sb ε 0 ω - U1c S Sb ε (-P.L1) ω : ℤ) : ℝ) + ((S.N 0 ω - S.N (-P.L2) ω : ℤ) : ℝ)
        ≤ 2 * (Sb : ℝ) + 4 * ((S.N 0 ω - S.N (-(P.L1 + P.L2)) ω : ℤ) : ℝ) := by
      have := (Int.cast_le (R := ℝ)).mpr hz
      push_cast at this ⊢
      linarith
    have hD := incr_real_nonneg S (show -(P.L1 + P.L2) ≤ 0 by linarith) ω
    rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal hr
  refine lt_of_le_of_lt (lintegral_mono hbound) ?_
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_const_mul _ (meas_incr S _ _), S.lintegral_incr_val (by linarith)]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top⟩

include hε in
lemma adm_finite (hεL : ε ≤ P.L2) (hSb : 0 < Sb) {Φ : ℝ} (hΦ0 : 0 ≤ Φ)
    (hΦ : ∀ t, ∫⁻ ω, ENNReal.ofReal (phi P.h2 P.p ((Sb + S.N (t - P.L2) ω - S.N t ω : ℤ) : ℝ)) ∂S.ν
      ≤ ENNReal.ofReal Φ) :
    ∀ T : ℝ, 0 ≤ T →
      ∫⁻ ω, ((∫⁻ t in Set.Ioc 0 T, ENNReal.ofReal ((πc).cI t ω))
        + ENNReal.ofReal ((πc).shipSetup T ω)) ∂S.ν < ⊤ := fun T hT =>
  lt_of_le_of_lt (expected_total_le hε hεL hSb hΦ0 hΦ hT) ENNReal.ofReal_lt_top

include hε in

lemma backlog_le (hSb : 0 ≤ Sb) (T : ℝ) (ω : S.Ω) :
    max (-(netInv P.L1 (fun _ => Sb) (U1c S Sb ε) S.N T ω)) 0
      ≤ S.N T ω - S.N (T - (P.L1 + (ε + P.L2))) ω := by
  have h := IL1_ge (S := S) hε hSb T ω
  have h2 := S.incr_nonneg (show T - (P.L1 + (ε + P.L2)) ≤ T by
    linarith [P.L1_nonneg, P.L2_nonneg]) ω
  exact max_le (by linarith) h2

include hε in
lemma adm_rate_del (hSb : 0 ≤ Sb) :
    Tendsto (fun T : ℝ => ENNReal.ofReal T⁻¹ *
      ∫⁻ ω, ENNReal.ofReal (((πc).U0 T ω - (πc).U0 0 ω : ℤ) : ℝ) ∂S.ν) atTop
      (𝓝 (ENNReal.ofReal P.lam)) := by
  set W := P.L1 + (ε + P.L2) with hW
  have hW0 : 0 ≤ W := by have := P.L1_nonneg; have := P.L2_nonneg; positivity
  have hl := P.lam_nonneg
  refine ennreal_rate (B := P.lam * W) hl (mul_nonneg hl hW0) (fun T hT => ?_) (fun T hT => ?_)
  ·
    have hb : ∀ ω, ENNReal.ofReal (((πc).U0 T ω - (πc).U0 0 ω : ℤ) : ℝ)
        ≤ ENNReal.ofReal ((S.N T ω - S.N 0 ω : ℤ) : ℝ)
          + ENNReal.ofReal ((S.N 0 ω - S.N (0 - W) ω : ℤ) : ℝ) := by
      intro ω
      have b0 := backlog_le hε hSb 0 ω
      have bT : 0 ≤ max (-(netInv P.L1 (fun _ => Sb) (U1c S Sb ε) S.N T ω)) 0 := le_max_right _ _
      have hz : (πc).U0 T ω - (πc).U0 0 ω ≤ (S.N T ω - S.N 0 ω) + (S.N 0 ω - S.N (0 - W) ω) := by
        show (S.N T ω - max (-(netInv P.L1 (fun _ => Sb) (U1c S Sb ε) S.N T ω)) 0)
          - (S.N 0 ω - max (-(netInv P.L1 (fun _ => Sb) (U1c S Sb ε) S.N 0 ω)) 0) ≤ _
        linarith
      rw [← ENNReal.ofReal_add (incr_real_nonneg S hT ω)
        (incr_real_nonneg S (by linarith) ω)]
      apply ENNReal.ofReal_le_ofReal
      have := (Int.cast_le (R := ℝ)).mpr hz
      push_cast at this ⊢
      linarith
    calc _ ≤ ∫⁻ ω, (ENNReal.ofReal ((S.N T ω - S.N 0 ω : ℤ) : ℝ)
          + ENNReal.ofReal ((S.N 0 ω - S.N (0 - W) ω : ℤ) : ℝ)) ∂S.ν := lintegral_mono hb
      _ = ENNReal.ofReal (P.lam * T + P.lam * W) := by
          rw [lintegral_add_left (meas_incr S _ _), S.lintegral_incr_val hT,
            S.lintegral_incr_val (by linarith), ← ENNReal.ofReal_add (mul_nonneg hl (by linarith))
              (mul_nonneg hl (by linarith))]
          congr 1; ring
  ·
    have hb : ∀ ω, ENNReal.ofReal ((S.N T ω - S.N 0 ω : ℤ) : ℝ)
        ≤ ENNReal.ofReal (((πc).U0 T ω - (πc).U0 0 ω : ℤ) : ℝ)
          + ENNReal.ofReal ((S.N T ω - S.N (T - W) ω : ℤ) : ℝ) := by
      intro ω
      have bT := backlog_le hε hSb T ω
      have b0 : 0 ≤ max (-(netInv P.L1 (fun _ => Sb) (U1c S Sb ε) S.N 0 ω)) 0 := le_max_right _ _
      have hz : S.N T ω - S.N 0 ω ≤ ((πc).U0 T ω - (πc).U0 0 ω) + (S.N T ω - S.N (T - W) ω) := by
        show _ ≤ ((S.N T ω - max (-(netInv P.L1 (fun _ => Sb) (U1c S Sb ε) S.N T ω)) 0)
          - (S.N 0 ω - max (-(netInv P.L1 (fun _ => Sb) (U1c S Sb ε) S.N 0 ω)) 0)) + _
        linarith
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) (ENNReal.ofReal_add_le)
      have := (Int.cast_le (R := ℝ)).mpr hz
      push_cast at this ⊢
      linarith
    calc ENNReal.ofReal (P.lam * T) = ∫⁻ ω, ENNReal.ofReal ((S.N T ω - S.N 0 ω : ℤ) : ℝ) ∂S.ν := by
          rw [S.lintegral_incr_val hT, sub_zero]
      _ ≤ ∫⁻ ω, (ENNReal.ofReal (((πc).U0 T ω - (πc).U0 0 ω : ℤ) : ℝ)
          + ENNReal.ofReal ((S.N T ω - S.N (T - W) ω : ℤ) : ℝ)) ∂S.ν := lintegral_mono hb
      _ = _ := by
          rw [lintegral_add_right _ (meas_incr S _ _), S.lintegral_incr_val (by linarith)]
          congr 2; ring

include hε in
lemma adm_rate_U1 (hSb : 0 ≤ Sb) :
    Tendsto (fun T : ℝ => ENNReal.ofReal T⁻¹ *
      ∫⁻ ω, ENNReal.ofReal (((πc).U1 T ω - (πc).U1 0 ω : ℤ) : ℝ) ∂S.ν) atTop
      (𝓝 (ENNReal.ofReal P.lam)) := by
  have hl := P.lam_nonneg
  have hL2 := P.L2_nonneg
  have hS : (0 : ℝ) ≤ Sb := by exact_mod_cast hSb
  have hB : 0 ≤ (Sb : ℝ) + P.lam * (ε + P.L2) + P.lam * P.L2 := by positivity
  refine ennreal_rate hl hB (fun T hT => ?_) (fun T hT => ?_)
  · have hb : ∀ ω, ENNReal.ofReal (((πc).U1 T ω - (πc).U1 0 ω : ℤ) : ℝ)
        ≤ ENNReal.ofReal ((S.N (T - P.L2) ω - S.N (-P.L2) ω : ℤ) : ℝ) := by
      intro ω
      apply ENNReal.ofReal_le_ofReal
      have u1 := U1c_le (S := S) (Sb := Sb) hε hT ω
      have u0 := U1c_zero (S := S) (Sb := Sb) hε ω
      show (((U1c S Sb ε T ω - U1c S Sb ε 0 ω : ℤ) : ℝ)) ≤ _
      exact_mod_cast (by omega : U1c S Sb ε T ω - U1c S Sb ε 0 ω ≤ S.N (T - P.L2) ω - S.N (-P.L2) ω)
    calc _ ≤ ∫⁻ ω, ENNReal.ofReal ((S.N (T - P.L2) ω - S.N (-P.L2) ω : ℤ) : ℝ) ∂S.ν :=
          lintegral_mono hb
      _ = ENNReal.ofReal (P.lam * T) := by
          rw [S.lintegral_incr_val (by linarith)]; congr 1; ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  · have hb : ∀ ω, ENNReal.ofReal ((S.N T ω - S.N 0 ω : ℤ) : ℝ)
        ≤ ENNReal.ofReal (((πc).U1 T ω - (πc).U1 0 ω : ℤ) : ℝ)
          + (ENNReal.ofReal Sb + ENNReal.ofReal ((S.N T ω - S.N (T - (ε + P.L2)) ω : ℤ) : ℝ)
          + ENNReal.ofReal ((S.N 0 ω - S.N (-P.L2) ω : ℤ) : ℝ)) := by
      intro ω
      have u1 := U1c_ge (S := S) (Sb := Sb) hε hSb T ω
      have u0 := U1c_zero (S := S) (Sb := Sb) hε ω
      have mm : S.N (-P.L2) ω ≤ S.N 0 ω := S.N_mono ω (by linarith)
      have hz : S.N T ω - S.N 0 ω ≤ (U1c S Sb ε T ω - U1c S Sb ε 0 ω)
          + (Sb + (S.N T ω - S.N (T - (ε + P.L2)) ω) + (S.N 0 ω - S.N (-P.L2) ω)) := by omega
      have w1 := incr_real_nonneg S (show T - (ε + P.L2) ≤ T by linarith) ω
      have w2 := incr_real_nonneg S (show -P.L2 ≤ 0 by linarith) ω
      rw [← ENNReal.ofReal_add hS w1, ← ENNReal.ofReal_add (add_nonneg hS w1) w2]
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) (ENNReal.ofReal_add_le)
      have := (Int.cast_le (R := ℝ)).mpr hz
      push_cast at this ⊢
      show _ ≤ ((U1c S Sb ε T ω : ℤ) : ℝ) - ((U1c S Sb ε 0 ω : ℤ) : ℝ) + _
      linarith
    have hm : Measurable (fun ω => ENNReal.ofReal Sb
        + ENNReal.ofReal ((S.N T ω - S.N (T - (ε + P.L2)) ω : ℤ) : ℝ)
        + ENNReal.ofReal ((S.N 0 ω - S.N (-P.L2) ω : ℤ) : ℝ)) := by
      have h := ((measurable_const (a := ENNReal.ofReal (Sb : ℝ))).add
        (meas_incr S T (T - (ε + P.L2)))).add (meas_incr S 0 (-P.L2))
      exact h
    calc ENNReal.ofReal (P.lam * T) = ∫⁻ ω, ENNReal.ofReal ((S.N T ω - S.N 0 ω : ℤ) : ℝ) ∂S.ν := by
          rw [S.lintegral_incr_val hT, sub_zero]
      _ ≤ _ := lintegral_mono hb
      _ = _ := by
          have hm1 : Measurable (fun ω => ENNReal.ofReal Sb
              + ENNReal.ofReal ((S.N T ω - S.N (T - (ε + P.L2)) ω : ℤ) : ℝ)) := by
            have h := (measurable_const (a := ENNReal.ofReal Sb)).add (meas_incr S T (T - (ε + P.L2)))
            exact h
          rw [lintegral_add_right _ hm, lintegral_add_left hm1,
            lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            S.lintegral_incr_val (by linarith), S.lintegral_incr_val (by linarith),
            ← ENNReal.ofReal_add hS (mul_nonneg hl (by linarith)),
            ← ENNReal.ofReal_add (add_nonneg hS (mul_nonneg hl (by linarith)))
              (mul_nonneg hl (by linarith))]
          congr 2; ring

lemma adm_rate_U2 :
    Tendsto (fun T : ℝ => ENNReal.ofReal T⁻¹ *
      ∫⁻ ω, ENNReal.ofReal ((S.N T ω - S.N 0 ω : ℤ) : ℝ) ∂S.ν) atTop
      (𝓝 (ENNReal.ofReal P.lam)) := by
  have hl := P.lam_nonneg
  refine ennreal_rate (B := 0) hl le_rfl (fun T hT => ?_) (fun T hT => ?_)
  · rw [S.lintegral_incr_val hT, sub_zero, add_zero]
  · rw [S.lintegral_incr_val hT, sub_zero, ENNReal.ofReal_zero, add_zero]

include hε in
lemma adm_term1 (hSb : 0 ≤ Sb) :
    Tendsto (fun T : ℝ => ENNReal.ofReal T⁻¹ *
      ∫⁻ ω, ENNReal.ofReal (|(netInv P.L1 (πc).x1 (πc).U1 S.N T ω : ℝ)|
        + (((πc).U1 T ω - (πc).U1 (T - P.L1) ω : ℤ) : ℝ)) ∂S.ν) atTop (𝓝 0) := by
  set W := P.L1 + (ε + P.L2) with hW
  have hW0 : 0 ≤ W := by have := P.L1_nonneg; have := P.L2_nonneg; positivity
  have hS : (0 : ℝ) ≤ Sb := by exact_mod_cast hSb
  refine ennreal_o (B := 2 * Sb + 2 * (P.lam * W)) (fun T hT => ?_)
  have hb : ∀ ω, ENNReal.ofReal (|(netInv P.L1 (πc).x1 (πc).U1 S.N T ω : ℝ)|
        + (((πc).U1 T ω - (πc).U1 (T - P.L1) ω : ℤ) : ℝ))
      ≤ ENNReal.ofReal (2 * Sb) + ENNReal.ofReal 2 * ENNReal.ofReal ((S.N T ω - S.N (T - W) ω : ℤ) : ℝ) := by
    intro ω
    have i1 := IL1_ge (S := S) hε hSb T ω
    have i2 := IL1_le (S := S) (Sb := Sb) hε T ω
    have u1 := U1c_le_N (S := S) (Sb := Sb) hε T ω
    have u2 := U1c_ge (S := S) (Sb := Sb) hε hSb (T - P.L1) ω
    have e : T - P.L1 - (ε + P.L2) = T - W := by rw [hW]; ring
    rw [e] at u2
    rw [← hW] at i1
    have hDz : 0 ≤ S.N T ω - S.N (T - W) ω := S.incr_nonneg (by linarith) ω
    have hD := incr_real_nonneg S (show T - W ≤ T by linarith) ω
    show ENNReal.ofReal (|((netInv P.L1 (fun _ => Sb) (U1c S Sb ε) S.N T ω : ℤ) : ℝ)|
        + ((U1c S Sb ε T ω - U1c S Sb ε (T - P.L1) ω : ℤ) : ℝ)) ≤ _
    rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have a1 : |netInv P.L1 (fun _ => Sb) (U1c S Sb ε) S.N T ω| ≤ Sb + (S.N T ω - S.N (T - W) ω) := by
      rw [abs_le]; constructor <;> linarith
    have hz : |netInv P.L1 (fun _ => Sb) (U1c S Sb ε) S.N T ω|
        + (U1c S Sb ε T ω - U1c S Sb ε (T - P.L1) ω) ≤ 2 * Sb + 2 * (S.N T ω - S.N (T - W) ω) := by
      linarith
    have := (Int.cast_le (R := ℝ)).mpr hz
    push_cast at this ⊢
    linarith
  calc _ ≤ ∫⁻ ω, (ENNReal.ofReal (2 * Sb)
        + ENNReal.ofReal 2 * ENNReal.ofReal ((S.N T ω - S.N (T - W) ω : ℤ) : ℝ)) ∂S.ν :=
        lintegral_mono hb
    _ = ENNReal.ofReal (2 * Sb + 2 * (P.lam * W)) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ (meas_incr S _ _), S.lintegral_incr_val (by linarith),
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
            (mul_nonneg (by norm_num) (mul_nonneg P.lam_nonneg (by linarith)))]
        congr 1; ring

lemma adm_term2 (hSb : 0 ≤ Sb) :
    Tendsto (fun T : ℝ => ENNReal.ofReal T⁻¹ *
      ∫⁻ ω, ENNReal.ofReal (|(netInv P.L2 (fun _ => Sb) S.N S.N T ω : ℝ)|
        + ((S.N T ω - S.N (T - P.L2) ω : ℤ) : ℝ)) ∂S.ν) atTop (𝓝 0) := by
  have hS : (0 : ℝ) ≤ Sb := by exact_mod_cast hSb
  have hL2 := P.L2_nonneg
  refine ennreal_o (B := Sb + 2 * (P.lam * P.L2)) (fun T hT => ?_)
  have hb : ∀ ω, ENNReal.ofReal (|(netInv P.L2 (fun _ => Sb) S.N S.N T ω : ℝ)|
        + ((S.N T ω - S.N (T - P.L2) ω : ℤ) : ℝ))
      ≤ ENNReal.ofReal Sb + ENNReal.ofReal 2 * ENNReal.ofReal ((S.N T ω - S.N (T - P.L2) ω : ℤ) : ℝ) := by
    intro ω
    have hD := incr_real_nonneg S (show T - P.L2 ≤ T by linarith) ω
    have m := S.N_mono ω (show T - P.L2 ≤ T by linarith)
    rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add hS (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    unfold netInv
    simp only at m ⊢
    have a1 : |Sb + S.N (T - P.L2) ω - S.N T ω| ≤ Sb + (S.N T ω - S.N (T - P.L2) ω) := by
      rw [abs_le]; constructor <;> linarith
    have := (Int.cast_le (R := ℝ)).mpr a1
    push_cast at this ⊢
    linarith
  calc _ ≤ ∫⁻ ω, (ENNReal.ofReal Sb
        + ENNReal.ofReal 2 * ENNReal.ofReal ((S.N T ω - S.N (T - P.L2) ω : ℤ) : ℝ)) ∂S.ν :=
        lintegral_mono hb
    _ = ENNReal.ofReal (Sb + 2 * (P.lam * P.L2)) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ (meas_incr S _ _), S.lintegral_incr_val (by linarith),
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add hS
            (mul_nonneg (by norm_num) (mul_nonneg P.lam_nonneg (by linarith)))]
        congr 1; ring

include hε in
lemma adm_wcost (hSb : 0 ≤ Sb) {Φ : ℝ} (hΦ0 : 0 ≤ Φ)
    (hΦ : ∀ t, ∫⁻ ω, ENNReal.ofReal (phi P.h2 P.p ((Sb + S.N (t - P.L2) ω - S.N t ω : ℤ) : ℝ)) ∂S.ν
      ≤ ENNReal.ofReal Φ) :
    Tendsto (fun T : ℝ => ENNReal.ofReal T⁻¹ *
      ∫⁻ ω, (∫⁻ t in Set.Ioc T (T + (P.L1 + P.L2)), ENNReal.ofReal ((πc).cI t ω)) ∂S.ν)
      atTop (𝓝 0) := by
  refine ennreal_o (B := (Φ + P.h1 * Sb + 4 * (P.h2 + P.p) * P.lam * ε) * (P.L1 + P.L2)
    + (P.h2 + P.p) * (P.L1 * (Sb + P.lam * ((P.L1 + P.L2) + P.L1 + ε)))) (fun T hT => ?_)
  refine (lintegral_cost_le hε hSb hΦ0 hΦ hT (by linarith [P.L1_nonneg, P.L2_nonneg])).trans
    (le_of_eq ?_)
  congr 1; ring

include hε in
lemma adm_wU1 (hSb : 0 ≤ Sb) :
    Tendsto (fun T : ℝ => ENNReal.ofReal T⁻¹ *
      ∫⁻ ω, ENNReal.ofReal (((πc).U1 (T + (P.L1 + P.L2)) ω - (πc).U1 T ω : ℤ) : ℝ) ∂S.ν)
      atTop (𝓝 0) := by
  set w := P.L1 + P.L2 with hw
  have hw0 : 0 ≤ w := by have := P.L1_nonneg; have := P.L2_nonneg; positivity
  have hS : (0 : ℝ) ≤ Sb := by exact_mod_cast hSb
  refine ennreal_o (B := Sb + P.lam * (w + (ε + P.L2))) (fun T hT => ?_)
  have hb : ∀ ω, ENNReal.ofReal (((πc).U1 (T + w) ω - (πc).U1 T ω : ℤ) : ℝ)
      ≤ ENNReal.ofReal Sb + ENNReal.ofReal ((S.N (T + w) ω - S.N (T - (ε + P.L2)) ω : ℤ) : ℝ) := by
    intro ω
    have u1 := U1c_le_N (S := S) (Sb := Sb) hε (T + w) ω
    have u2 := U1c_ge (S := S) (Sb := Sb) hε hSb T ω
    have hD := incr_real_nonneg S (show T - (ε + P.L2) ≤ T + w by linarith [P.L2_nonneg]) ω
    rw [← ENNReal.ofReal_add hS hD]
    apply ENNReal.ofReal_le_ofReal
    have hz : U1c S Sb ε (T + w) ω - U1c S Sb ε T ω
        ≤ Sb + (S.N (T + w) ω - S.N (T - (ε + P.L2)) ω) := by omega
    have := (Int.cast_le (R := ℝ)).mpr hz
    push_cast at this ⊢
    show ((U1c S Sb ε (T + w) ω : ℤ) : ℝ) - ((U1c S Sb ε T ω : ℤ) : ℝ) ≤ _
    linarith
  calc _ ≤ ∫⁻ ω, (ENNReal.ofReal Sb
        + ENNReal.ofReal ((S.N (T + w) ω - S.N (T - (ε + P.L2)) ω : ℤ) : ℝ)) ∂S.ν := lintegral_mono hb
    _ = ENNReal.ofReal (Sb + P.lam * (w + (ε + P.L2))) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          S.lintegral_incr_val (by linarith [P.L2_nonneg]), ← ENNReal.ofReal_add hS
            (mul_nonneg P.lam_nonneg (by linarith [P.L2_nonneg]))]
        congr 2; ring

lemma adm_wU2 :
    Tendsto (fun T : ℝ => ENNReal.ofReal T⁻¹ *
      ∫⁻ ω, ENNReal.ofReal ((S.N (T + (P.L1 + P.L2)) ω - S.N T ω : ℤ) : ℝ) ∂S.ν)
      atTop (𝓝 0) := by
  refine ennreal_o (B := P.lam * (P.L1 + P.L2)) (fun T hT => ?_)
  rw [S.lintegral_incr_val (by linarith [P.L1_nonneg, P.L2_nonneg])]
  apply le_of_eq; congr 1; ring

include hε in
lemma adm_unf1 (hSb : 0 ≤ Sb) :
    Tendsto (fun T : ℝ => ENNReal.ofReal T⁻¹ *
      ∫⁻ ω, (unfinishedCount ((πc).x1 ω) (fun t => (πc).U1 t ω) (fun t => S.N t ω) T : ℝ≥0∞) ∂S.ν)
      atTop (𝓝 0) := by
  show Tendsto (fun T : ℝ => ENNReal.ofReal T⁻¹ *
      ∫⁻ ω, (unfinishedCount Sb (fun t => U1c S Sb ε t ω) (fun t => S.N t ω) T : ℝ≥0∞) ∂S.ν)
      atTop (𝓝 0)
  set v := 2 * ε + P.L2 with hv
  have hL2 := P.L2_nonneg
  have hv0 : 0 < v := by linarith
  set c := (P.lam * (2 * v)) ^ 2 + P.lam * (2 * v) with hc
  have hc0 : 0 ≤ c := by have := P.lam_nonneg; positivity
  have hS : (0 : ℝ) ≤ Sb := by exact_mod_cast hSb
  refine ennreal_o' (g := fun T => (Sb : ℝ) + √T + ((c / v) * T + c) / √T) ?_
    (tendsto_sqrt_bound _ _ _)
  filter_upwards [eventually_gt_atTop 0] with T hT
  have hsq : 0 < √T := Real.sqrt_pos.mpr hT
  have hpath : ∀ ω, (unfinishedCount Sb (fun t => U1c S Sb ε t ω) (fun t => S.N t ω) T : ℝ≥0∞)
      ≤ ENNReal.ofReal Sb + ENNReal.ofReal (Mx S v T ω : ℝ) := by
    intro ω
    have hU : Monotone (fun t => U1c S Sb ε t ω) := U1c_mono hε ω
    have hUr : RCont (fun t => U1c S Sb ε t ω) := U1c_rcont hε ω
    have hN : Monotone (fun t => S.N t ω) := S.N_mono ω
    have hNr : RCont (fun t => S.N t ω) := S.N_rcont ω
    have hb := unfinished_le Sb (fun t => U1c S Sb ε t ω) (fun t => S.N t ω) hU hUr hN hNr hT.le
      (-(Mx S v T ω : ℤ)) Sb ?_ ?_ ?_ ?_
    · have hz : (unfinishedCount Sb (fun t => U1c S Sb ε t ω) (fun t => S.N t ω) T : ℤ)
          ≤ Sb + (Mx S v T ω : ℤ) := by
        have h0 : 0 ≤ Sb - -(Mx S v T ω : ℤ) := by omega
        have := Int.toNat_of_nonneg h0
        omega
      rw [← ENNReal.ofReal_natCast]
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) ENNReal.ofReal_add_le
      have := (Int.cast_le (R := ℝ)).mpr hz
      push_cast at this
      exact this
    · have w0 := window_le_Mx (S := S) hv0 (τ := 0) le_rfl hT.le ω
      have u0 := U1c_zero (S := S) (Sb := Sb) hε ω
      have m1 : S.N (0 - v) ω ≤ S.N (-P.L2) ω := S.N_mono ω (by linarith)
      have m2 : S.N (-P.L2) ω ≤ S.N 0 ω := S.N_mono ω (by linarith)
      constructor <;> omega
    · intro τ hτ
      have w1 := window_le_Mx (S := S) hv0 hτ.1.le hτ.2 ω
      have l1 := le_lv hU (show τ - ε < τ by linarith)
      have g1 := U1c_ge (S := S) (Sb := Sb) hε hSb (τ - ε) ω
      have e : τ - ε - (ε + P.L2) = τ - v := by rw [hv]; ring
      rw [e] at g1
      omega
    · intro τ _
      obtain ⟨s, hs, he⟩ := lv_mem hU τ
      have h1 := U1c_le_N (S := S) (Sb := Sb) hε s ω
      have h2 := le_lv hN hs
      omega
    · intro τ _
      have := U1c_le_N (S := S) (Sb := Sb) hε τ ω
      omega
  calc ∫⁻ ω, (unfinishedCount Sb (fun t => U1c S Sb ε t ω) (fun t => S.N t ω) T : ℝ≥0∞) ∂S.ν
      ≤ ∫⁻ ω, (ENNReal.ofReal Sb + ENNReal.ofReal (Mx S v T ω : ℝ)) ∂S.ν := lintegral_mono hpath
    _ = ENNReal.ofReal Sb + ∫⁻ ω, ENNReal.ofReal (Mx S v T ω : ℝ) ∂S.ν := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal Sb + ENNReal.ofReal (√T + (⌊T / v⌋₊ + 1 : ℝ) * (c / √T)) := by
        gcongr
        exact lintegral_Mx_le hv0 T hsq
    _ ≤ ENNReal.ofReal ((Sb : ℝ) + √T + ((c / v) * T + c) / √T) := by
        rw [← ENNReal.ofReal_add hS (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hfl : (⌊T / v⌋₊ : ℝ) ≤ T / v := Nat.floor_le (div_nonneg hT.le hv0.le)
        have : (⌊T / v⌋₊ + 1 : ℝ) * (c / √T) ≤ (T / v + 1) * (c / √T) :=
          mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hc0 hsq.le)
        have e : (T / v + 1) * (c / √T) = ((c / v) * T + c) / √T := by field_simp
        linarith

include hε in
lemma adm_unf2 (hSb : 0 ≤ Sb) :
    Tendsto (fun T : ℝ => ENNReal.ofReal T⁻¹ *
      ∫⁻ ω, (unfinishedCount ((πc).x2 ω) (fun t => (πc).U2 t ω) (fun t => S.N t ω) T : ℝ≥0∞) ∂S.ν)
      atTop (𝓝 0) := by
  show Tendsto (fun T : ℝ => ENNReal.ofReal T⁻¹ *
      ∫⁻ ω, (unfinishedCount Sb (fun t => S.N t ω) (fun t => S.N t ω) T : ℝ≥0∞) ∂S.ν)
      atTop (𝓝 0)
  set v := 2 * ε + P.L2 with hv
  have hL2 := P.L2_nonneg
  have hv0 : 0 < v := by linarith
  set c := (P.lam * (2 * v)) ^ 2 + P.lam * (2 * v) with hc
  have hc0 : 0 ≤ c := by have := P.lam_nonneg; positivity
  have hS : (0 : ℝ) ≤ Sb := by exact_mod_cast hSb
  refine ennreal_o' (g := fun T => (Sb : ℝ) + √T + ((c / v) * T + c) / √T) ?_
    (tendsto_sqrt_bound _ _ _)
  filter_upwards [eventually_gt_atTop 0] with T hT
  have hsq : 0 < √T := Real.sqrt_pos.mpr hT
  have hpath : ∀ ω, (unfinishedCount Sb (fun t => S.N t ω) (fun t => S.N t ω) T : ℝ≥0∞)
      ≤ ENNReal.ofReal (Mx S v T ω : ℝ) := by
    intro ω
    have hN : Monotone (fun t => S.N t ω) := S.N_mono ω
    have hNr : RCont (fun t => S.N t ω) := S.N_rcont ω
    have hb := unfinished_le Sb (fun t => S.N t ω) (fun t => S.N t ω) hN hNr hN hNr hT.le
      (Sb - (Mx S v T ω : ℤ)) Sb ?_ ?_ ?_ ?_
    · have hz : (unfinishedCount Sb (fun t => S.N t ω) (fun t => S.N t ω) T : ℤ)
          ≤ (Mx S v T ω : ℤ) := by
        have h0 : 0 ≤ Sb - (Sb - (Mx S v T ω : ℤ)) := by omega
        have := Int.toNat_of_nonneg h0
        omega
      rw [← ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_le_ofReal
      exact_mod_cast hz
    · skip
      constructor <;> omega
    · intro τ hτ
      have w1 := window_le_Mx (S := S) hv0 hτ.1.le hτ.2 ω
      have l1 := le_lv hN (show τ - v < τ by linarith)
      omega
    · intro τ _
      omega
    · intro τ _
      omega
  calc ∫⁻ ω, (unfinishedCount Sb (fun t => S.N t ω) (fun t => S.N t ω) T : ℝ≥0∞) ∂S.ν
      ≤ ∫⁻ ω, ENNReal.ofReal (Mx S v T ω : ℝ) ∂S.ν := lintegral_mono hpath
    _ ≤ ENNReal.ofReal (√T + (⌊T / v⌋₊ + 1 : ℝ) * (c / √T)) := lintegral_Mx_le hv0 T hsq
    _ ≤ ENNReal.ofReal ((Sb : ℝ) + √T + ((c / v) * T + c) / √T) := by
        apply ENNReal.ofReal_le_ofReal
        have hfl : (⌊T / v⌋₊ : ℝ) ≤ T / v := Nat.floor_le (div_nonneg hT.le hv0.le)
        have : (⌊T / v⌋₊ + 1 : ℝ) * (c / √T) ≤ (T / v + 1) * (c / √T) :=
          mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hc0 hsq.le)
        have e : (T / v + 1) * (c / √T) = ((c / v) * T + c) / √T := by field_simp
        linarith

theorem pol_admissible (hεL : ε ≤ P.L2) (hSb : 0 < Sb) {Φ : ℝ} (hΦ0 : 0 ≤ Φ)
    (hΦ : ∀ t, ∫⁻ ω, ENNReal.ofReal (phi P.h2 P.p ((Sb + S.N (t - P.L2) ω - S.N t ω : ℤ) : ℝ)) ∂S.ν
      ≤ ENNReal.ofReal Φ) :
    (πc).Admissible (πc).shipSetup where
  init_moments := adm_init hε hSb.le
  finite_horizon := adm_finite hε hεL hSb hΦ0 hΦ
  rate_deliveries := adm_rate_del hε hSb.le
  rate_U1 := adm_rate_U1 hε hSb.le
  rate_U2 := adm_rate_U2
  terminal_1 := adm_term1 hε hSb.le
  terminal_2 := adm_term2 hSb.le
  window_cost := adm_wcost hε hSb.le hΦ0 hΦ
  window_U1 := adm_wU1 hε hSb.le
  window_U2 := adm_wU2
  unfinished_1 := adm_unf1 hε hSb.le
  unfinished_2 := adm_unf2 hε hSb.le

end Fields

end Imp

end TwoStageRnQ

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace Imp

section Instance

lemma hh_le_inv_sq {s : ℕ} (h2 : 2 ≤ s) : hh s ≤ 1 / (s : ℝ) ^ 2 := by
  unfold hh poisW
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast h2
  have hs0 : (0 : ℝ) < s := by linarith
  have hμ : 0 ≤ 1 / (s : ℝ) := by positivity
  have hμ1 : 1 / (s : ℝ) ≤ 1 := by rw [div_le_one hs0]; linarith
  have he : Real.exp (-(1 / (s : ℝ))) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hf : (1 : ℝ) ≤ (s.factorial : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero s)
  have hp : (1 / (s : ℝ)) ^ s ≤ (1 / (s : ℝ)) ^ 2 := pow_le_pow_of_le_one hμ hμ1 h2
  have hX : 0 ≤ Real.exp (-(1 / (s : ℝ))) * (1 / (s : ℝ)) ^ s := by positivity
  calc Real.exp (-(1 / (s : ℝ))) * (1 / (s : ℝ)) ^ s / (s.factorial : ℝ)
      ≤ Real.exp (-(1 / (s : ℝ))) * (1 / (s : ℝ)) ^ s := div_le_self hX hf
    _ ≤ 1 * (1 / (s : ℝ)) ^ s := mul_le_mul_of_nonneg_right he (by positivity)
    _ ≤ (1 / (s : ℝ)) ^ 2 := by rw [one_mul]; exact hp
    _ = 1 / (s : ℝ) ^ 2 := by rw [div_pow, one_pow]

lemma costA_Pimp {s : ℕ} (hs : 30 ≤ s) (hs0 : 0 < s) :
    costA (Pimp s hs0) (s : ℤ) (hh s / 4)
        (hh s * s + hh s * ((1 / (s : ℝ)) / (1 - 1 / (s : ℝ)) ^ 2))
      ≤ hh s * ((1 + alp) * s + 5) := by
  have hsR : (30 : ℝ) ≤ s := by exact_mod_cast hs
  have hx0 : (0 : ℝ) < s := by linarith
  have hH := hh_pos hs0
  have hHle := hh_le_inv_sq (s := s) (by omega)
  have ha0 := alp_pos
  have ha1 := alp_le_half
  set H := hh s with hHdef
  set x : ℝ := (s : ℝ) with hx
  have hxH : x ^ 2 * H ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hHle
    linarith
  have hH900 : H ≤ 1 / 900 := by
    have : 1 / x ^ 2 ≤ 1 / 900 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hq : (1 / x) / (1 - 1 / x) ^ 2 ≤ 1 / 10 := by
    have h1 : 1 / x ≤ 1 / 30 := by
      rw [div_le_div_iff₀ hx0 (by norm_num)]; linarith
    have h2 : (29 / 30 : ℝ) ≤ 1 - 1 / x := by linarith
    have h3 : (0 : ℝ) < (1 - 1 / x) ^ 2 := by nlinarith
    rw [div_le_iff₀ h3]
    nlinarith
  have hcast : ((s : ℤ) : ℝ) = x := by rw [hx]; push_cast; ring
  unfold costA
  simp only [Pimp]
  rw [hcast]
  have a1 : H / x * x = H := by field_simp
  have a2 : alp * H * x ^ 2 * (1 + 1 ^ 2 * (2 * (1 / x) + x * (H / 4))) / x
      = alp * H * (x + 2 + x ^ 2 * H / 4) := by field_simp; ring
  rw [a1, a2]
  have hprod : alp * (x ^ 2 * H) ≤ 1 / 2 := by nlinarith
  have hbr : x + (1 / x) / (1 - 1 / x) ^ 2 + 1 + (H + 1) + (H + 1) / 4
      + alp * (x + 2 + x ^ 2 * H / 4) + 1 ≤ (1 + alp) * x + 5 := by
    nlinarith
  have := mul_le_mul_of_nonneg_left hbr hH.le
  nlinarith

end Instance

theorem impossibility_main (r : ℝ) (hr : r < (1 + Real.sqrt 3) / 2) :
    ∃ P : Params, 0 < P.lam ∧ 0 < P.L1 ∧ 0 < P.L2 ∧ 0 < P.h1 ∧ 0 < P.h2 ∧ 0 < P.p ∧
      0 < P.K1 ∧ 0 < P.K2 ∧
      ∀ S : DemandSpace P,
        ENNReal.ofReal r * OPTsh P < ⨅ c : ClassicalControls, classicalShipCost P S c ∧
        ENNReal.ofReal r * OPTsh P < ⨅ c : ClassicalControls, classicalLotCost P S c := by
  set r' := max r 0 with hr'
  have hr'0 : 0 ≤ r' := le_max_right _ _
  have hrr' : r ≤ r' := le_max_left _ _
  have hsq := sqrt3_gt
  have hsq2 := sqrt3_lt_two
  have hsq3 := sqrt3_sq
  have hδ : 0 < Real.sqrt 3 - r' * (1 + alp) := by
    have hr'lt : r' < (1 + Real.sqrt 3) / 2 := max_lt hr (by linarith)
    unfold alp
    have e : (1 + Real.sqrt 3) / 2 * (3 - Real.sqrt 3) = Real.sqrt 3 := by nlinarith
    have h3 : 0 < 3 - Real.sqrt 3 := by linarith
    have : r' * (3 - Real.sqrt 3) < (1 + Real.sqrt 3) / 2 * (3 - Real.sqrt 3) :=
      mul_lt_mul_of_pos_right hr'lt h3
    have e2 : 1 + (2 - Real.sqrt 3) = 3 - Real.sqrt 3 := by ring
    rw [e2]
    linarith
  set δ := Real.sqrt 3 - r' * (1 + alp) with hδdef
  obtain ⟨s, hs30, hsδ⟩ : ∃ s : ℕ, 30 ≤ s ∧ 5 * r' + 3 < δ * s := by
    set N0 : ℕ := max 30 (⌈(5 * r' + 3) / δ⌉₊ + 1) with hN0
    refine ⟨N0, le_max_left _ _, ?_⟩
    have h1 : ((⌈(5 * r' + 3) / δ⌉₊ + 1 : ℕ) : ℝ) ≤ (N0 : ℝ) := by
      exact_mod_cast le_max_right _ _
    have h2 : (5 * r' + 3) / δ ≤ ⌈(5 * r' + 3) / δ⌉₊ := Nat.le_ceil _
    have h1' : (⌈(5 * r' + 3) / δ⌉₊ : ℝ) + 1 ≤ (N0 : ℝ) := by
      have := h1; push_cast at this; exact this
    have h3 : (5 * r' + 3) / δ < (N0 : ℝ) := by linarith
    rw [div_lt_iff₀ hδ] at h3
    linarith
  have hs0 : 0 < s := by omega
  have hsR : (30 : ℝ) ≤ s := by exact_mod_cast hs30
  have hH := hh_pos hs0
  refine ⟨Pimp s hs0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (0 : ℝ) < 1; norm_num
  · show 0 < hh s / 4; exact div_pos hH (by norm_num)
  · show 0 < 1 / (s : ℝ); positivity
  · show 0 < hh s / s; exact div_pos hH (by exact_mod_cast hs0)
  · exact hH
  · show (0 : ℝ) < 1; norm_num
  · show 0 < alp * hh s * (s : ℝ) ^ 2; have := alp_pos; positivity
  · exact hH
  intro S

  have hlb : ENNReal.ofReal (hh s * (Real.sqrt 3 * s - 5 / 2 - 1 / s))
      ≤ ⨅ c : ClassicalControls, classicalShipCost (Pimp s hs0) S c := by
    refine le_iInf (fun c => ?_)
    obtain ⟨m, hm, σ, h⟩ := classical_ship_lb S (show (0 : ℝ) < (Pimp s hs0).lam by
      show (0 : ℝ) < 1; norm_num) c
    exact (ENNReal.ofReal_le_ofReal (cyc_lb hs30 m hm σ)).trans h

  have hε : 0 < hh s / 4 := div_pos hH (by norm_num)
  have hHle := hh_le_inv_sq (s := s) (by omega)
  have hεL : hh s / 4 ≤ (Pimp s hs0).L2 := by
    show hh s / 4 ≤ 1 / (s : ℝ)
    have : 1 / (s : ℝ) ^ 2 ≤ 4 / s := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have : 1 / (s : ℝ) ^ 2 / 4 ≤ 1 / s := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
      calc 1 / (s : ℝ) ^ 2 ≤ 4 / s := this
        _ = 1 / s * 4 := by ring
    linarith [div_le_div_of_nonneg_right hHle (by norm_num : (0 : ℝ) ≤ 4)]
  have hSb : (0 : ℤ) < (s : ℤ) := by exact_mod_cast hs0
  set Φ := hh s * s + hh s * ((1 / (s : ℝ)) / (1 - 1 / (s : ℝ)) ^ 2) with hΦdef
  have hq0 : 0 ≤ (1 / (s : ℝ)) / (1 - 1 / (s : ℝ)) ^ 2 := by positivity
  have hΦ0 : 0 ≤ Φ := by positivity
  have hΦ : ∀ t, ∫⁻ ω, ENNReal.ofReal (phi (Pimp s hs0).h2 (Pimp s hs0).p
      ((((s : ℕ) : ℤ) + S.N (t - (Pimp s hs0).L2) ω - S.N t ω : ℤ) : ℝ)) ∂S.ν
      ≤ ENNReal.ofReal Φ := by
    intro t
    have hμ : (Pimp s hs0).lam * (t - (t - (Pimp s hs0).L2)) = 1 / (s : ℝ) := by
      show (1 : ℝ) * (t - (t - 1 / (s : ℝ))) = 1 / s; ring
    have hμ1 : (Pimp s hs0).lam * (t - (t - (Pimp s hs0).L2)) < 1 := by
      rw [hμ, div_lt_one (by positivity)]; linarith
    have h := lintegral_phi_incr_le S (show t - (Pimp s hs0).L2 ≤ t by
      linarith [(Pimp s hs0).L2_nonneg]) s hμ1
    have e : ∀ ω, ENNReal.ofReal (phi (Pimp s hs0).h2 (Pimp s hs0).p
        ((((s : ℕ) : ℤ) + S.N (t - (Pimp s hs0).L2) ω - S.N t ω : ℤ) : ℝ))
        = ENNReal.ofReal (phi (Pimp s hs0).h2 (Pimp s hs0).p
          ((((s : ℕ) : ℤ) - (S.N t ω - S.N (t - (Pimp s hs0).L2) ω) : ℤ) : ℝ)) := by
      intro ω
      rw [show ((s : ℕ) : ℤ) + S.N (t - (Pimp s hs0).L2) ω - S.N t ω
        = ((s : ℕ) : ℤ) - (S.N t ω - S.N (t - (Pimp s hs0).L2) ω) by ring]
    rw [lintegral_congr e]
    refine h.trans (le_of_eq ?_)
    rw [hμ]
    show ENNReal.ofReal (hh s * s + 1 * (poisW (1 / (s : ℝ)) s
      * (1 / (s : ℝ) / (1 - 1 / (s : ℝ)) ^ 2))) = ENNReal.ofReal Φ
    rw [hΦdef, one_mul]
    rfl
  have hadm := pol_admissible (S := S) (Sb := (s : ℤ)) hε hεL hSb hΦ0 hΦ
  have hcost := shipCost_pol_le (S := S) (Sb := (s : ℤ)) hε hεL hSb hΦ0 hΦ
  have hopt : OPTsh (Pimp s hs0) ≤ ENNReal.ofReal (costA (Pimp s hs0) (s : ℤ) (hh s / 4) Φ) :=
    (iInf_le_of_le S (iInf_le_of_le (pol (S := S) (Sb := (s : ℤ)) hε)
      (iInf_le_of_le hadm le_rfl))).trans hcost
  have hA := costA_Pimp hs30 hs0
  have h1s : 1 / (s : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hpos : 0 < hh s * (Real.sqrt 3 * s - 5 / 2 - 1 / s) := by
    apply mul_pos hH
    nlinarith
  have hkey : r' * (hh s * ((1 + alp) * s + 5)) < hh s * (Real.sqrt 3 * s - 5 / 2 - 1 / s) := by
    have hin : r' * ((1 + alp) * s + 5) < Real.sqrt 3 * s - 5 / 2 - 1 / s := by
      rw [hδdef] at hsδ
      nlinarith
    have := mul_lt_mul_of_pos_left hin hH
    nlinarith
  have hmain : ENNReal.ofReal r * OPTsh (Pimp s hs0)
      < ENNReal.ofReal (hh s * (Real.sqrt 3 * s - 5 / 2 - 1 / s)) := by
    calc ENNReal.ofReal r * OPTsh (Pimp s hs0)
        ≤ ENNReal.ofReal r' * ENNReal.ofReal (hh s * ((1 + alp) * s + 5)) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hrr') (hopt.trans (ENNReal.ofReal_le_ofReal hA))
      _ = ENNReal.ofReal (r' * (hh s * ((1 + alp) * s + 5))) := (ENNReal.ofReal_mul hr'0).symm
      _ < _ := (ENNReal.ofReal_lt_ofReal_iff hpos).mpr hkey
  exact ⟨lt_of_lt_of_le hmain hlb, lt_of_lt_of_le hmain
    (hlb.trans (iInf_mono (fun c => classical_ship_le_lot_pf (Pimp s hs0) S c)))⟩

end Imp

end TwoStageRnQ

namespace TwoStageRnQ

theorem _root_.solution (r : ℝ) (hr : r < (1 + Real.sqrt 3) / 2) :
    ∃ P : Params, 0 < P.lam ∧ 0 < P.L1 ∧ 0 < P.L2 ∧ 0 < P.h1 ∧ 0 < P.h2 ∧ 0 < P.p ∧
      0 < P.K1 ∧ 0 < P.K2 ∧
      ∀ S : DemandSpace P,
        ENNReal.ofReal r * OPTsh P < ⨅ c : ClassicalControls, classicalShipCost P S c ∧
        ENNReal.ofReal r * OPTsh P < ⨅ c : ClassicalControls, classicalLotCost P S c :=
  Imp.impossibility_main r hr

end TwoStageRnQ
