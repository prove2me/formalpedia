-- Prove2me | solution 1 for TwoStageRnQ.LBsp_le_OPTsh
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T00:27:17.582786+00:00
-- url     : https://prove2.me/submissions/59dbb90c-cc21-4281-8f2c-d2afc3910041

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
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Infix
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Card
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Data.Real.Pointwise
import Mathlib.Analysis.Normed.Ring.InfiniteSum

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

end Params

lemma latAvg_nonneg {j : ℕ} {F : ℝ → ℝ} (hF : ∀ x, 0 ≤ F x) (x : ℝ) : 0 ≤ latAvg j F x := by
  unfold latAvg; exact div_nonneg (Finset.sum_nonneg (fun v _ => hF _)) (Nat.cast_nonneg j)

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

lemma pcost_nonneg (hF : ∀ x, 0 ≤ F x) (hk : 0 ≤ k) (l : List ℤ) : 0 ≤ pcost F k l := by
  rw [pcost_eq]
  have h1 : 0 ≤ ((dstates l).map F).sum := List.sum_nonneg (fun x hx => by
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact hF y)
  positivity

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

theorem path_bound (hF : ∀ x, 0 ≤ F x) (hk : 0 ≤ k) {C : ℝ}
    (hC : ∀ (m : ℕ) (s : ℤ), 0 < m → (m : ℝ) * C ≤ k + ∑ j ∈ Finset.range m, F (s - j))
    (p : List ℤ) (hv : p.IsChain vrel) :
    C * ((downCount p : ℝ) - downCount (loopErase p)) ≤ pcost F k p := by
  obtain ⟨-, -, -, h⟩ := erase_bound F k hF hk hC p hv
  have := pcost_nonneg F k hF hk (loopErase p)
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

lemma gp_nonneg {T : ℝ} (hT : 0 ≤ T) (n j : ℕ) : 0 ≤ gp T n j := by
  unfold gp; positivity

lemma gp_le {T : ℝ} (hT : 0 ≤ T) {n j : ℕ} (hj : j ≤ 2 ^ n) : gp T n j ≤ T := by
  unfold gp
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have : (j : ℝ) ≤ 2 ^ n := by exact_mod_cast hj
  rw [mul_div_assoc', div_le_iff₀ h2]
  nlinarith

lemma gap (E : Finset ℝ) : ∃ δ > 0, ∀ τ ∈ E, ∀ τ' ∈ E, τ < τ' → δ ≤ τ' - τ := by
  classical
  set D := ((E ×ˢ E).filter (fun q => q.1 < q.2)).image (fun q => q.2 - q.1) with hD
  by_cases hDn : D.Nonempty
  · refine ⟨D.min' hDn, ?_, ?_⟩
    · obtain ⟨q, hq, e⟩ := Finset.mem_image.mp (D.min'_mem hDn)
      rw [Finset.mem_filter] at hq
      rw [← e]
      linarith [hq.2]
    · intro τ hτ τ' hτ' hlt
      exact D.min'_le _ (Finset.mem_image.mpr ⟨(τ, τ'),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hτ, hτ'⟩, hlt⟩, rfl⟩)
  · refine ⟨1, one_pos, fun τ hτ τ' hτ' hlt => ?_⟩
    exfalso
    apply hDn
    exact ⟨τ' - τ, Finset.mem_image.mpr ⟨(τ, τ'),
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hτ, hτ'⟩, hlt⟩, rfl⟩⟩

lemma eventually_cells {T : ℝ} (hT : 0 < T) (E : Finset ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ,
      (E.filter (fun τ => gp T n j < τ ∧ τ ≤ gp T n (j + 1))).card ≤ 1 := by
  obtain ⟨δ, hδ, hgap⟩ := gap E
  have hlim : Tendsto (fun n : ℕ => T / (2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with n hn j
  rw [Finset.card_le_one]
  intro τ hτ τ' hτ'
  rw [Finset.mem_filter, gp_succ] at hτ hτ'
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := hgap τ hτ.1 τ' hτ'.1 h
    linarith [hτ.2.1, hτ.2.2, hτ'.2.1, hτ'.2.2]
  · have := hgap τ' hτ'.1 τ hτ.1 h
    linarith [hτ.2.1, hτ.2.2, hτ'.2.1, hτ'.2.2]

lemma cell_iff {T : ℝ} (hT : 0 < T) (n j : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    ⌈τ / (T / 2 ^ n)⌉₊ - 1 = j ↔ gp T n j < τ ∧ τ ≤ gp T n (j + 1) := by
  have hh : 0 < T / 2 ^ n := by positivity
  have hpos : 1 ≤ ⌈τ / (T / 2 ^ n)⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; positivity)
  have e1 : ⌈τ / (T / 2 ^ n)⌉₊ - 1 = j ↔ ⌈τ / (T / 2 ^ n)⌉₊ = j + 1 := by omega
  rw [e1, Nat.ceil_eq_iff (by omega), Nat.add_sub_cancel, gp, gp, lt_div_iff₀ hh, div_le_iff₀ hh]
  all_goals (push_cast; try rfl)

lemma sum_cells {T : ℝ} (hT : 0 < T) (n : ℕ) (E : Finset ℝ) (hE : ∀ τ ∈ E, 0 < τ ∧ τ ≤ T)
    (f : ℝ → ℝ≥0∞) :
    ∑ τ ∈ E, f τ = ∑ j ∈ Finset.range (2 ^ n),
      ∑ τ ∈ E.filter (fun τ => gp T n j < τ ∧ τ ≤ gp T n (j + 1)), f τ := by
  have hh : 0 < T / 2 ^ n := by positivity
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun τ => ⌈τ / (T / 2 ^ n)⌉₊ - 1)
    (t := Finset.range (2 ^ n))]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr (Finset.filter_congr (fun τ hτ => cell_iff hT n j (hE τ hτ).1)) ?_
    intro _ _; rfl
  · intro τ hτ
    rw [Finset.mem_range]
    have h1 : τ / (T / 2 ^ n) ≤ (2 ^ n : ℕ) := by
      rw [div_le_iff₀ hh]
      push_cast
      have : (2 : ℝ) ^ n * (T / 2 ^ n) = T := by field_simp
      linarith [(hE τ hτ).2]
    have h2 := Nat.ceil_le.mpr h1
    have h3 : 1 ≤ ⌈τ / (T / 2 ^ n)⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
      rw [Ne, Nat.ceil_eq_zero, not_le]; exact div_pos (hE τ hτ).1 hh)
    have h4 : 0 < 2 ^ n := by positivity
    omega

variable {x : ℤ} {U N : ℝ → ℤ}

lemma mem_ev_iff {T : ℝ} (hE : (evSet U N T).Finite) {a b : ℝ} (h0 : 0 ≤ a) (hbT : b ≤ T)
    {t : ℝ} (h1 : a < t) (h2 : t ≤ b) :
    t ∈ hE.toFinset.filter (fun τ => a < τ ∧ τ ≤ b) ↔ (IsJump N t ∨ IsJump U t) := by
  rw [Finset.mem_filter, Set.Finite.mem_toFinset]
  unfold evSet IsJump
  simp only [Set.mem_ofPred_eq, Set.mem_Ioc]
  constructor
  · rintro ⟨⟨_, h⟩, _⟩; exact h
  · intro h; exact ⟨⟨⟨by linarith, by linarith⟩, h⟩, h1, h2⟩

lemma cell_facts (hU : Monotone U) (hUr : RCont U) (hN : Monotone N) (hNr : RCont N)
    {T : ℝ} (hE : (evSet U N T).Finite) {a b : ℝ} (h0 : 0 ≤ a) (hab : a < b) (hbT : b ≤ T) :
    (hE.toFinset.filter (fun τ => a < τ ∧ τ ≤ b) = ∅ → N b = N a ∧ U b = U a) ∧
    (∀ τ, hE.toFinset.filter (fun τ => a < τ ∧ τ ≤ b) = {τ} →
      N b - N a = N τ - leftVal N τ ∧ U b - U a = U τ - leftVal U τ ∧
      leftVal U τ = U a ∧ leftVal N τ = N a) := by
  constructor
  · intro hemp
    have hno : ∀ t, a < t → t ≤ b → ¬ (IsJump N t ∨ IsJump U t) := by
      intro t h1 h2 h3
      have := (mem_ev_iff hE h0 hbT h1 h2).mpr h3
      rw [hemp] at this
      simp at this
    exact ⟨val_noJump hN hNr hab.le (fun t h1 h2 h3 => hno t h1 h2 (Or.inl h3)),
      val_noJump hU hUr hab.le (fun t h1 h2 h3 => hno t h1 h2 (Or.inr h3))⟩
  · intro τ hτ
    have hmem : τ ∈ hE.toFinset.filter (fun τ => a < τ ∧ τ ≤ b) := by rw [hτ]; simp
    have hτab := (Finset.mem_filter.mp hmem).2
    have hno : ∀ t, a < t → t ≤ b → t ≠ τ → ¬ (IsJump N t ∨ IsJump U t) := by
      intro t h1 h2 hne h3
      have := (mem_ev_iff hE h0 hbT h1 h2).mpr h3
      rw [hτ, Finset.mem_singleton] at this
      exact hne this
    have hlU := lv_noJump hU hUr hτab.1 (fun t h1 h2 h3 =>
      hno t h1 (by linarith [hτab.2]) (ne_of_lt h2) (Or.inr h3))
    have hlN := lv_noJump hN hNr hτab.1 (fun t h1 h2 h3 =>
      hno t h1 (by linarith [hτab.2]) (ne_of_lt h2) (Or.inl h3))
    have hvU := val_noJump hU hUr hτab.2 (fun t h1 h2 h3 =>
      hno t (by linarith [hτab.1]) h2 (ne_of_gt h1) (Or.inr h3))
    have hvN := val_noJump hN hNr hτab.2 (fun t h1 h2 h3 =>
      hno t (by linarith [hτab.1]) h2 (ne_of_gt h1) (Or.inl h3))
    refine ⟨by rw [hvN, hlN], by rw [hvU, hlU], hlU, hlN⟩

lemma ofReal_toNat {z : ℤ} (hz : 0 ≤ z) : ENNReal.ofReal ((z : ℤ) : ℝ) = ((z.toNat : ℕ) : ℝ≥0∞) := by
  rw [← ENNReal.ofReal_natCast]
  congr 1
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hz]

def Sn (g : ℤ → ℝ≥0∞) (x : ℤ) (U N : ℝ → ℤ) (T : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (2 ^ n), g (x + U (gp T n j) - N (gp T n j))
    * ENNReal.ofReal ((N (gp T n (j + 1)) - N (gp T n j) : ℤ) : ℝ)

def Jn (U : ℝ → ℤ) (T : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (2 ^ n), if U (gp T n j) < U (gp T n (j + 1)) then 1 else 0

def Rn (g : ℤ → ℝ≥0∞) (x : ℤ) (U N : ℝ → ℤ) (T : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (2 ^ n), g (x + U (gp T n j) - N (gp T n j)) * ENNReal.ofReal (T / 2 ^ n)

lemma ev_mem {T : ℝ} (hE : (evSet U N T).Finite) : ∀ τ ∈ hE.toFinset, 0 < τ ∧ τ ≤ T := by
  intro τ hτ
  rw [Set.Finite.mem_toFinset] at hτ
  exact hτ.1

theorem Sn_eventually (g : ℤ → ℝ≥0∞) (hU : Monotone U) (hUr : RCont U) (hN : Monotone N)
    (hNr : RCont N) {T : ℝ} (hT : 0 < T) (hE : (evSet U N T).Finite) :
    ∀ᶠ n in atTop, Sn g x U N T n = ∑ τ ∈ hE.toFinset,
      g (x + leftVal U τ - leftVal N τ) * (((N τ - leftVal N τ).toNat : ℕ) : ℝ≥0∞) := by
  filter_upwards [eventually_cells hT hE.toFinset] with n hn
  rw [sum_cells hT n hE.toFinset (ev_mem hE), Sn]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjn := Finset.mem_range.mp hj
  have h0 := gp_nonneg hT.le n j
  have hh' : 0 < T / 2 ^ n := by positivity
  have hab : gp T n j < gp T n (j + 1) := by rw [gp_succ]; linarith
  have hbT := gp_le hT.le (n := n) (j := j + 1) (by omega)
  obtain ⟨c1, c2⟩ := cell_facts hU hUr hN hNr hE h0 hab hbT
  obtain ⟨τ, hτ⟩ := Finset.card_le_one_iff_subset_singleton.mp (hn j)
  rcases Finset.subset_singleton_iff.mp hτ with h | h
  · rw [h, Finset.sum_empty, (c1 h).1, sub_self]; simp
  · obtain ⟨d1, -, d3, d4⟩ := c2 τ h
    rw [h, Finset.sum_singleton, d1, d3, d4, ofReal_toNat (by have := lv_le hN τ; omega)]

theorem Jn_eventually (hU : Monotone U) (hUr : RCont U) (hN : Monotone N)
    (hNr : RCont N) {T : ℝ} (hT : 0 < T) (hE : (evSet U N T).Finite) :
    ∀ᶠ n in atTop, Jn U T n = ∑ τ ∈ hE.toFinset, if 0 < U τ - leftVal U τ then 1 else 0 := by
  filter_upwards [eventually_cells hT hE.toFinset] with n hn
  rw [sum_cells hT n hE.toFinset (ev_mem hE), Jn]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjn := Finset.mem_range.mp hj
  have h0 := gp_nonneg hT.le n j
  have hh' : 0 < T / 2 ^ n := by positivity
  have hab : gp T n j < gp T n (j + 1) := by rw [gp_succ]; linarith
  have hbT := gp_le hT.le (n := n) (j := j + 1) (by omega)
  obtain ⟨c1, c2⟩ := cell_facts hU hUr hN hNr hE h0 hab hbT
  obtain ⟨τ, hτ⟩ := Finset.card_le_one_iff_subset_singleton.mp (hn j)
  rcases Finset.subset_singleton_iff.mp hτ with h | h
  · rw [h, Finset.sum_empty, (c1 h).2]; simp
  · obtain ⟨-, d2, -, -⟩ := c2 τ h
    rw [h, Finset.sum_singleton]
    have : (U (gp T n j) < U (gp T n (j + 1))) ↔ (0 < U τ - leftVal U τ) := by omega
    simp only [this]

def cl (T : ℝ) (n : ℕ) (t : ℝ) : ℝ := ((⌈t / (T / 2 ^ n)⌉₊ - 1 : ℕ) : ℝ) * (T / 2 ^ n)

lemma cl_cell {T : ℝ} (hT : 0 < T) (n j : ℕ) {t : ℝ} (ht : gp T n j < t ∧ t ≤ gp T n (j + 1)) :
    cl T n t = gp T n j := by
  have h0 : 0 < t := lt_of_le_of_lt (gp_nonneg hT.le n j) ht.1
  unfold cl
  rw [(cell_iff hT n j h0).mpr ht]
  rfl

lemma cl_bounds {T : ℝ} (hT : 0 < T) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    t - T / 2 ^ n ≤ cl T n t ∧ cl T n t < t := by
  have hh : 0 < T / 2 ^ n := by positivity
  have hpos : 1 ≤ ⌈t / (T / 2 ^ n)⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; exact div_pos ht hh)
  have e : (((⌈t / (T / 2 ^ n)⌉₊ - 1 : ℕ) : ℝ)) = (⌈t / (T / 2 ^ n)⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub hpos]; simp
  have h1 := Nat.le_ceil (t / (T / 2 ^ n))
  have h2 := Nat.ceil_lt_add_one (div_pos ht hh).le
  unfold cl
  rw [e]
  have h3 : t / (T / 2 ^ n) * (T / 2 ^ n) = t := by field_simp
  constructor <;> nlinarith

lemma lintegral_cells (φ : ℝ → ℝ≥0∞) (h : ℝ) (hh : 0 ≤ h) : ∀ M : ℕ,
    ∫⁻ t in Set.Ioc 0 ((M : ℝ) * h), φ t
      = ∑ j ∈ Finset.range M, ∫⁻ t in Set.Ioc ((j : ℝ) * h) (((j : ℝ) + 1) * h), φ t
  | 0 => by simp
  | M + 1 => by
    rw [Finset.sum_range_succ, ← lintegral_cells φ h hh M]
    have e : ((M + 1 : ℕ) : ℝ) * h = ((M : ℝ) + 1) * h := by push_cast; ring
    rw [e, ← Set.Ioc_union_Ioc_eq_Ioc (by positivity : (0 : ℝ) ≤ (M : ℝ) * h)
      (by nlinarith : (M : ℝ) * h ≤ ((M : ℝ) + 1) * h),
      lintegral_union measurableSet_Ioc (Set.Ioc_disjoint_Ioc_of_le le_rfl)]

lemma Rn_eq (g : ℤ → ℝ≥0∞) (hU : Monotone U) (hN : Monotone N) {T : ℝ} (hT : 0 < T) (n : ℕ) :
    Rn g x U N T n = ∫⁻ t in Set.Ioc 0 T, g (x + U (cl T n t) - N (cl T n t)) := by
  have hh : 0 < T / 2 ^ n := by positivity
  have hT' : T = ((2 ^ n : ℕ) : ℝ) * (T / 2 ^ n) := by push_cast; field_simp
  have hI : Set.Ioc (0 : ℝ) T = Set.Ioc 0 (((2 ^ n : ℕ) : ℝ) * (T / 2 ^ n)) := by
    congr 1
  rw [hI, lintegral_cells _ _ hh.le, Rn]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => g (x + U (gp T n j) - N (gp T n j)))
    (fun t ht => by
      have ht' : gp T n j < t ∧ t ≤ gp T n (j + 1) := by
        unfold gp; push_cast; exact ⟨ht.1, ht.2⟩
      simp only
      rw [cl_cell hT n j ht']),
    setLIntegral_const, Real.volume_Ioc]
  congr 2
  ring

lemma path_meas (hU : Monotone U) (hN : Monotone N) :
    Measurable (fun t => x + U t - N t) := by
  have h1 : Measurable U := hU.measurable
  have h2 : Measurable N := hN.measurable
  exact (measurable_const.add h1).sub h2

theorem Rn_tendsto (g : ℤ → ℝ≥0∞) {B : ℝ≥0∞} (hB : B ≠ ⊤) (hg : ∀ z, g z ≤ B)
    (hU : Monotone U) (hUr : RCont U) (hN : Monotone N) (hNr : RCont N) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n => Rn g x U N T n) atTop
      (𝓝 (∫⁻ t in Set.Ioc 0 T, g (x + U t - N t))) := by
  have hE := evSet_finite hU hN T
  simp_rw [Rn_eq g hU hN hT]
  have hclm : ∀ n, Measurable (cl T n) := by
    intro n
    have h1 : Measurable (fun t : ℝ => ⌈t / (T / 2 ^ n)⌉₊) :=
      Nat.measurable_ceil.comp (measurable_id.div_const _)
    have h2 := ((measurable_of_countable (fun k : ℕ => ((k - 1 : ℕ) : ℝ))).comp h1).mul_const (T / 2 ^ n)
    exact h2
  refine tendsto_lintegral_of_dominated_convergence (fun _ => B)
    (fun n => (measurable_of_countable g).comp ((path_meas hU hN).comp (hclm n)))
    (fun n => Eventually.of_forall (fun t => hg _)) (by
      rw [setLIntegral_const]
      exact ENNReal.mul_ne_top hB measure_Ioc_lt_top.ne) ?_
  have hnull : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 T)), t ∉ (hE.toFinset : Set ℝ) :=
    ae_restrict_of_ae (Set.Finite.countable (Finset.finite_toSet _) |>.ae_notMem _)
  filter_upwards [hnull, ae_restrict_mem measurableSet_Ioc] with t ht htT
  refine tendsto_nhds_of_eventually_eq ?_

  set E' := hE.toFinset.filter (· < t) with hE'
  set p : ℝ := if h : E'.Nonempty then E'.max' h else 0 with hp
  have hpt : p < t := by
    rw [hp]
    split_ifs with h
    · exact (Finset.mem_filter.mp (E'.max'_mem h)).2
    · exact htT.1
  have hp0 : 0 ≤ p := by
    rw [hp]
    split_ifs with h
    · exact ((ev_mem hE) _ (Finset.mem_filter.mp (E'.max'_mem h)).1).1.le
    · exact le_rfl
  have hlim : Tendsto (fun n : ℕ => T / (2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  filter_upwards [hlim.eventually (gt_mem_nhds (sub_pos.mpr hpt))] with n hn
  obtain ⟨b1, b2⟩ := cl_bounds hT n htT.1
  have hcp : p < cl T n t := by linarith
  have hno : ∀ s, cl T n t < s → s ≤ t → ¬ (IsJump N s ∨ IsJump U s) := by
    intro s h1 h2 h3
    have hsE : s ∈ hE.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact ⟨⟨by linarith, le_trans h2 htT.2⟩, h3⟩
    rcases eq_or_lt_of_le h2 with h4 | h4
    · rw [h4] at hsE; exact ht (by exact_mod_cast hsE)
    · have hsE' : s ∈ E' := Finset.mem_filter.mpr ⟨hsE, h4⟩
      have hne : E'.Nonempty := ⟨s, hsE'⟩
      have : s ≤ p := by rw [hp, dif_pos hne]; exact E'.le_max' s hsE'
      linarith
  have e1 := val_noJump hU hUr b2.le (fun s h1 h2 h3 => hno s h1 h2 (Or.inr h3))
  have e2 := val_noJump hN hNr b2.le (fun s h1 h2 h3 => hno s h1 h2 (Or.inl h3))
  rw [e1, e2]

lemma jumpCount_eq (hU : Monotone U) {T : ℝ} (hE : (evSet U N T).Finite) :
    ((jumpCount U T : ℕ) : ℝ≥0∞) = ∑ τ ∈ hE.toFinset, if 0 < U τ - leftVal U τ then 1 else 0 := by
  rw [Finset.sum_boole]
  congr 1
  unfold jumpCount
  rw [← Set.ncard_coe_finset]
  congr 1
  ext t
  simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  rw [jump_iff hU t]
  unfold evSet IsJump
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, Or.inr h2⟩, by omega⟩
  · rintro ⟨⟨h1, _⟩, h2⟩
    exact ⟨h1, by omega⟩

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

theorem unit_jumps {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂S.ν, ∀ t ∈ Set.Ioc 0 T, S.N t ω - leftVal (fun s => S.N s ω) t ≤ 1 := by
  rw [ae_iff]
  have hn : ∀ n : ℕ, S.ν {ω | ¬∀ t ∈ Set.Ioc 0 T, S.N t ω - leftVal (fun s => S.N s ω) t ≤ 1}
      ≤ ENNReal.ofReal ((P.lam * T) ^ 2 / 2 ^ n) := by
    intro n
    have hh : 0 < T / 2 ^ n := by positivity
    have hsub : {ω | ¬∀ t ∈ Set.Ioc 0 T, S.N t ω - leftVal (fun s => S.N s ω) t ≤ 1}
        ⊆ ⋃ j ∈ Finset.range (2 ^ n), {ω | 2 ≤ S.N (gp T n (j + 1)) ω - S.N (gp T n j) ω} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq, not_forall, not_le] at hω
      obtain ⟨t, ht, h2⟩ := hω
      have hcell := (cell_iff hT n (⌈t / (T / 2 ^ n)⌉₊ - 1) ht.1).mp rfl
      have hjlt : ⌈t / (T / 2 ^ n)⌉₊ - 1 < 2 ^ n := by
        have h1 : t / (T / 2 ^ n) ≤ (2 ^ n : ℕ) := by
          rw [div_le_iff₀ hh]
          push_cast
          have : (2 : ℝ) ^ n * (T / 2 ^ n) = T := by field_simp
          linarith [ht.2]
        have h3 := Nat.ceil_le.mpr h1
        have h4 : 1 ≤ ⌈t / (T / 2 ^ n)⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
          rw [Ne, Nat.ceil_eq_zero, not_le]; exact div_pos ht.1 hh)
        have h5 : 0 < 2 ^ n := by positivity
        omega
      simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_ofPred_eq]
      refine ⟨⌈t / (T / 2 ^ n)⌉₊ - 1, hjlt, ?_⟩
      have e1 : S.N t ω ≤ S.N (gp T n (⌈t / (T / 2 ^ n)⌉₊ - 1 + 1)) ω := S.N_mono ω hcell.2
      have e2 : S.N (gp T n (⌈t / (T / 2 ^ n)⌉₊ - 1)) ω ≤ leftVal (fun s => S.N s ω) t :=
        le_lv (S.N_mono ω) hcell.1
      omega
    calc _ ≤ S.ν (⋃ j ∈ Finset.range (2 ^ n),
          {ω | 2 ≤ S.N (gp T n (j + 1)) ω - S.N (gp T n j) ω}) := measure_mono hsub
      _ ≤ ∑ j ∈ Finset.range (2 ^ n), S.ν {ω | 2 ≤ S.N (gp T n (j + 1)) ω - S.N (gp T n j) ω} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ j ∈ Finset.range (2 ^ n), ENNReal.ofReal ((P.lam * (T / 2 ^ n)) ^ 2) := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          have hvw : gp T n j ≤ gp T n (j + 1) := by rw [gp_succ]; linarith
          have h := pois_two S hvw
          rwa [show gp T n (j + 1) - gp T n j = T / 2 ^ n by rw [gp_succ]; ring] at h
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

structure Proc (S : DemandSpace P) where
  x : S.Ω → ℤ
  U : ℝ → S.Ω → ℤ
  x_meas : Measurable[S.𝓕 0] x
  U_adapted : ∀ t, Measurable[S.𝓕 t] (U t)
  U_mono : ∀ ω, Monotone (fun t => U t ω)
  U_rcont : ∀ ω t, ∃ δ > 0, ∀ s, t ≤ s → s < t + δ → U s ω = U t ω

variable {S} (pr : Proc S)

lemma x_m : Measurable pr.x := pr.x_meas.mono (S.𝓕.le 0) le_rfl

lemma U_m (t : ℝ) : Measurable (pr.U t) := (pr.U_adapted t).mono (S.𝓕.le t) le_rfl

lemma X_adapted {t : ℝ} (ht : 0 ≤ t) :
    Measurable[S.𝓕 t] (fun ω => pr.x ω + pr.U t ω - S.N t ω) :=
  ((pr.x_meas.mono (S.𝓕.mono ht) le_rfl).add (pr.U_adapted t)).sub (S.N_adapted t)

lemma X_m (t : ℝ) : Measurable (fun ω => pr.x ω + pr.U t ω - S.N t ω) :=
  ((x_m pr).add (U_m pr t)).sub (S.N_meas t)

lemma joint_meas {Y : ℝ → S.Ω → ℤ} (hm : ∀ t, Measurable (Y t))
    (hr : ∀ ω t, ∃ δ > 0, ∀ s, t ≤ s → s < t + δ → Y s ω = Y t ω) :
    Measurable (fun p : S.Ω × ℝ => Y p.2 p.1) := by
  set g : ℕ → S.Ω × ℝ → ℤ := fun k p => Y ((⌈p.2 * 2 ^ k⌉ : ℤ) / (2 : ℝ) ^ k) p.1 with hg
  have hgm : ∀ k, Measurable (g k) := by
    intro k
    have h1 : Measurable (fun q : S.Ω × ℤ => Y ((q.2 : ℝ) / (2 : ℝ) ^ k) q.1) :=
      measurable_from_prod_countable_left (fun z => by exact hm ((z : ℝ) / (2 : ℝ) ^ k))
    exact h1.comp (measurable_fst.prodMk (Int.measurable_ceil.comp (measurable_snd.mul_const _)))
  refine measurable_of_tendsto_metrizable hgm (tendsto_pi_nhds.mpr (fun p => ?_))
  refine tendsto_nhds_of_eventually_eq ?_
  obtain ⟨δ, hδ, hN⟩ := hr p.1 p.2
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

lemma X_joint : Measurable (fun p : S.Ω × ℝ => pr.x p.1 + pr.U p.2 p.1 - S.N p.2 p.1) :=
  (((x_m pr).comp measurable_fst).add (joint_meas (U_m pr) pr.U_rcont)).sub S.N_joint

lemma ev_fin (T : ℝ) (ω : S.Ω) :
    (evSet (fun t => pr.U t ω) (fun t => S.N t ω) T).Finite :=
  evSet_finite (pr.U_mono ω) (S.N_mono ω) T

def Asum (g : ℤ → ℝ≥0∞) (T : ℝ) (ω : S.Ω) : ℝ≥0∞ :=
  ∑ τ ∈ (ev_fin pr T ω).toFinset,
    g (pr.x ω + leftVal (fun t => pr.U t ω) τ - leftVal (fun t => S.N t ω) τ)
      * (((S.N τ ω - leftVal (fun t => S.N t ω) τ).toNat : ℕ) : ℝ≥0∞)

lemma Sn_meas (g : ℤ → ℝ≥0∞) (T : ℝ) (n : ℕ) :
    Measurable (fun ω => Sn g (pr.x ω) (fun t => pr.U t ω) (fun t => S.N t ω) T n) := by
  unfold Sn
  refine Finset.measurable_sum _ (fun j _ => ?_)
  refine ((measurable_of_countable g).comp (X_m pr _)).mul ?_
  have h := (measurable_of_countable (fun z : ℤ => ENNReal.ofReal (z : ℝ))).comp
    ((S.N_meas (gp T n (j + 1))).sub (S.N_meas (gp T n j)))
  exact h

lemma Asum_eventually (g : ℤ → ℝ≥0∞) {T : ℝ} (hT : 0 < T) (ω : S.Ω) :
    ∀ᶠ n in atTop, Sn g (pr.x ω) (fun t => pr.U t ω) (fun t => S.N t ω) T n = Asum pr g T ω :=
  Sn_eventually g (pr.U_mono ω) (pr.U_rcont ω) (S.N_mono ω) (S.N_rcont ω) hT (ev_fin pr T ω)

lemma Asum_meas (g : ℤ → ℝ≥0∞) {T : ℝ} (hT : 0 < T) : Measurable (Asum pr g T) := by
  have e : Asum pr g T = fun ω => liminf (fun n => Sn g (pr.x ω) (fun t => pr.U t ω)
      (fun t => S.N t ω) T n) atTop := by
    funext ω
    rw [liminf_congr (Asum_eventually pr g hT ω), liminf_const]
  rw [e]
  exact Measurable.liminf (fun n => Sn_meas pr g T n)

lemma jumps_eq (T : ℝ) (ω : S.Ω) :
    ((jumpCount (fun t => pr.U t ω) T : ℕ) : ℝ≥0∞)
      = ∑ τ ∈ (ev_fin pr T ω).toFinset,
          if 0 < pr.U τ ω - leftVal (fun t => pr.U t ω) τ then 1 else 0 :=
  jumpCount_eq (pr.U_mono ω) (ev_fin pr T ω)

lemma jumps_meas {T : ℝ} (hT : 0 < T) :
    Measurable (fun ω => ((jumpCount (fun t => pr.U t ω) T : ℕ) : ℝ≥0∞)) := by
  have hJ : ∀ n, Measurable (fun ω => Jn (fun t => pr.U t ω) T n) := by
    intro n
    unfold Jn
    refine Finset.measurable_sum _ (fun j _ => ?_)
    exact Measurable.ite (measurableSet_lt (U_m pr _) (U_m pr _)) measurable_const measurable_const
  have e : (fun ω => ((jumpCount (fun t => pr.U t ω) T : ℕ) : ℝ≥0∞))
      = fun ω => liminf (fun n => Jn (fun t => pr.U t ω) T n) atTop := by
    funext ω
    rw [liminf_congr (Jn_eventually (pr.U_mono ω) (pr.U_rcont ω) (S.N_mono ω) (S.N_rcont ω) hT
      (ev_fin pr T ω)), liminf_const, jumps_eq]
  rw [e]
  exact Measurable.liminf hJ

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

theorem ES_eq (g : ℤ → ℝ≥0∞) {T : ℝ} (hT : 0 < T) (n : ℕ) :
    ∫⁻ ω, Sn g (pr.x ω) (fun t => pr.U t ω) (fun t => S.N t ω) T n ∂S.ν
      = ENNReal.ofReal P.lam * ∫⁻ ω, Rn g (pr.x ω) (fun t => pr.U t ω) (fun t => S.N t ω) T n ∂S.ν := by
  unfold Sn Rn
  have hm1 : ∀ j ∈ Finset.range (2 ^ n), Measurable (fun ω => g (pr.x ω + pr.U (gp T n j) ω
      - S.N (gp T n j) ω) * ENNReal.ofReal ((S.N (gp T n (j + 1)) ω - S.N (gp T n j) ω : ℤ) : ℝ)) := by
    intro j _
    refine ((measurable_of_countable g).comp (X_m pr _)).mul ?_
    have h := (measurable_of_countable (fun z : ℤ => ENNReal.ofReal (z : ℝ))).comp
      ((S.N_meas (gp T n (j + 1))).sub (S.N_meas (gp T n j)))
    exact h
  have hm2 : ∀ j ∈ Finset.range (2 ^ n), Measurable (fun ω => g (pr.x ω + pr.U (gp T n j) ω
      - S.N (gp T n j) ω) * ENNReal.ofReal (T / 2 ^ n)) :=
    fun j _ => ((measurable_of_countable g).comp (X_m pr _)).mul measurable_const
  rw [lintegral_finsetSum _ hm1, lintegral_finsetSum _ hm2, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hv := gp_nonneg hT.le n j
  have hh' : 0 < T / 2 ^ n := by positivity
  have hvw : gp T n j ≤ gp T n (j + 1) := by rw [gp_succ]; linarith
  rw [lintegral_mul_incr hv hvw (X_adapted pr hv) g,
    lintegral_mul_const' (ENNReal.ofReal (T / 2 ^ n))
      (fun ω => g (pr.x ω + pr.U (gp T n j) ω - S.N (gp T n j) ω)) ENNReal.ofReal_ne_top,
    show gp T n (j + 1) - gp T n j = T / 2 ^ n by rw [gp_succ]; ring,
    ENNReal.ofReal_mul P.lam_nonneg]
  ring

lemma Sn_le (g : ℤ → ℝ≥0∞) {B : ℝ≥0∞} (hg : ∀ z, g z ≤ B) {T : ℝ} (hT : 0 < T) (n : ℕ) (ω : S.Ω) :
    Sn g (pr.x ω) (fun t => pr.U t ω) (fun t => S.N t ω) T n
      ≤ B * ENNReal.ofReal ((S.N T ω - S.N 0 ω : ℤ) : ℝ) := by
  unfold Sn
  have hnn : ∀ j ∈ Finset.range (2 ^ n), (0 : ℝ) ≤ ((S.N (gp T n (j + 1)) ω - S.N (gp T n j) ω : ℤ) : ℝ) := by
    intro j _
    have hh' : 0 < T / 2 ^ n := by positivity
    have h : gp T n j ≤ gp T n (j + 1) := by rw [gp_succ]; linarith
    exact_mod_cast S.incr_nonneg h ω
  calc ∑ j ∈ Finset.range (2 ^ n), g (pr.x ω + pr.U (gp T n j) ω - S.N (gp T n j) ω)
        * ENNReal.ofReal ((S.N (gp T n (j + 1)) ω - S.N (gp T n j) ω : ℤ) : ℝ)
      ≤ ∑ j ∈ Finset.range (2 ^ n), B
        * ENNReal.ofReal ((S.N (gp T n (j + 1)) ω - S.N (gp T n j) ω : ℤ) : ℝ) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul' (hg _) le_rfl)
    _ = B * ENNReal.ofReal ((S.N T ω - S.N 0 ω : ℤ) : ℝ) := by
        rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg hnn]
        congr 2
        have h := Finset.sum_range_sub (fun j => S.N (gp T n j) ω) (2 ^ n)
        have h0 : gp T n 0 = 0 := by simp [gp]
        have hT' : gp T n (2 ^ n) = T := by unfold gp; push_cast; field_simp
        rw [h0, hT'] at h
        push_cast at h ⊢
        exact_mod_cast h

lemma Rn_le (g : ℤ → ℝ≥0∞) {B : ℝ≥0∞} (hg : ∀ z, g z ≤ B) {T : ℝ} (hT : 0 < T) (n : ℕ) (ω : S.Ω) :
    Rn g (pr.x ω) (fun t => pr.U t ω) (fun t => S.N t ω) T n ≤ B * ENNReal.ofReal T := by
  unfold Rn
  calc ∑ j ∈ Finset.range (2 ^ n), g (pr.x ω + pr.U (gp T n j) ω - S.N (gp T n j) ω)
        * ENNReal.ofReal (T / 2 ^ n)
      ≤ ∑ j ∈ Finset.range (2 ^ n), B * ENNReal.ofReal (T / 2 ^ n) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul' (hg _) le_rfl)
    _ = B * ENNReal.ofReal T := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_left_comm,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        push_cast
        field_simp

theorem pasta_bdd (g : ℤ → ℝ≥0∞) {B : ℝ≥0∞} (hB : B ≠ ⊤) (hg : ∀ z, g z ≤ B) {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, Asum pr g T ω ∂S.ν
      = ENNReal.ofReal P.lam * ∫⁻ ω, (∫⁻ t in Set.Ioc 0 T, g (pr.x ω + pr.U t ω - S.N t ω)) ∂S.ν := by

  have h1 : Tendsto (fun n => ∫⁻ ω, Sn g (pr.x ω) (fun t => pr.U t ω) (fun t => S.N t ω) T n ∂S.ν)
      atTop (𝓝 (∫⁻ ω, Asum pr g T ω ∂S.ν)) := by
    refine tendsto_lintegral_of_dominated_convergence
      (fun ω => B * ENNReal.ofReal ((S.N T ω - S.N 0 ω : ℤ) : ℝ)) (fun n => Sn_meas pr g T n)
      (fun n => Eventually.of_forall (fun ω => Sn_le pr g hg hT n ω)) ?_ ?_
    · have hm : Measurable (fun ω => ENNReal.ofReal ((S.N T ω - S.N 0 ω : ℤ) : ℝ)) := by
        have h := (measurable_of_countable (fun z : ℤ => ENNReal.ofReal (z : ℝ))).comp
          ((S.N_meas T).sub (S.N_meas 0))
        exact h
      rw [lintegral_const_mul _ hm, S.lintegral_incr_val hT.le]
      exact ENNReal.mul_ne_top hB ENNReal.ofReal_ne_top
    · exact Eventually.of_forall (fun ω => tendsto_nhds_of_eventually_eq (Asum_eventually pr g hT ω))

  have h2 : Tendsto (fun n => ∫⁻ ω, Rn g (pr.x ω) (fun t => pr.U t ω) (fun t => S.N t ω) T n ∂S.ν)
      atTop (𝓝 (∫⁻ ω, (∫⁻ t in Set.Ioc 0 T, g (pr.x ω + pr.U t ω - S.N t ω)) ∂S.ν)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => B * ENNReal.ofReal T) (fun n => ?_)
      (fun n => Eventually.of_forall (fun ω => Rn_le pr g hg hT n ω)) ?_ ?_
    · unfold Rn
      refine Finset.measurable_sum _ (fun j _ => ?_)
      exact ((measurable_of_countable g).comp (X_m pr _)).mul measurable_const
    · rw [lintegral_const, measure_univ, mul_one]
      exact ENNReal.mul_ne_top hB ENNReal.ofReal_ne_top
    · exact Eventually.of_forall (fun ω => Rn_tendsto g hB hg (pr.U_mono ω) (pr.U_rcont ω)
        (S.N_mono ω) (S.N_rcont ω) hT)
  have h3 := (ENNReal.Tendsto.const_mul h2 (Or.inr ENNReal.ofReal_ne_top)).congr
    (fun n => (ES_eq pr g hT n).symm)
  exact tendsto_nhds_unique h1 h3

theorem pasta (g : ℤ → ℝ≥0∞) (hg : ∀ z, g z ≠ ⊤) {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, Asum pr g T ω ∂S.ν
      = ENNReal.ofReal P.lam * ∫⁻ ω, (∫⁻ t in Set.Ioc 0 T, g (pr.x ω + pr.U t ω - S.N t ω)) ∂S.ν := by
  set gB : ℕ → ℤ → ℝ≥0∞ := fun B z => min (g z) (B : ℝ≥0∞) with hgB
  have hmono : ∀ z, Monotone (fun B => gB B z) := fun z a b hab =>
    min_le_min_left _ (by exact_mod_cast hab)
  have hlim : ∀ z, Tendsto (fun B => gB B z) atTop (𝓝 (g z)) := by
    intro z
    refine tendsto_nhds_of_eventually_eq ?_
    obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt (hg z)
    filter_upwards [eventually_ge_atTop m] with B hB
    exact min_eq_left (le_trans hm.le (by exact_mod_cast hB))
  have hbdd : ∀ B, ∀ z, gB B z ≤ (B : ℝ≥0∞) := fun B z => min_le_right _ _
  have hpB : ∀ B : ℕ, ∫⁻ ω, Asum pr (gB B) T ω ∂S.ν = ENNReal.ofReal P.lam
      * ∫⁻ ω, (∫⁻ t in Set.Ioc 0 T, gB B (pr.x ω + pr.U t ω - S.N t ω)) ∂S.ν :=
    fun B => pasta_bdd pr (gB B) (ENNReal.natCast_ne_top B) (hbdd B) hT

  have hL : Tendsto (fun B : ℕ => ∫⁻ ω, Asum pr (gB B) T ω ∂S.ν) atTop
      (𝓝 (∫⁻ ω, Asum pr g T ω ∂S.ν)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone (fun B => (Asum_meas pr (gB B) hT).aemeasurable)
      (Eventually.of_forall (fun ω a b hab => Finset.sum_le_sum (fun τ _ =>
        mul_le_mul' (hmono _ hab) le_rfl))) (Eventually.of_forall (fun ω => ?_))
    unfold Asum
    exact tendsto_finsetSum _ (fun τ _ => ENNReal.Tendsto.mul_const (hlim _) (Or.inr
      (ENNReal.natCast_ne_top _)))

  have hjm : ∀ B : ℕ, Measurable (fun p : S.Ω × ℝ => gB B (pr.x p.1 + pr.U p.2 p.1 - S.N p.2 p.1)) :=
    fun B => (measurable_of_countable (gB B)).comp (X_joint pr)
  have hR : Tendsto (fun B : ℕ => ∫⁻ ω, (∫⁻ t in Set.Ioc 0 T, gB B (pr.x ω + pr.U t ω - S.N t ω)) ∂S.ν)
      atTop (𝓝 (∫⁻ ω, (∫⁻ t in Set.Ioc 0 T, g (pr.x ω + pr.U t ω - S.N t ω)) ∂S.ν)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone (fun B =>
      ((hjm B).lintegral_prod_right' (ν := volume.restrict (Set.Ioc 0 T))).aemeasurable)
      (Eventually.of_forall (fun ω a b hab => lintegral_mono (fun t => hmono _ hab)))
      (Eventually.of_forall (fun ω => ?_))
    have hjt : ∀ B : ℕ, Measurable (fun t => gB B (pr.x ω + pr.U t ω - S.N t ω)) :=
      fun B => (hjm B).comp (measurable_const.prodMk measurable_id)
    exact lintegral_tendsto_of_tendsto_of_monotone (fun B => (hjt B).aemeasurable)
      (Eventually.of_forall (fun t a b hab => hmono _ hab))
      (Eventually.of_forall (fun t => hlim _))
  have hR' := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal P.lam) hR (Or.inr ENNReal.ofReal_ne_top)
  exact tendsto_nhds_unique hL (hR'.congr (fun B => (hpB B).symm))

end LBP

end TwoStageRnQ

open Finset Filter Topology

noncomputable section

namespace TwoStageRnQ

namespace Params

variable (P : Params)

end Params

namespace Params

variable (P : Params)

lemma latInf_bddBelow {j : ℕ} {F : ℝ → ℝ} (hF : ∀ x, 0 ≤ F x) :
    BddBelow (Set.range fun x => latAvg j F x) :=
  ⟨0, by rintro _ ⟨x, rfl⟩; exact latAvg_nonneg hF x⟩

lemma latInf_nonneg {j : ℕ} {F : ℝ → ℝ} (hF : ∀ x, 0 ≤ F x) : 0 ≤ latInf j F :=
  Real.iInf_nonneg (fun x => latAvg_nonneg hF x)

lemma cycCost_bddBelow {F : ℝ → ℝ} (hF : ∀ x, 0 ≤ F x) {k : ℝ} (hk : 0 ≤ k) :
    BddBelow (Set.range fun j : ℕ+ => k / ((j : ℕ) : ℝ) + latInf j F) :=
  ⟨0, by rintro _ ⟨j, rfl⟩; exact add_nonneg (div_nonneg hk (Nat.cast_nonneg _)) (latInf_nonneg hF)⟩

end Params

end TwoStageRnQ

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace LBP

open TwoStageRnQ.LB

lemma cycCost_nonneg {F : ℝ → ℝ} (hF : ∀ x, 0 ≤ F x) {k : ℝ} (hk : 0 ≤ k) : 0 ≤ cycCost F k :=
  le_ciInf (fun j => add_nonneg (div_nonneg hk (Nat.cast_nonneg _)) (Params.latInf_nonneg hF))

lemma cyc_hC {F : ℝ → ℝ} (hF : ∀ x, 0 ≤ F x) {k : ℝ} (hk : 0 ≤ k) (m : ℕ) (s : ℤ) (hm : 0 < m) :
    (m : ℝ) * cycCost F k ≤ k + ∑ j ∈ Finset.range m, (fun z : ℤ => F z) (s - j) := by
  have h1 : cycCost F k ≤ k / (((⟨m, hm⟩ : ℕ+) : ℕ) : ℝ) + latInf ((⟨m, hm⟩ : ℕ+) : ℕ) F :=
    ciInf_le (Params.cycCost_bddBelow hF hk) ⟨m, hm⟩
  have h2 : latInf m F ≤ latAvg m F s := ciInf_le (Params.latInf_bddBelow hF) (s : ℝ)
  simp only [PNat.mk_coe] at h1
  unfold latAvg at h2
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have e : ∑ j ∈ Finset.range m, (fun z : ℤ => F z) (s - j)
      = ∑ v ∈ Finset.range m, F ((s : ℝ) - v) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp
  rw [e]
  have h3 : cycCost F k ≤ (k + ∑ v ∈ Finset.range m, F ((s : ℝ) - v)) / m := by
    rw [add_div]; linarith
  rw [le_div_iff₀ hmR] at h3
  linarith

variable {P : Params} {S : DemandSpace P}

lemma path_ineq (pr : Proc S) (F : ℝ → ℝ) (hF : ∀ y, 0 ≤ F y) {k : ℝ} (hk : 0 ≤ k) {T : ℝ}
    (hT : 0 < T) (ω : S.Ω)
    (hunit : ∀ t ∈ Set.Ioc 0 T, S.N t ω - leftVal (fun s => S.N s ω) t ≤ 1) :
    ENNReal.ofReal (cycCost F k) * ENNReal.ofReal (((S.N T ω - S.N 0 ω : ℤ) : ℝ))
      ≤ Asum pr (fun z => ENNReal.ofReal (F z)) T ω
        + ENNReal.ofReal k * ((jumpCount (fun t => pr.U t ω) T : ℕ) : ℝ≥0∞)
        + ENNReal.ofReal (cycCost F k)
          * ((unfinishedCount (pr.x ω) (fun t => pr.U t ω) (fun t => S.N t ω) T : ℕ) : ℝ≥0∞) := by
  have hC0 := cycCost_nonneg hF hk
  obtain ⟨hv, hcost, hdown⟩ := chron_spec (fun z : ℤ => F z) k (pr.x ω) (fun t => pr.U t ω)
    (fun t => S.N t ω) (pr.U_mono ω) (pr.U_rcont ω) (S.N_mono ω) (S.N_rcont ω) hT.le
  have hpb := path_bound (fun z : ℤ => F z) k (fun z => hF _) hk (cyc_hC hF hk) _ hv
  have hr : unfinishedCount (pr.x ω) (fun t => pr.U t ω) (fun t => S.N t ω) T
      = downCount (loopErase (chronPath (pr.x ω) (fun t => pr.U t ω) (fun t => S.N t ω) T)) := rfl

  have hsum : ∀ τ ∈ (ev_fin pr T ω).toFinset,
      ∑ j ∈ Finset.range (S.N τ ω - leftVal (fun t => S.N t ω) τ).toNat,
        F ((pr.x ω + leftVal (fun t => pr.U t ω) τ - leftVal (fun t => S.N t ω) τ - j : ℤ) : ℝ)
      = (((S.N τ ω - leftVal (fun t => S.N t ω) τ).toNat : ℕ) : ℝ)
        * F ((pr.x ω + leftVal (fun t => pr.U t ω) τ - leftVal (fun t => S.N t ω) τ : ℤ) : ℝ) := by
    intro τ hτ
    have hτ' := (Set.Finite.mem_toFinset _).mp hτ
    have h1 := hunit τ hτ'.1
    rcases Nat.lt_or_ge (S.N τ ω - leftVal (fun t => S.N t ω) τ).toNat 1 with h | h
    · have h0 : (S.N τ ω - leftVal (fun t => S.N t ω) τ).toNat = 0 := by omega
      rw [h0]; simp
    · have h0 : (S.N τ ω - leftVal (fun t => S.N t ω) τ).toNat = 1 := by omega
      rw [h0]; simp
  rw [hcost, Finset.sum_congr rfl hsum] at hpb
  have hAsum : Asum pr (fun z => ENNReal.ofReal (F z)) T ω
      = ENNReal.ofReal (∑ τ ∈ (ev_fin pr T ω).toFinset,
          (((S.N τ ω - leftVal (fun t => S.N t ω) τ).toNat : ℕ) : ℝ)
          * F ((pr.x ω + leftVal (fun t => pr.U t ω) τ - leftVal (fun t => S.N t ω) τ : ℤ) : ℝ)) := by
    unfold Asum
    rw [ENNReal.ofReal_sum_of_nonneg (fun τ _ => mul_nonneg (Nat.cast_nonneg _) (hF _))]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [mul_comm, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have hS0 : 0 ≤ ∑ τ ∈ (ev_fin pr T ω).toFinset,
      (((S.N τ ω - leftVal (fun t => S.N t ω) τ).toNat : ℕ) : ℝ)
        * F ((pr.x ω + leftVal (fun t => pr.U t ω) τ - leftVal (fun t => S.N t ω) τ : ℤ) : ℝ) :=
    Finset.sum_nonneg (fun τ _ => mul_nonneg (Nat.cast_nonneg _) (hF _))
  have hD : (((S.N T ω - S.N 0 ω : ℤ) : ℝ))
      = ((downCount (chronPath (pr.x ω) (fun t => pr.U t ω) (fun t => S.N t ω) T) : ℕ) : ℝ) := by
    rw [← hdown]; push_cast; ring
  rw [hAsum, hr, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hC0, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul hk, ← ENNReal.ofReal_mul hC0,
    ← ENNReal.ofReal_add hS0 (mul_nonneg hk (Nat.cast_nonneg _)),
    ← ENNReal.ofReal_add (add_nonneg hS0 (mul_nonneg hk (Nat.cast_nonneg _)))
      (mul_nonneg hC0 (Nat.cast_nonneg _)), hD]
  exact ENNReal.ofReal_le_ofReal (by linarith)

theorem cycle_lemma (pr : Proc S) (F : ℝ → ℝ) (hF : ∀ y, 0 ≤ F y) {k : ℝ} (hk : 0 ≤ k) {T : ℝ}
    (hT : 0 < T) :
    ENNReal.ofReal (cycCost F k) * ENNReal.ofReal (P.lam * T)
      ≤ ENNReal.ofReal P.lam * ∫⁻ ω, (∫⁻ t in Set.Ioc 0 T,
          ENNReal.ofReal (F ((pr.x ω + pr.U t ω - S.N t ω : ℤ) : ℝ))) ∂S.ν
        + ENNReal.ofReal k * ∫⁻ ω, ((jumpCount (fun t => pr.U t ω) T : ℕ) : ℝ≥0∞) ∂S.ν
        + ENNReal.ofReal (cycCost F k) * ∫⁻ ω,
          ((unfinishedCount (pr.x ω) (fun t => pr.U t ω) (fun t => S.N t ω) T : ℕ) : ℝ≥0∞) ∂S.ν := by
  have h1 := lintegral_mono_ae (μ := S.ν) ((unit_jumps S hT).mono
    (fun ω h => path_ineq pr F hF hk hT ω h))
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, S.lintegral_incr_val hT.le, sub_zero] at h1
  have hAm := Asum_meas pr (fun z => ENNReal.ofReal (F z)) hT
  have hJm := jumps_meas pr hT
  have hAJ : Measurable (fun ω => Asum pr (fun z => ENNReal.ofReal (F z)) T ω
      + ENNReal.ofReal k * ((jumpCount (fun t => pr.U t ω) T : ℕ) : ℝ≥0∞)) :=
    hAm.add (hJm.const_mul _)
  rw [lintegral_add_left hAJ, lintegral_add_left hAm,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    pasta pr (fun z => ENNReal.ofReal (F z)) (fun z => ENNReal.ofReal_ne_top) hT] at h1
  exact h1

end LBP

end TwoStageRnQ

open Finset
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace Prop1

section Defs

variable (Q n : ℕ+) (R1 R2 : ℤ)

end Defs

section Comb

variable (Q n : ℕ+) (R1 R2 : ℤ)

end Comb

end Prop1

end TwoStageRnQ

open Finset
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace Prop1

section Bounds

variable (Q n : ℕ+) (R1 R2 : ℤ)

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

namespace LBA

open TwoStageRnQ.LB TwoStageRnQ.LBP

variable {P : Params} {S : DemandSpace P}

lemma cond_f {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) {X : S.Ω → ℤ} (hX : Measurable[S.𝓕 v] X)
    (f : ℝ → ℝ) (hf : ∀ y, 0 ≤ f y)
    (hpi : ∀ a : ℤ, PInt (P.lam * (w - v)) (fun d : ℕ => f ((a : ℝ) - d))) :
    ∫⁻ ω, ENNReal.ofReal (f (((X ω - (S.N w ω - S.N v ω) : ℤ) : ℝ))) ∂S.ν
      = ∫⁻ ω, ENNReal.ofReal (pexp (P.lam * (w - v)) (fun d : ℕ => f ((X ω : ℝ) - d))) ∂S.ν := by
  have hμ : 0 ≤ P.lam * (w - v) := mul_nonneg P.lam_nonneg (by linarith)
  have hXm : Measurable X := hX.mono (S.𝓕.le v) le_rfl
  have e1 : ∀ ω, ENNReal.ofReal (f (((X ω - (S.N w ω - S.N v ω) : ℤ) : ℝ)))
      = ENNReal.ofReal (f ((X ω : ℝ) - (((S.N w ω - S.N v ω).toNat : ℕ) : ℝ))) := by
    intro ω
    congr 2
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (S.incr_nonneg hvw ω)]
    push_cast
    ring
  have key := S.lintegral_incr hv hvw hX
    (fun (a : ℤ) (d : ℕ) => ENNReal.ofReal (f ((a : ℝ) - (d : ℝ))))
  rw [lintegral_congr e1, key, S.lintegral_comp hXm
    (fun a => ENNReal.ofReal (pexp (P.lam * (w - v)) (fun d : ℕ => f ((a : ℝ) - d))))]
  refine tsum_congr (fun a => ?_)
  congr 1
  exact TwoStageRnQ.Prop1.tsum_ofReal_pexp hμ (fun d => hf _) (hpi a)

lemma lintegral_Ioc_shift (g : ℝ → ℝ≥0∞) (a b c : ℝ) :
    ∫⁻ t in Set.Ioc a b, g (t + c) = ∫⁻ s in Set.Ioc (a + c) (b + c), g s := by
  rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioc]
  have e : (Set.Ioc a b).indicator (fun t => g (t + c))
      = fun t => (Set.Ioc (a + c) (b + c)).indicator g (t + c) := by
    funext t
    by_cases h : t ∈ Set.Ioc a b
    · have h' : t + c ∈ Set.Ioc (a + c) (b + c) := ⟨by linarith [h.1], by linarith [h.2]⟩
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
    · have h' : t + c ∉ Set.Ioc (a + c) (b + c) := by
        intro h''
        exact h ⟨by linarith [h''.1], by linarith [h''.2]⟩
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
  rw [e]
  exact lintegral_add_right_eq_self _ c

def DI (F : S.Ω × ℝ → ℝ≥0∞) (s : Set ℝ) : ℝ≥0∞ := ∫⁻ ω, (∫⁻ t in s, F (ω, t)) ∂S.ν

lemma DI_add {F G : S.Ω × ℝ → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G) (c : ℝ≥0∞)
    (s : Set ℝ) : DI (fun p => F p + c * G p) s = DI F s + c * DI G s := by
  unfold DI
  have h1 : ∀ ω, ∫⁻ t in s, (F (ω, t) + c * G (ω, t))
      = (∫⁻ t in s, F (ω, t)) + c * ∫⁻ t in s, G (ω, t) := by
    intro ω
    have hFt : Measurable (fun t => F (ω, t)) := hF.comp (measurable_const.prodMk measurable_id)
    have hGt : Measurable (fun t => G (ω, t)) := hG.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_add_left hFt, lintegral_const_mul _ hGt]
  simp_rw [h1]
  have hF' : Measurable (fun ω => ∫⁻ t in s, F (ω, t)) :=
    hF.lintegral_prod_right' (ν := volume.restrict s)
  have hG' : Measurable (fun ω => ∫⁻ t in s, G (ω, t)) :=
    hG.lintegral_prod_right' (ν := volume.restrict s)
  rw [lintegral_add_left hF', lintegral_const_mul _ hG']

lemma DI_mono {F G : S.Ω × ℝ → ℝ≥0∞} (hG : Measurable G) {s : Set ℝ}
    (h : ∀ ω t, t ∈ s → F (ω, t) ≤ G (ω, t)) : DI F s ≤ DI G s :=
  lintegral_mono (fun ω => setLIntegral_mono (hG.comp (measurable_const.prodMk measurable_id))
    (fun t ht => h ω t ht))

lemma DI_congr {F G : S.Ω × ℝ → ℝ≥0∞} {s : Set ℝ} (hs : MeasurableSet s)
    (h : ∀ ω t, t ∈ s → F (ω, t) = G (ω, t)) : DI F s = DI G s :=
  lintegral_congr (fun ω => setLIntegral_congr_fun hs (fun t ht => h ω t ht))

lemma DI_union {F : S.Ω × ℝ → ℝ≥0∞} (hF : Measurable F) {s₁ s₂ : Set ℝ} (hd : Disjoint s₁ s₂)
    (hs₂ : MeasurableSet s₂) : DI F (s₁ ∪ s₂) = DI F s₁ + DI F s₂ := by
  unfold DI
  simp_rw [lintegral_union hs₂ hd]
  have hF' : Measurable (fun ω => ∫⁻ t in s₁, F (ω, t)) :=
    hF.lintegral_prod_right' (ν := volume.restrict s₁)
  rw [lintegral_add_left hF']

lemma DI_mono_set {F : S.Ω × ℝ → ℝ≥0∞} {s₁ s₂ : Set ℝ} (h : s₁ ⊆ s₂) : DI F s₁ ≤ DI F s₂ :=
  lintegral_mono (fun ω => lintegral_mono_set h)

lemma DI_swap {F : S.Ω × ℝ → ℝ≥0∞} (hF : Measurable F) (s : Set ℝ) :
    DI F s = ∫⁻ t in s, (∫⁻ ω, F (ω, t) ∂S.ν) := by
  unfold DI
  exact lintegral_lintegral_swap (μ := S.ν) (ν := volume.restrict s)
    (f := fun ω t => F (ω, t)) hF.aemeasurable

lemma Ioc_split {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    Set.Ioc a c = Set.Ioc a b ∪ Set.Ioc b c := (Set.Ioc_union_Ioc_eq_Ioc hab hbc).symm

variable (π : ShipmentPolicy P S)

def IP1 (t : ℝ) (ω : S.Ω) : ℤ := π.x1 ω + π.U1 t ω - S.N t ω
def IP2 (t : ℝ) (ω : S.Ω) : ℤ := π.x2 ω + π.U2 t ω - S.N t ω
def IL1 (t : ℝ) (ω : S.Ω) : ℤ := netInv P.L1 π.x1 π.U1 S.N t ω
def IL2 (t : ℝ) (ω : S.Ω) : ℤ := netInv P.L2 π.x2 π.U2 S.N t ω

def pr1 : Proc S := ⟨π.x1, π.U1, π.x1_meas, π.U1_adapted, π.U1_mono, π.U1_rcont⟩
def pr2 : Proc S := ⟨π.x2, π.U2, π.x2_meas, π.U2_adapted, π.U2_mono, π.U2_rcont⟩

lemma IL1_shift (t : ℝ) (ω : S.Ω) :
    IL1 π (t + P.L1) ω = IP1 π t ω - (S.N (t + P.L1) ω - S.N t ω) := by
  unfold IL1 IP1 netInv
  rw [add_sub_cancel_right]
  ring

lemma IL2_shift (t : ℝ) (ω : S.Ω) :
    IL2 π (t + P.L2) ω = IP2 π t ω - (S.N (t + P.L2) ω - S.N t ω) := by
  unfold IL2 IP2 netInv
  rw [add_sub_cancel_right]
  ring

lemma mat {t : ℝ} (ht : 0 ≤ t) (ω : S.Ω) : IP1 π t ω ≤ IL2 π t ω := by
  unfold IP1 IL2 netInv
  have := π.material ω t ht
  linarith

lemma IL1_le_IL2 {t : ℝ} (ht : 0 ≤ t) (ω : S.Ω) : IL1 π t ω ≤ IL2 π t ω := by
  have h1 := mat π ht ω
  have h2 : π.U1 (t - P.L1) ω ≤ π.U1 t ω := π.U1_mono ω (by linarith [P.L1_nonneg])
  unfold IL1 netInv
  unfold IP1 at h1
  linarith

lemma IP1_adapted {t : ℝ} (ht : 0 ≤ t) : Measurable[S.𝓕 t] (IP1 π t) :=
  X_adapted (pr1 π) ht

lemma IP2_adapted {t : ℝ} (ht : 0 ≤ t) : Measurable[S.𝓕 t] (IP2 π t) :=
  X_adapted (pr2 π) ht

lemma U1_joint : Measurable (fun p : S.Ω × ℝ => π.U1 p.2 p.1) :=
  joint_meas (U_m (pr1 π)) π.U1_rcont

lemma U2_joint : Measurable (fun p : S.Ω × ℝ => π.U2 p.2 p.1) :=
  joint_meas (U_m (pr2 π)) π.U2_rcont

lemma IP1_joint : Measurable (fun p : S.Ω × ℝ => IP1 π p.2 p.1) := X_joint (pr1 π)

lemma IP2_joint : Measurable (fun p : S.Ω × ℝ => IP2 π p.2 p.1) := X_joint (pr2 π)

lemma IL1_joint : Measurable (fun p : S.Ω × ℝ => IL1 π p.2 p.1) := by
  unfold IL1 netInv
  exact (((x_m (pr1 π)).comp measurable_fst).add ((U1_joint π).comp
    (measurable_fst.prodMk (measurable_snd.sub_const _)))).sub S.N_joint

lemma IL2_joint : Measurable (fun p : S.Ω × ℝ => IL2 π p.2 p.1) := by
  unfold IL2 netInv
  exact (((x_m (pr2 π)).comp measurable_fst).add ((U2_joint π).comp
    (measurable_fst.prodMk (measurable_snd.sub_const _)))).sub S.N_joint

lemma cI_eq (t : ℝ) (ω : S.Ω) :
    π.cI t ω = P.h1 * max (IL1 π t ω : ℝ) 0 + P.h2 * ((IL2 π t ω : ℝ) + max (-(IL1 π t ω : ℝ)) 0)
      + P.p * max (-(IL1 π t ω : ℝ)) 0 := rfl

def c1 (η ζ : ℝ) (t : ℝ) (ω : S.Ω) : ℝ :=
  P.h1 * max (IL1 π t ω : ℝ) 0 + η * P.h2 * ((IL2 π t ω : ℝ) + max (-(IL1 π t ω : ℝ)) 0)
    + ζ * P.p * max (-(IL1 π t ω : ℝ)) 0

def c2 (η ζ : ℝ) (t : ℝ) (ω : S.Ω) : ℝ :=
  (1 - η) * P.h2 * ((IL2 π t ω : ℝ) + max (-(IL1 π t ω : ℝ)) 0)
    + (1 - ζ) * P.p * max (-(IL1 π t ω : ℝ)) 0

lemma c1_add_c2 (η ζ t : ℝ) (ω : S.Ω) : c1 π η ζ t ω + c2 π η ζ t ω = π.cI t ω := by
  rw [cI_eq]; unfold c1 c2; ring

lemma I2_nonneg {t : ℝ} (ht : 0 ≤ t) (ω : S.Ω) :
    0 ≤ (IL2 π t ω : ℝ) + max (-(IL1 π t ω : ℝ)) 0 := by
  have h := IL1_le_IL2 π ht ω
  have h' : (IL1 π t ω : ℝ) ≤ (IL2 π t ω : ℝ) := by exact_mod_cast h
  have := le_max_left (-(IL1 π t ω : ℝ)) 0
  linarith

lemma c1_nonneg {η ζ : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (hζ : ζ ∈ Set.Icc (0 : ℝ) 1) {t : ℝ}
    (ht : 0 ≤ t) (ω : S.Ω) : 0 ≤ c1 π η ζ t ω := by
  unfold c1
  have := I2_nonneg π ht ω
  have := P.h1_nonneg; have := P.h2_nonneg; have := P.p_nonneg
  have := hη.1; have := hζ.1
  have h1 : 0 ≤ max (IL1 π t ω : ℝ) 0 := le_max_right _ _
  have h2 : 0 ≤ max (-(IL1 π t ω : ℝ)) 0 := le_max_right _ _
  positivity

lemma c2_nonneg {η ζ : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (hζ : ζ ∈ Set.Icc (0 : ℝ) 1) {t : ℝ}
    (ht : 0 ≤ t) (ω : S.Ω) : 0 ≤ c2 π η ζ t ω := by
  unfold c2
  have := I2_nonneg π ht ω
  have := P.h2_nonneg; have := P.p_nonneg
  have h3 : 0 ≤ 1 - η := by linarith [hη.2]
  have h4 : 0 ≤ 1 - ζ := by linarith [hζ.2]
  have h2 : 0 ≤ max (-(IL1 π t ω : ℝ)) 0 := le_max_right _ _
  positivity

lemma c1_meas (η ζ : ℝ) : Measurable (fun p : S.Ω × ℝ => ENNReal.ofReal (c1 π η ζ p.2 p.1)) := by
  unfold c1
  have h1 : Measurable (fun p : S.Ω × ℝ => (IL1 π p.2 p.1 : ℝ)) :=
    (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp (IL1_joint π)
  have h2 : Measurable (fun p : S.Ω × ℝ => (IL2 π p.2 p.1 : ℝ)) :=
    (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp (IL2_joint π)
  exact ENNReal.measurable_ofReal.comp ((((h1.max measurable_const).const_mul _).add
    ((h2.add (h1.neg.max measurable_const)).const_mul _)).add
    ((h1.neg.max measurable_const).const_mul _))

lemma c2_meas (η ζ : ℝ) : Measurable (fun p : S.Ω × ℝ => ENNReal.ofReal (c2 π η ζ p.2 p.1)) := by
  unfold c2
  have h1 : Measurable (fun p : S.Ω × ℝ => (IL1 π p.2 p.1 : ℝ)) :=
    (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp (IL1_joint π)
  have h2 : Measurable (fun p : S.Ω × ℝ => (IL2 π p.2 p.1 : ℝ)) :=
    (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp (IL2_joint π)
  exact ENNReal.measurable_ofReal.comp
    (((h2.add (h1.neg.max measurable_const)).const_mul _).add
    ((h1.neg.max measurable_const).const_mul _))

end LBA

end TwoStageRnQ

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace LBA

open TwoStageRnQ.LB TwoStageRnQ.LBP

variable {P : Params} {S : DemandSpace P} (π : ShipmentPolicy P S)

lemma max_sub_max (x : ℝ) : max x 0 - max (-x) 0 = x := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

lemma zmeas (f : ℤ → ℝ≥0∞) {Y : S.Ω × ℝ → ℤ} (hY : Measurable Y) : Measurable (fun p => f (Y p)) :=
  (measurable_of_countable f).comp hY

theorem comp1 {η ζ : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (hζ : ζ ∈ Set.Icc (0 : ℝ) 1)
    (Ψ : S.Ω × ℝ → ℝ) (hΨm : Measurable (fun p => ENNReal.ofReal (Ψ p))) (hΨ0 : ∀ p, 0 ≤ Ψ p)
    (hΨ : ∀ ω t, 0 ≤ t → Ψ (ω, t) + η * P.h2 * max (-(IL2 π t ω : ℝ)) 0
        ≤ pexp P.mu1 (fun d : ℕ => phi P.h1 (ζ * P.p + η * P.h2) ((IP1 π t ω : ℝ) - d))
          + η * P.h2 * max (IL2 π t ω : ℝ) 0)
    {T : ℝ} (hT : 2 * P.L1 ≤ T)
    (hfin : DI (fun p => ENNReal.ofReal |(IL2 π p.2 p.1 : ℝ)|) (Set.Ioc 0 T) ≠ ⊤) :
    DI (fun p => ENNReal.ofReal (Ψ p)) (Set.Ioc 0 (T - P.L1))
      ≤ DI (fun p => ENNReal.ofReal (c1 π η ζ p.2 p.1)) (Set.Ioc 0 T)
        + ENNReal.ofReal (η * P.h2) * (DI (fun p => ENNReal.ofReal |(IL2 π p.2 p.1 : ℝ)|) (Set.Ioc 0 P.L1)
          + DI (fun p => ENNReal.ofReal |(IL2 π p.2 p.1 : ℝ)|) (Set.Ioc (T - P.L1) T)) := by
  have hL1 := P.L1_nonneg
  have hb : 0 ≤ ζ * P.p + η * P.h2 :=
    add_nonneg (mul_nonneg hζ.1 P.p_nonneg) (mul_nonneg hη.1 P.h2_nonneg)
  have hc : 0 ≤ η * P.h2 := mul_nonneg hη.1 P.h2_nonneg
  set c := ENNReal.ofReal (η * P.h2) with hcdef

  set fp : S.Ω × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (max (IL2 π p.2 p.1 : ℝ) 0) with hfp
  set fm : S.Ω × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (max (-(IL2 π p.2 p.1 : ℝ)) 0) with hfm
  set fa : S.Ω × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal |(IL2 π p.2 p.1 : ℝ)| with hfa
  set Gt : S.Ω × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal
    (pexp P.mu1 (fun d : ℕ => phi P.h1 (ζ * P.p + η * P.h2) ((IP1 π p.2 p.1 : ℝ) - d))) with hGt
  set Ph : S.Ω × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal
    (phi P.h1 (ζ * P.p + η * P.h2) (IL1 π p.2 p.1 : ℝ)) with hPh
  set Cc : S.Ω × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (c1 π η ζ p.2 p.1) with hCc
  have mfp : Measurable fp := zmeas (fun z : ℤ => ENNReal.ofReal (max (z : ℝ) 0)) (IL2_joint π)
  have mfm : Measurable fm := zmeas (fun z : ℤ => ENNReal.ofReal (max (-(z : ℝ)) 0)) (IL2_joint π)
  have mfa : Measurable fa := zmeas (fun z : ℤ => ENNReal.ofReal |(z : ℝ)|) (IL2_joint π)
  have mGt : Measurable Gt := zmeas (fun z : ℤ => ENNReal.ofReal
    (pexp P.mu1 (fun d : ℕ => phi P.h1 (ζ * P.p + η * P.h2) ((z : ℝ) - d)))) (IP1_joint π)
  have mPh : Measurable Ph := zmeas (fun z : ℤ => ENNReal.ofReal
    (phi P.h1 (ζ * P.p + η * P.h2) (z : ℝ))) (IL1_joint π)
  have mCc : Measurable Cc := c1_meas π η ζ
  set A := Set.Ioc (0 : ℝ) (T - P.L1) with hA
  set B := Set.Ioc P.L1 T with hB

  have hI : DI (fun p => ENNReal.ofReal (Ψ p)) A + c * DI fm A ≤ DI Gt A + c * DI fp A := by
    rw [← DI_add hΨm mfm, ← DI_add mGt mfp]
    refine DI_mono (G := fun p => Gt p + c * fp p) (by exact mGt.add (mfp.const_mul _))
      (fun ω t ht => ?_)
    have h := hΨ ω t ht.1.le
    simp only [hfm, hfp, hGt, hcdef]
    rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul hc,
      ← ENNReal.ofReal_add (hΨ0 _) (mul_nonneg hc (le_max_right _ _)),
      ← ENNReal.ofReal_add (pexp_nonneg P.mu1_nonneg (fun d => phi_nonneg P.h1_nonneg hb _))
        (mul_nonneg hc (le_max_right _ _))]
    exact ENNReal.ofReal_le_ofReal (by linarith)

  have hII : DI Cc B + c * DI fm B = DI Ph B + c * DI fp B := by
    rw [← DI_add mCc mfm, ← DI_add mPh mfp]
    refine DI_congr measurableSet_Ioc (fun ω s hs => ?_)
    have hs0 : 0 ≤ s := le_trans hL1 hs.1.le
    simp only [hCc, hfm, hPh, hfp, hcdef]
    rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul hc,
      ← ENNReal.ofReal_add (c1_nonneg π hη hζ hs0 ω) (mul_nonneg hc (le_max_right _ _)),
      ← ENNReal.ofReal_add (phi_nonneg P.h1_nonneg hb _) (mul_nonneg hc (le_max_right _ _))]
    congr 1
    unfold c1 phi
    have e := max_sub_max (IL2 π s ω : ℝ)
    nlinarith [e]

  have hIII : DI Gt A = DI Ph B := by
    rw [DI_swap mGt, DI_swap mPh]
    have h1 : ∀ t ∈ A, ∫⁻ ω, Gt (ω, t) ∂S.ν = ∫⁻ ω, Ph (ω, t + P.L1) ∂S.ν := by
      intro t ht
      have hcond := cond_f (v := t) (w := t + P.L1) ht.1.le (by linarith) (IP1_adapted π ht.1.le)
        (phi P.h1 (ζ * P.p + η * P.h2)) (phi_nonneg P.h1_nonneg hb)
        (fun a => (phi_linGrowth P.h1_nonneg hb (a : ℝ)).pint
          (mul_nonneg P.lam_nonneg (by linarith)))
      rw [show P.lam * (t + P.L1 - t) = P.mu1 by unfold Params.mu1; ring] at hcond
      simp only [hGt, hPh]
      rw [← hcond]
      refine lintegral_congr (fun ω => ?_)
      rw [IL1_shift]
    rw [setLIntegral_congr_fun measurableSet_Ioc h1,
      lintegral_Ioc_shift (fun s => ∫⁻ ω, Ph (ω, s) ∂S.ν) 0 (T - P.L1) P.L1, zero_add, sub_add_cancel]

  have hIV : DI fp A + DI fm B ≤ DI fm A + DI fp B
      + (DI fa (Set.Ioc 0 P.L1) + DI fa (Set.Ioc (T - P.L1) T)) := by
    have hsA : A = Set.Ioc 0 P.L1 ∪ Set.Ioc P.L1 (T - P.L1) := Ioc_split hL1 (by linarith)
    have hsB : B = Set.Ioc P.L1 (T - P.L1) ∪ Set.Ioc (T - P.L1) T := Ioc_split (by linarith) (by linarith)
    have hd1 : Disjoint (Set.Ioc 0 P.L1) (Set.Ioc P.L1 (T - P.L1)) := Set.Ioc_disjoint_Ioc_of_le le_rfl
    have hd2 : Disjoint (Set.Ioc P.L1 (T - P.L1)) (Set.Ioc (T - P.L1) T) :=
      Set.Ioc_disjoint_Ioc_of_le le_rfl
    rw [hsA, hsB, DI_union mfp hd1 measurableSet_Ioc, DI_union mfm hd2 measurableSet_Ioc,
      DI_union mfm hd1 measurableSet_Ioc, DI_union mfp hd2 measurableSet_Ioc]
    have e1 : DI fp (Set.Ioc 0 P.L1) ≤ DI fa (Set.Ioc 0 P.L1) :=
      DI_mono mfa (fun ω t _ => ENNReal.ofReal_le_ofReal (by
        rcases le_total 0 (IL2 π t ω : ℝ) with h | h
        · rw [max_eq_left h, abs_of_nonneg h]
        · rw [max_eq_right h]; exact abs_nonneg _))
    have e2 : DI fm (Set.Ioc (T - P.L1) T) ≤ DI fa (Set.Ioc (T - P.L1) T) :=
      DI_mono mfa (fun ω t _ => ENNReal.ofReal_le_ofReal (by
        rcases le_total 0 (IL2 π t ω : ℝ) with h | h
        · rw [max_eq_right (by linarith)]; exact abs_nonneg _
        · rw [max_eq_left (by linarith), abs_of_nonpos h]))
    calc DI fp (Set.Ioc 0 P.L1) + DI fp (Set.Ioc P.L1 (T - P.L1))
          + (DI fm (Set.Ioc P.L1 (T - P.L1)) + DI fm (Set.Ioc (T - P.L1) T))
        ≤ DI fa (Set.Ioc 0 P.L1) + DI fp (Set.Ioc P.L1 (T - P.L1))
          + (DI fm (Set.Ioc P.L1 (T - P.L1)) + DI fa (Set.Ioc (T - P.L1) T)) := by
          gcongr
      _ ≤ DI fm (Set.Ioc 0 P.L1) + DI fm (Set.Ioc P.L1 (T - P.L1))
          + (DI fp (Set.Ioc P.L1 (T - P.L1)) + DI fp (Set.Ioc (T - P.L1) T))
          + (DI fa (Set.Ioc 0 P.L1) + DI fa (Set.Ioc (T - P.L1) T)) := by
          calc _ = 0 + DI fm (Set.Ioc P.L1 (T - P.L1)) + (DI fp (Set.Ioc P.L1 (T - P.L1)) + 0)
                + (DI fa (Set.Ioc 0 P.L1) + DI fa (Set.Ioc (T - P.L1) T)) := by ring
            _ ≤ _ := by gcongr <;> exact zero_le

  have hsub1 : A ⊆ Set.Ioc 0 T := Set.Ioc_subset_Ioc le_rfl (by linarith)
  have hsub2 : B ⊆ Set.Ioc 0 T := Set.Ioc_subset_Ioc hL1 le_rfl
  have hfinAB : DI fm A + DI fp B ≠ ⊤ := by
    have h1 : DI fm A ≤ DI fa (Set.Ioc 0 T) :=
      le_trans (DI_mono mfa (fun ω t _ => ENNReal.ofReal_le_ofReal (by
        rcases le_total 0 (IL2 π t ω : ℝ) with h | h
        · rw [max_eq_right (by linarith)]; exact abs_nonneg _
        · rw [max_eq_left (by linarith), abs_of_nonpos h]))) (DI_mono_set hsub1)
    have h2 : DI fp B ≤ DI fa (Set.Ioc 0 T) :=
      le_trans (DI_mono mfa (fun ω t _ => ENNReal.ofReal_le_ofReal (by
        rcases le_total 0 (IL2 π t ω : ℝ) with h | h
        · rw [max_eq_left h, abs_of_nonneg h]
        · rw [max_eq_right h]; exact abs_nonneg _))) (DI_mono_set hsub2)
    exact ENNReal.add_ne_top.mpr ⟨ne_top_of_le_ne_top hfin h1, ne_top_of_le_ne_top hfin h2⟩
  have hcfin : c * (DI fm A + DI fp B) ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinAB

  have key : DI (fun p => ENNReal.ofReal (Ψ p)) A + c * (DI fm A + DI fp B)
      ≤ DI Cc B + c * (DI fa (Set.Ioc 0 P.L1) + DI fa (Set.Ioc (T - P.L1) T))
        + c * (DI fm A + DI fp B) := by
    calc DI (fun p => ENNReal.ofReal (Ψ p)) A + c * (DI fm A + DI fp B)
        = (DI (fun p => ENNReal.ofReal (Ψ p)) A + c * DI fm A) + c * DI fp B := by ring
      _ ≤ (DI Gt A + c * DI fp A) + c * DI fp B := by gcongr
      _ = (DI Ph B + c * DI fp B) + c * DI fp A := by rw [hIII]; ring
      _ = (DI Cc B + c * DI fm B) + c * DI fp A := by rw [hII]
      _ = DI Cc B + c * (DI fp A + DI fm B) := by ring
      _ ≤ DI Cc B + c * (DI fm A + DI fp B
            + (DI fa (Set.Ioc 0 P.L1) + DI fa (Set.Ioc (T - P.L1) T))) := by gcongr
      _ = _ := by ring
  have h5 := (ENNReal.add_le_add_iff_right hcfin).mp key
  calc DI (fun p => ENNReal.ofReal (Ψ p)) A ≤ DI Cc B
        + c * (DI fa (Set.Ioc 0 P.L1) + DI fa (Set.Ioc (T - P.L1) T)) := h5
    _ ≤ DI Cc (Set.Ioc 0 T) + c * (DI fa (Set.Ioc 0 P.L1) + DI fa (Set.Ioc (T - P.L1) T)) := by
        gcongr
        exact DI_mono_set hsub2

end LBA

end TwoStageRnQ

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace LBA

open TwoStageRnQ.LB TwoStageRnQ.LBP

variable {P : Params} {S : DemandSpace P} (π : ShipmentPolicy P S)

lemma c2_ge {η ζ : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (hζ : ζ ∈ Set.Icc (0 : ℝ) 1) {t : ℝ}
    (ht : 0 ≤ t) (ω : S.Ω) :
    phi ((1 - η) * P.h2) ((1 - ζ) * P.p)
        (((IP2 π t ω - (S.N (t + P.L2 + P.L1) ω - S.N t ω) : ℤ) : ℝ))
      ≤ c2 π η ζ (t + P.L2 + P.L1) ω := by
  have hL1 := P.L1_nonneg
  have hL2 := P.L2_nonneg
  have hm := π.material ω (t + P.L2) (by linarith)
  rw [add_sub_cancel_right] at hm
  have hU2 : π.U2 t ω ≤ π.U2 (t + P.L1) ω := π.U2_mono ω (by linarith)
  have e1 : IL1 π (t + P.L2 + P.L1) ω = π.x1 ω + π.U1 (t + P.L2) ω - S.N (t + P.L2 + P.L1) ω := by
    unfold IL1 netInv; rw [add_sub_cancel_right]
  have e2 : IL2 π (t + P.L2 + P.L1) ω = π.x2 ω + π.U2 (t + P.L1) ω - S.N (t + P.L2 + P.L1) ω := by
    unfold IL2 netInv; congr 3; ring
  set Z : ℤ := IP2 π t ω - (S.N (t + P.L2 + P.L1) ω - S.N t ω) with hZ
  have hZ1 : IL1 π (t + P.L2 + P.L1) ω ≤ Z := by rw [e1, hZ]; unfold IP2; linarith
  have hZ2 : Z ≤ IL2 π (t + P.L2 + P.L1) ω := by rw [e2, hZ]; unfold IP2; linarith
  have r1 : ((IL1 π (t + P.L2 + P.L1) ω : ℤ) : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hZ1
  have r2 : (Z : ℝ) ≤ ((IL2 π (t + P.L2 + P.L1) ω : ℤ) : ℝ) := by exact_mod_cast hZ2
  have ha : 0 ≤ (1 - η) * P.h2 := mul_nonneg (by linarith [hη.2]) P.h2_nonneg
  have hb : 0 ≤ (1 - ζ) * P.p := mul_nonneg (by linarith [hζ.2]) P.p_nonneg
  unfold phi c2
  have m1 : max (-(Z : ℝ)) 0 ≤ max (-((IL1 π (t + P.L2 + P.L1) ω : ℤ) : ℝ)) 0 :=
    max_le_max (by linarith) le_rfl
  have m2 : max (Z : ℝ) 0 ≤ ((IL2 π (t + P.L2 + P.L1) ω : ℤ) : ℝ)
      + max (-((IL1 π (t + P.L2 + P.L1) ω : ℤ) : ℝ)) 0 := by
    rcases le_total 0 (Z : ℝ) with h | h
    · rw [max_eq_left h]; have := le_max_right (-((IL1 π (t + P.L2 + P.L1) ω : ℤ) : ℝ)) 0; linarith
    · rw [max_eq_right h]
      have := le_max_left (-((IL1 π (t + P.L2 + P.L1) ω : ℤ) : ℝ)) 0
      linarith
  have := mul_le_mul_of_nonneg_left m1 hb
  have := mul_le_mul_of_nonneg_left m2 ha
  linarith

lemma pexp_phi_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {μ : ℝ} (hμ : 0 ≤ μ) (y : ℝ) :
    pexp μ (fun d : ℕ => phi a b (y - d)) ≤ (a + b) * (|y| + μ) := by
  have h1 : PInt μ (fun d : ℕ => phi a b (y - d)) := (phi_linGrowth ha hb y).pint hμ
  have h2 : PInt μ (fun d : ℕ => (a + b) * (|y| + (d : ℝ))) :=
    ((pint_const |y|).add hμ pint_nat).const_mul (a + b)
  calc pexp μ (fun d : ℕ => phi a b (y - d)) ≤ pexp μ (fun d : ℕ => (a + b) * (|y| + (d : ℝ))) :=
        pexp_mono hμ h1 h2 (fun d => by
          have := phi_abs_le ha hb (y - d)
          have := abs_sub_nat y d
          have h3 := le_abs_self (phi a b (y - d))
          nlinarith)
    _ = (a + b) * (|y| + μ) := by
        rw [pexp_const_mul, pexp_add hμ (pint_const _) pint_nat, pexp_const, pexp_nat]

lemma pint_pexp_phi {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {μ ν : ℝ} (hμ : 0 ≤ μ) (hν : 0 ≤ ν)
    (y : ℝ) : PInt ν (fun d : ℕ => pexp μ (fun d1 : ℕ => phi a b (y - d - d1))) := by
  refine PInt.of_abs_le hν (((pint_const ((a + b) * (|y| + μ))).add hν pint_nat).const_mul 1
    |>.add hν (pint_nat.const_mul (a + b))) (fun d => ?_)
  have h0 : 0 ≤ pexp μ (fun d1 : ℕ => phi a b (y - d - d1)) :=
    pexp_nonneg hμ (fun d1 => phi_nonneg ha hb _)
  rw [abs_of_nonneg h0]
  have h1 := pexp_phi_le ha hb hμ (y - d)
  have h2 := abs_sub_nat y d
  have hab : 0 ≤ a + b := add_nonneg ha hb
  have : (a + b) * (|y - (d : ℝ)| + μ) ≤ (a + b) * (|y| + μ) + (a + b) * d := by nlinarith
  simp only [one_mul]
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith

lemma pexp_swap {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {μ ν : ℝ} (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (x : ℝ) :
    ENNReal.ofReal (pexp ν (fun d2 : ℕ => pexp μ (fun d1 : ℕ => phi a b (x - d2 - d1))))
      = ENNReal.ofReal (pexp μ (fun d1 : ℕ => pexp ν (fun d2 : ℕ => phi a b (x - d1 - d2)))) := by
  open TwoStageRnQ.Prop1 in
  rw [← tsum_ofReal_pexp hν (fun d2 => pexp_nonneg hμ (fun d1 => phi_nonneg ha hb _))
      (pint_pexp_phi ha hb hμ hν x),
    ← tsum_ofReal_pexp hμ (fun d1 => pexp_nonneg hν (fun d2 => phi_nonneg ha hb _))
      (pint_pexp_phi ha hb hν hμ x)]
  have e1 : ∀ d2 : ℕ, ENNReal.ofReal (pexp μ (fun d1 : ℕ => phi a b (x - d2 - d1)))
      = ∑' d1 : ℕ, ENNReal.ofReal (poisW μ d1) * ENNReal.ofReal (phi a b (x - d2 - d1)) :=
    fun d2 => (tsum_ofReal_pexp hμ (fun d1 => phi_nonneg ha hb _)
      ((phi_linGrowth ha hb (x - d2)).pint hμ)).symm
  have e2 : ∀ d1 : ℕ, ENNReal.ofReal (pexp ν (fun d2 : ℕ => phi a b (x - d1 - d2)))
      = ∑' d2 : ℕ, ENNReal.ofReal (poisW ν d2) * ENNReal.ofReal (phi a b (x - d1 - d2)) :=
    fun d1 => (tsum_ofReal_pexp hν (fun d2 => phi_nonneg ha hb _)
      ((phi_linGrowth ha hb (x - d1)).pint hν)).symm
  simp_rw [e1, e2, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun d1 => tsum_congr (fun d2 => ?_))
  rw [show x - (d2 : ℝ) - d1 = x - d1 - d2 by ring]
  ring

theorem comp2 {η ζ : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (hζ : ζ ∈ Set.Icc (0 : ℝ) 1) {T : ℝ}
    (hT : P.L1 + P.L2 ≤ T) :
    DI (fun p => ENNReal.ofReal (P.allocF2 η ζ (IP2 π p.2 p.1))) (Set.Ioc 0 (T - (P.L1 + P.L2)))
      ≤ DI (fun p => ENNReal.ofReal (c2 π η ζ p.2 p.1)) (Set.Ioc 0 T) := by
  have hL1 := P.L1_nonneg
  have hL2 := P.L2_nonneg
  have ha : 0 ≤ (1 - η) * P.h2 := mul_nonneg (by linarith [hη.2]) P.h2_nonneg
  have hb : 0 ≤ (1 - ζ) * P.p := mul_nonneg (by linarith [hζ.2]) P.p_nonneg
  have hm1 := P.mu1_nonneg
  have hm2 := P.mu2_nonneg
  have mF : Measurable (fun p : S.Ω × ℝ => ENNReal.ofReal (P.allocF2 η ζ (IP2 π p.2 p.1))) :=
    zmeas (fun z : ℤ => ENNReal.ofReal (P.allocF2 η ζ (z : ℝ))) (IP2_joint π)
  rw [DI_swap mF, DI_swap (c2_meas π η ζ)]

  have hpt : ∀ t ∈ Set.Ioc (0 : ℝ) (T - (P.L1 + P.L2)),
      ∫⁻ ω, ENNReal.ofReal (P.allocF2 η ζ (IP2 π t ω)) ∂S.ν
        ≤ ∫⁻ ω, ENNReal.ofReal (c2 π η ζ (t + (P.L1 + P.L2)) ω) ∂S.ν := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1.le

    set Y : S.Ω → ℤ := fun ω => IP2 π t ω - (S.N (t + P.L2) ω - S.N t ω) with hY
    have hYm : Measurable[S.𝓕 (t + P.L2)] Y :=
      (((IP2_adapted π ht0).mono (S.𝓕.mono (by linarith)) le_rfl).sub
        ((S.N_adapted (t + P.L2)).sub ((S.N_adapted t).mono (S.𝓕.mono (by linarith)) le_rfl)))
    have hA := cond_f (v := t + P.L2) (w := t + P.L2 + P.L1) (by linarith) (by linarith) hYm
      (phi ((1 - η) * P.h2) ((1 - ζ) * P.p)) (phi_nonneg ha hb)
      (fun z => (phi_linGrowth ha hb (z : ℝ)).pint (mul_nonneg P.lam_nonneg (by linarith)))
    rw [show P.lam * (t + P.L2 + P.L1 - (t + P.L2)) = P.mu1 by unfold Params.mu1; ring] at hA
    have hB := cond_f (v := t) (w := t + P.L2) ht0 (by linarith) (IP2_adapted π ht0)
      (fun y => pexp P.mu1 (fun d1 : ℕ => phi ((1 - η) * P.h2) ((1 - ζ) * P.p) (y - d1)))
      (fun y => pexp_nonneg hm1 (fun d1 => phi_nonneg ha hb _))
      (fun z => pint_pexp_phi (ν := P.lam * (t + P.L2 - t)) ha hb hm1
        (mul_nonneg P.lam_nonneg (by linarith)) (z : ℝ))
    rw [show P.lam * (t + P.L2 - t) = P.mu2 by unfold Params.mu2; ring] at hB
    have e1 : ∀ ω, ENNReal.ofReal (P.allocF2 η ζ (IP2 π t ω))
        = ENNReal.ofReal (pexp P.mu2 (fun d2 : ℕ => pexp P.mu1 (fun d1 : ℕ =>
            phi ((1 - η) * P.h2) ((1 - ζ) * P.p) ((IP2 π t ω : ℝ) - d2 - d1)))) := by
      intro ω
      unfold Params.allocF2
      rw [pexp_swap ha hb hm1 hm2]
    calc ∫⁻ ω, ENNReal.ofReal (P.allocF2 η ζ (IP2 π t ω)) ∂S.ν
        = ∫⁻ ω, ENNReal.ofReal (pexp P.mu1 (fun d1 : ℕ =>
            phi ((1 - η) * P.h2) ((1 - ζ) * P.p) (((Y ω : ℤ) : ℝ) - d1))) ∂S.ν := by
          rw [lintegral_congr e1, ← hB]
      _ = ∫⁻ ω, ENNReal.ofReal (phi ((1 - η) * P.h2) ((1 - ζ) * P.p)
            (((IP2 π t ω - (S.N (t + P.L2 + P.L1) ω - S.N t ω) : ℤ) : ℝ))) ∂S.ν := by
          rw [← hA]
          refine lintegral_congr (fun ω => ?_)
          congr 3
          rw [hY]
          ring
      _ ≤ ∫⁻ ω, ENNReal.ofReal (c2 π η ζ (t + (P.L1 + P.L2)) ω) ∂S.ν := by
          refine lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal ?_)
          have h1 := c2_ge π hη hζ ht0 ω
          have e : c2 π η ζ (t + P.L2 + P.L1) ω = c2 π η ζ (t + (P.L1 + P.L2)) ω := by
            congr 1; ring
          exact h1.trans (le_of_eq e)
  calc ∫⁻ t in Set.Ioc 0 (T - (P.L1 + P.L2)), ∫⁻ ω, ENNReal.ofReal (P.allocF2 η ζ (IP2 π t ω)) ∂S.ν
      ≤ ∫⁻ t in Set.Ioc 0 (T - (P.L1 + P.L2)),
          ∫⁻ ω, ENNReal.ofReal (c2 π η ζ (t + (P.L1 + P.L2)) ω) ∂S.ν :=
        setLIntegral_mono' measurableSet_Ioc hpt
    _ = ∫⁻ s in Set.Ioc (0 + (P.L1 + P.L2)) (T - (P.L1 + P.L2) + (P.L1 + P.L2)),
          ∫⁻ ω, ENNReal.ofReal (c2 π η ζ s ω) ∂S.ν :=
        lintegral_Ioc_shift (fun s => ∫⁻ ω, ENNReal.ofReal (c2 π η ζ s ω) ∂S.ν) _ _ _
    _ ≤ ∫⁻ s in Set.Ioc 0 T, ∫⁻ ω, ENNReal.ofReal (c2 π η ζ s ω) ∂S.ν := by
        rw [zero_add, sub_add_cancel]
        exact lintegral_mono_set (Set.Ioc_subset_Ioc (by linarith) le_rfl)

end LBA

end TwoStageRnQ

open MeasureTheory Filter Topology Finset
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace LBE

variable (P : Params)

lemma hb1 : 0 ≤ 1 * P.p + 1 * P.h2 := by
  have := P.p_nonneg; have := P.h2_nonneg; linarith

def Gadj (x : ℝ) : ℝ := pexp P.mu1 (fun d : ℕ => phi P.h1 (1 * P.p + 1 * P.h2) (x - d))

lemma Gadj_nonneg (x : ℝ) : 0 ≤ Gadj P x :=
  pexp_nonneg P.mu1_nonneg (fun d => phi_nonneg P.h1_nonneg (hb1 P) _)

lemma G0_eq (x : ℝ) : P.G0 x = Gadj P x + P.h2 * x := by
  have hμ := P.mu1_nonneg
  unfold Params.G0 Params.lossDown Gadj
  have e : ∀ d : ℕ, phi (P.h1 + P.h2) P.p (x - d)
      = phi P.h1 (1 * P.p + 1 * P.h2) (x - d) + P.h2 * (x - d) := by
    intro d
    unfold phi
    have := TwoStageRnQ.LBA.max_sub_max (x - d)
    linear_combination P.h2 * this
  simp_rw [e]
  rw [pexp_add hμ ((phi_linGrowth P.h1_nonneg (hb1 P) x).pint hμ)
      (((pint_const x).sub hμ pint_nat).const_mul P.h2),
    pexp_const_mul, pexp_sub hμ (pint_const x) pint_nat, pexp_const, pexp_nat]
  unfold Params.H0 Params.mu1
  ring

lemma phi_convex {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (x y : ℝ) :
    phi a b (θ * x + (1 - θ) * y) ≤ θ * phi a b x + (1 - θ) * phi a b y := by
  unfold phi
  have h1' : 0 ≤ 1 - θ := by linarith
  have m1 : max (θ * x + (1 - θ) * y) 0 ≤ θ * max x 0 + (1 - θ) * max y 0 := by
    refine max_le ?_ (by positivity)
    have := mul_le_mul_of_nonneg_left (le_max_left x 0) h0
    have := mul_le_mul_of_nonneg_left (le_max_left y 0) h1'
    linarith
  have m2 : max (-(θ * x + (1 - θ) * y)) 0 ≤ θ * max (-x) 0 + (1 - θ) * max (-y) 0 := by
    refine max_le ?_ (by positivity)
    have := mul_le_mul_of_nonneg_left (le_max_left (-x) 0) h0
    have := mul_le_mul_of_nonneg_left (le_max_left (-y) 0) h1'
    linarith
  have := mul_le_mul_of_nonneg_left m1 ha
  have := mul_le_mul_of_nonneg_left m2 hb
  nlinarith

lemma Gadj_convex {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (a b : ℝ) :
    Gadj P (θ * a + (1 - θ) * b) ≤ θ * Gadj P a + (1 - θ) * Gadj P b := by
  have hμ := P.mu1_nonneg
  have hpa := (phi_linGrowth P.h1_nonneg (hb1 P) a).pint hμ
  have hpb := (phi_linGrowth P.h1_nonneg (hb1 P) b).pint hμ
  unfold Gadj
  rw [← pexp_const_mul, ← pexp_const_mul, ← pexp_add hμ (hpa.const_mul θ) (hpb.const_mul (1 - θ))]
  refine pexp_mono hμ ((phi_linGrowth P.h1_nonneg (hb1 P) _).pint hμ)
    ((hpa.const_mul θ).add hμ (hpb.const_mul (1 - θ))) (fun d => ?_)
  have e : θ * a + (1 - θ) * b - d = θ * (a - d) + (1 - θ) * (b - d) := by ring
  rw [e]
  exact phi_convex P.h1_nonneg (hb1 P) h0 h1 (a - d) (b - d)

def E0 (x : ℝ) : ℝ := ⨅ v : Set.Iic x, (P.G0 v + P.h2 * (x - v))

lemma E0_term_nonneg (x : ℝ) (v : Set.Iic x) : 0 ≤ P.G0 v + P.h2 * (x - v) :=
  add_nonneg (P.G0_nonneg _) (mul_nonneg P.h2_nonneg (sub_nonneg.mpr v.2))

lemma E0_bdd (x : ℝ) : BddBelow (Set.range fun v : Set.Iic x => P.G0 v + P.h2 * (x - v)) :=
  ⟨0, by rintro _ ⟨v, rfl⟩; exact E0_term_nonneg P x v⟩

lemma E0_le {x v : ℝ} (h : v ≤ x) : E0 P x ≤ P.G0 v + P.h2 * (x - v) :=
  ciInf_le (E0_bdd P x) ⟨v, h⟩

lemma E0_nonneg (x : ℝ) : 0 ≤ E0 P x := by
  haveI : Nonempty (Set.Iic x) := ⟨⟨x, Set.mem_Iic.mpr le_rfl⟩⟩
  exact le_ciInf (fun v => E0_term_nonneg P x v)

lemma E0_le_G0 (x : ℝ) : E0 P x ≤ P.G0 x := by
  have := E0_le P (le_refl x)
  simpa using this

lemma G0_le (x : ℝ) : P.G0 x ≤ P.H0 + (P.h1 + P.h2 + P.p) * (|x| + P.mu1) := by
  unfold Params.G0 Params.lossDown
  have := TwoStageRnQ.LBA.pexp_phi_le P.a_nonneg P.p_nonneg P.mu1_nonneg x
  linarith

lemma pint_E0 {μ : ℝ} (hμ : 0 ≤ μ) (z : ℝ) : PInt μ (fun d : ℕ => E0 P (z - d)) := by
  have hK : 0 ≤ P.h1 + P.h2 + P.p := add_nonneg P.a_nonneg P.p_nonneg
  refine PInt.of_abs_le hμ (((pint_const (P.H0 + (P.h1 + P.h2 + P.p) * (|z| + P.mu1))).add hμ
    (pint_nat.const_mul (P.h1 + P.h2 + P.p)))) (fun d => ?_)
  rw [abs_of_nonneg (E0_nonneg P _)]
  have h1 := E0_le_G0 P (z - d)
  have h2 := G0_le P (z - d)
  have h3 := TwoStageRnQ.abs_sub_nat z d
  have : (P.h1 + P.h2 + P.p) * |z - (d : ℝ)| ≤ (P.h1 + P.h2 + P.p) * (|z| + d) :=
    mul_le_mul_of_nonneg_left h3 hK
  nlinarith

lemma V0_term_nonneg (ry : ℝ × ℝ) : 0 ≤ pexp P.mu2 (fun d : ℕ =>
    P.G0 (ry.1 - max (-(ry.2 - (d : ℝ))) 0) + P.h2 * max (ry.2 - (d : ℝ)) 0) :=
  pexp_nonneg P.mu2_nonneg (fun d => add_nonneg (P.G0_nonneg _)
    (mul_nonneg P.h2_nonneg (le_max_right _ _)))

lemma V0_bdd : BddBelow (Set.range fun ry : ℝ × ℝ => pexp P.mu2 (fun d : ℕ =>
    P.G0 (ry.1 - max (-(ry.2 - (d : ℝ))) 0) + P.h2 * max (ry.2 - (d : ℝ)) 0)) :=
  ⟨0, by rintro _ ⟨ry, rfl⟩; exact V0_term_nonneg P ry⟩

lemma V0_nonneg : 0 ≤ P.V0 := le_ciInf (fun ry => V0_term_nonneg P ry)

theorem envelope (z : ℝ) : P.V0 ≤ pexp P.mu2 (fun d : ℕ => E0 P (z - d)) := by
  have hμ2 := P.mu2_nonneg
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  haveI : Nonempty (Set.Iic z) := ⟨⟨z, Set.mem_Iic.mpr le_rfl⟩⟩
  have hbdd : BddBelow (Set.range fun v : Set.Iic z => Gadj P v) :=
    ⟨0, by rintro _ ⟨v, rfl⟩; exact Gadj_nonneg P v⟩
  obtain ⟨⟨r0, hr0⟩, hr0lt⟩ := exists_lt_of_ciInf_lt
    (lt_add_of_pos_right (⨅ v : Set.Iic z, Gadj P v) hε)
  have hmin : ∀ v, v ≤ z → Gadj P r0 ≤ Gadj P v + ε := by
    intro v hv
    have := ciInf_le hbdd ⟨v, hv⟩
    simp only at hr0lt this
    linarith
  have hkey : ∀ x, x ≤ z → ∀ v, v ≤ x → Gadj P (min r0 x) ≤ Gadj P v + ε := by
    intro x hx v hv
    rcases le_total r0 x with h | h
    · rw [min_eq_left h]; exact hmin v (le_trans hv hx)
    · rw [min_eq_right h]
      rcases eq_or_lt_of_le hv with hve | hvlt
      · rw [hve]; linarith
      · have hrv : 0 < r0 - v := by linarith
        have hθ0 : 0 ≤ (r0 - x) / (r0 - v) := div_nonneg (by linarith) hrv.le
        have hθ1 : (r0 - x) / (r0 - v) ≤ 1 := by rw [div_le_one hrv]; linarith
        have hx_eq : (r0 - x) / (r0 - v) * v + (1 - (r0 - x) / (r0 - v)) * r0 = x := by
          field_simp
          ring
        have hconv := Gadj_convex P hθ0 hθ1 v r0
        rw [hx_eq] at hconv
        have h2 := hmin v (by linarith)
        have h3 : (1 - (r0 - x) / (r0 - v)) * Gadj P r0
            ≤ (1 - (r0 - x) / (r0 - v)) * (Gadj P v + ε) :=
          mul_le_mul_of_nonneg_left h2 (by linarith)
        have h4 : (1 - (r0 - x) / (r0 - v)) * ε ≤ ε := by nlinarith
        nlinarith
  have hobj : ∀ d : ℕ, P.G0 (r0 - max (-((z - r0) - (d : ℝ))) 0) + P.h2 * max ((z - r0) - (d : ℝ)) 0
      ≤ E0 P (z - d) + ε := by
    intro d
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have e1 : r0 - max (-((z - r0) - (d : ℝ))) 0 = min r0 (z - d) := by
      rcases le_total r0 (z - d) with h | h
      · rw [min_eq_left h, max_eq_right (by linarith)]; ring
      · rw [min_eq_right h, max_eq_left (by linarith)]; ring
    have e2 : max ((z - r0) - (d : ℝ)) 0 = (z - d) - min r0 (z - d) := by
      rcases le_total r0 (z - d) with h | h
      · rw [min_eq_left h, max_eq_left (by linarith)]; ring
      · rw [min_eq_right h, max_eq_right (by linarith)]; ring
    rw [e1, e2, G0_eq]
    have hE : Gadj P (min r0 (z - d)) + P.h2 * (z - d) - ε ≤ E0 P (z - d) := by
      haveI : Nonempty (Set.Iic (z - (d : ℝ))) := ⟨⟨z - d, Set.mem_Iic.mpr le_rfl⟩⟩
      refine le_ciInf (fun v => ?_)
      have h1 := hkey (z - d) (by linarith) v v.2
      rw [G0_eq]
      linarith
    linarith
  have hpo : PInt P.mu2 (fun d : ℕ => P.G0 (r0 - max (-((z - r0) - (d : ℝ))) 0)
      + P.h2 * max ((z - r0) - (d : ℝ)) 0) := by
    refine PInt.of_abs_le hμ2 ((pint_E0 P hμ2 z).add hμ2 (pint_const ε)) (fun d => ?_)
    rw [abs_of_nonneg (add_nonneg (P.G0_nonneg _) (mul_nonneg P.h2_nonneg (le_max_right _ _)))]
    exact hobj d
  calc P.V0 ≤ pexp P.mu2 (fun d : ℕ => P.G0 (r0 - max (-((z - r0) - (d : ℝ))) 0)
        + P.h2 * max ((z - r0) - (d : ℝ)) 0) := ciInf_le (V0_bdd P) (r0, z - r0)
    _ ≤ pexp P.mu2 (fun d : ℕ => E0 P (z - d) + ε) :=
        pexp_mono hμ2 hpo ((pint_E0 P hμ2 z).add hμ2 (pint_const ε)) hobj
    _ = pexp P.mu2 (fun d : ℕ => E0 P (z - d)) + ε := by
        rw [pexp_add hμ2 (pint_E0 P hμ2 z) (pint_const ε), pexp_const]

end LBE

end TwoStageRnQ

open Finset Filter Topology

noncomputable section

namespace TwoStageRnQ

namespace Params

variable (P : Params)

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

lemma allocBound_le {c1 c2 : ℝ} (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) :
    P.allocBound c1 c2 ≤ P.H0 + c1 + c2 + 4 * (P.h1 + P.h2 + P.p) * (P.mu1 + P.mu2) := by
  haveI : Nonempty {q : ℝ × ℝ // q.1 ∈ Set.Icc (0 : ℝ) 1 ∧ q.2 ∈ Set.Icc (0 : ℝ) 1} :=
    ⟨⟨(0, 0), ⟨le_refl 0, zero_le_one⟩, ⟨le_refl 0, zero_le_one⟩⟩⟩
  exact ciSup_le (fun q => P.allocBound_term_le hc1 hc2 q)

end Params

end TwoStageRnQ

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace LBA

open TwoStageRnQ.LB TwoStageRnQ.LBP TwoStageRnQ.LBE

variable {P : Params} {S : DemandSpace P} (π : ShipmentPolicy P S)

lemma IL2_m (t : ℝ) : Measurable (IL2 π t) :=
  (IL2_joint π).comp (measurable_id.prodMk measurable_const)

lemma U2_m (t : ℝ) : Measurable (π.U2 t) := U_m (pr2 π) t

lemma U_fin {U : ℝ → S.Ω → ℤ} (hmono : ∀ ω, Monotone (fun t => U t ω))
    (hrate : Tendsto (fun T : ℝ => ENNReal.ofReal T⁻¹ *
      ∫⁻ ω, ENNReal.ofReal ((U T ω - U 0 ω : ℤ) : ℝ) ∂S.ν) atTop (𝓝 (ENNReal.ofReal P.lam)))
    (T : ℝ) : ∫⁻ ω, ENNReal.ofReal ((U T ω - U 0 ω : ℤ) : ℝ) ∂S.ν ≠ ⊤ := by
  obtain ⟨T1, hT1, hT1'⟩ := ((hrate.eventually (gt_mem_nhds ENNReal.ofReal_lt_top)).and
    (eventually_ge_atTop (max T 1))).exists
  have hpos : ENNReal.ofReal T1⁻¹ ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    have : (1 : ℝ) ≤ T1 := le_trans (le_max_right _ _) hT1'
    positivity
  have h1 : ∫⁻ ω, ENNReal.ofReal ((U T1 ω - U 0 ω : ℤ) : ℝ) ∂S.ν ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top hpos] at hT1
    exact lt_irrefl _ hT1
  refine ne_top_of_le_ne_top h1 (lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal ?_))
  have := hmono ω (le_trans (le_max_left _ _) hT1')
  have h2 : U T ω - U 0 ω ≤ U T1 ω - U 0 ω := by linarith
  exact_mod_cast h2

lemma init2_fin {Z : ℝ → S.Ω → ℝ} (hadm : π.Admissible Z) :
    ∫⁻ ω, ENNReal.ofReal (|(IL2 π 0 ω : ℝ)| + ((π.U2 0 ω - π.U2 (-P.L2) ω : ℤ) : ℝ)) ∂S.ν ≠ ⊤ := by
  refine ne_top_of_le_ne_top hadm.init_moments.ne
    (lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal ?_))
  have h1 : 0 ≤ |(netInv P.L1 π.x1 π.U1 S.N 0 ω : ℝ)| := abs_nonneg _
  have h2 : (0 : ℝ) ≤ ((π.U1 0 ω - π.U1 (-P.L1) ω : ℤ) : ℝ) := by
    have := π.U1_mono ω (by linarith [P.L1_nonneg] : -P.L1 ≤ 0)
    have h3 : (0 : ℤ) ≤ π.U1 0 ω - π.U1 (-P.L1) ω := by linarith
    exact_mod_cast h3
  unfold IL2
  linarith

lemma IL2_fin {Z : ℝ → S.Ω → ℝ} (hadm : π.Admissible Z) {T : ℝ} (hT : 0 ≤ T) :
    DI (fun p => ENNReal.ofReal |(IL2 π p.2 p.1 : ℝ)|) (Set.Ioc 0 T) ≠ ⊤ := by
  have hL2 := P.L2_nonneg
  set D : S.Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (|(IL2 π 0 ω : ℝ)| + ((π.U2 0 ω - π.U2 (-P.L2) ω : ℤ) : ℝ))
      + ENNReal.ofReal ((π.U2 T ω - π.U2 0 ω : ℤ) : ℝ)
      + ENNReal.ofReal ((S.N T ω - S.N 0 ω : ℤ) : ℝ) with hD
  have hpt : ∀ ω t, t ∈ Set.Ioc 0 T → ENNReal.ofReal |(IL2 π t ω : ℝ)| ≤ D ω := by
    intro ω t ht
    have a1 := π.U2_mono ω (by linarith : -P.L2 ≤ 0)
    have a2 := π.U2_mono ω hT
    have a3 := π.U2_mono ω (by linarith [ht.2] : t - P.L2 ≤ T)
    have a4 := π.U2_mono ω (by linarith [ht.1] : -P.L2 ≤ t - P.L2)
    have a5 := S.N_mono ω ht.1.le
    have a6 := S.N_mono ω ht.2
    have a7 := S.N_mono ω hT
    have e : IL2 π t ω - IL2 π 0 ω = (π.U2 (t - P.L2) ω - π.U2 (-P.L2) ω) - (S.N t ω - S.N 0 ω) := by
      unfold IL2 netInv; ring_nf
    have hz : |IL2 π t ω| ≤ (|IL2 π 0 ω| + (π.U2 0 ω - π.U2 (-P.L2) ω)) + (π.U2 T ω - π.U2 0 ω)
        + (S.N T ω - S.N 0 ω) := by
      have := abs_sub_abs_le_abs_sub (IL2 π t ω) (IL2 π 0 ω)
      rw [e] at this
      have h5 : |(π.U2 (t - P.L2) ω - π.U2 (-P.L2) ω) - (S.N t ω - S.N 0 ω)|
          ≤ (π.U2 (t - P.L2) ω - π.U2 (-P.L2) ω) + (S.N t ω - S.N 0 ω) := by
        rw [abs_le]; constructor <;> linarith
      linarith
    have hzr : |(IL2 π t ω : ℝ)| ≤ (|(IL2 π 0 ω : ℝ)| + ((π.U2 0 ω - π.U2 (-P.L2) ω : ℤ) : ℝ))
        + ((π.U2 T ω - π.U2 0 ω : ℤ) : ℝ) + ((S.N T ω - S.N 0 ω : ℤ) : ℝ) := by
      have h := (Int.cast_le (R := ℝ)).mpr hz
      push_cast at h ⊢
      exact h
    have n1 : (0 : ℝ) ≤ |(IL2 π 0 ω : ℝ)| + ((π.U2 0 ω - π.U2 (-P.L2) ω : ℤ) : ℝ) := by
      have : (0 : ℝ) ≤ ((π.U2 0 ω - π.U2 (-P.L2) ω : ℤ) : ℝ) := by exact_mod_cast (by linarith : (0:ℤ) ≤ π.U2 0 ω - π.U2 (-P.L2) ω)
      positivity
    have n2 : (0 : ℝ) ≤ ((π.U2 T ω - π.U2 0 ω : ℤ) : ℝ) := by exact_mod_cast (by linarith : (0:ℤ) ≤ π.U2 T ω - π.U2 0 ω)
    have n3 : (0 : ℝ) ≤ ((S.N T ω - S.N 0 ω : ℤ) : ℝ) := by exact_mod_cast (by linarith : (0:ℤ) ≤ S.N T ω - S.N 0 ω)
    simp only [hD]
    rw [← ENNReal.ofReal_add n1 n2, ← ENNReal.ofReal_add (add_nonneg n1 n2) n3]
    exact ENNReal.ofReal_le_ofReal hzr
  have hle : DI (fun p => ENNReal.ofReal |(IL2 π p.2 p.1 : ℝ)|) (Set.Ioc 0 T)
      ≤ ∫⁻ ω, D ω * ENNReal.ofReal T ∂S.ν := by
    unfold DI
    refine lintegral_mono (fun ω => ?_)
    calc ∫⁻ t in Set.Ioc 0 T, ENNReal.ofReal |(IL2 π t ω : ℝ)|
        ≤ ∫⁻ t in Set.Ioc 0 T, D ω := setLIntegral_mono measurable_const (fun t ht => hpt ω t ht)
      _ = D ω * ENNReal.ofReal T := by rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
  refine ne_top_of_le_ne_top ?_ hle
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  refine ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top
  have m1 : Measurable (fun ω => ENNReal.ofReal (|(IL2 π 0 ω : ℝ)| + ((π.U2 0 ω - π.U2 (-P.L2) ω : ℤ) : ℝ))) := by
    have h := (measurable_of_countable (fun z : ℤ × ℤ × ℤ => ENNReal.ofReal (|(z.1 : ℝ)|
      + ((z.2.1 - z.2.2 : ℤ) : ℝ)))).comp ((IL2_m π 0).prodMk ((U2_m π 0).prodMk (U2_m π (-P.L2))))
    exact h
  have m2 : Measurable (fun ω => ENNReal.ofReal ((π.U2 T ω - π.U2 0 ω : ℤ) : ℝ)) := by
    have h := (measurable_of_countable (fun z : ℤ × ℤ => ENNReal.ofReal ((z.1 - z.2 : ℤ) : ℝ))).comp
      ((U2_m π T).prodMk (U2_m π 0))
    exact h
  have m12 : Measurable (fun ω => ENNReal.ofReal (|(IL2 π 0 ω : ℝ)| + ((π.U2 0 ω - π.U2 (-P.L2) ω : ℤ) : ℝ))
      + ENNReal.ofReal ((π.U2 T ω - π.U2 0 ω : ℤ) : ℝ)) := m1.add m2
  simp only [hD]
  rw [lintegral_add_left m12, lintegral_add_left m1, S.lintegral_incr_val hT]
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨init2_fin π hadm,
    U_fin π.U2_mono hadm.rate_U2 T⟩, ENNReal.ofReal_ne_top⟩

lemma shift_tendsto {f : ℝ → ℝ≥0∞} (hf : Tendsto (fun T => ENNReal.ofReal T⁻¹ * f T) atTop (𝓝 0))
    {c : ℝ} (hc : 0 ≤ c) : Tendsto (fun T => ENNReal.ofReal T⁻¹ * f (T - c)) atTop (𝓝 0) := by
  have hs : Tendsto (fun T : ℝ => T - c) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun b => ⟨b + c, fun a ha => by linarith⟩)
  have h2 := hf.comp hs
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
    (Eventually.of_forall (fun _ => zero_le)) ?_
  filter_upwards [eventually_gt_atTop c] with T hT
  simp only [Function.comp]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  exact inv_anti₀ (by linarith) (by linarith)

lemma const_tendsto {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    Tendsto (fun T : ℝ => ENNReal.ofReal T⁻¹ * c) atTop (𝓝 0) := by
  have h := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal tendsto_inv_atTop_zero) (Or.inr hc)
  rwa [ENNReal.ofReal_zero, zero_mul] at h

def Wb (T : ℝ) : ℝ≥0∞ :=
  DI (fun p => ENNReal.ofReal |(IL2 π p.2 p.1 : ℝ)|) (Set.Ioc 0 P.L1)
    + DI (fun p => ENNReal.ofReal |(IL2 π p.2 p.1 : ℝ)|) (Set.Ioc (T - P.L1) T)

lemma Wb_tendsto {Z : ℝ → S.Ω → ℝ} (hadm : π.Admissible Z) :
    Tendsto (fun T => ENNReal.ofReal T⁻¹ * Wb π T) atTop (𝓝 0) := by
  have hL1 := P.L1_nonneg
  have hL2 := P.L2_nonneg
  unfold Wb
  simp_rw [mul_add]
  rw [show (0 : ℝ≥0∞) = 0 + 0 by simp]
  refine (const_tendsto (IL2_fin π hadm hL1)).add ?_

  set A : ℝ → ℝ≥0∞ := fun T => ∫⁻ ω, ENNReal.ofReal (|(netInv P.L2 π.x2 π.U2 S.N T ω : ℝ)|
    + ((π.U2 T ω - π.U2 (T - P.L2) ω : ℤ) : ℝ)) ∂S.ν with hA
  set Bw : ℝ → ℝ≥0∞ := fun T => ∫⁻ ω, ENNReal.ofReal ((π.U2 (T + (P.L1 + P.L2)) ω - π.U2 T ω : ℤ)
    : ℝ) ∂S.ν with hBw
  have hbound : ∀ T, P.L1 + P.L2 ≤ T →
      DI (fun p => ENNReal.ofReal |(IL2 π p.2 p.1 : ℝ)|) (Set.Ioc (T - P.L1) T)
        ≤ ENNReal.ofReal P.L1 * (A (T - P.L1) + Bw (T - (P.L1 + P.L2)) + ENNReal.ofReal (P.lam * P.L1)) := by
    intro T hT
    set T' := T - P.L1 with hT'
    set Dm : S.Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (|(netInv P.L2 π.x2 π.U2 S.N T' ω : ℝ)|
        + ((π.U2 T' ω - π.U2 (T' - P.L2) ω : ℤ) : ℝ))
      + ENNReal.ofReal ((π.U2 (T - (P.L1 + P.L2) + (P.L1 + P.L2)) ω - π.U2 (T - (P.L1 + P.L2)) ω : ℤ) : ℝ)
      + ENNReal.ofReal ((S.N T ω - S.N T' ω : ℤ) : ℝ) with hDm
    have hpt : ∀ ω s, s ∈ Set.Ioc T' T → ENNReal.ofReal |(IL2 π s ω : ℝ)| ≤ Dm ω := by
      intro ω s hs
      have e3 : T - (P.L1 + P.L2) = T' - P.L2 := by rw [hT']; ring
      have e4 : T - (P.L1 + P.L2) + (P.L1 + P.L2) = T := by ring
      have b1 := π.U2_mono ω (by linarith [hs.1] : T' - P.L2 ≤ s - P.L2)
      have b2 := π.U2_mono ω (by linarith [hs.2] : s - P.L2 ≤ T)
      have b3 := π.U2_mono ω (by linarith : T' - P.L2 ≤ T')
      have b4 := S.N_mono ω hs.1.le
      have b5 := S.N_mono ω hs.2
      have e : IL2 π s ω - IL2 π T' ω = (π.U2 (s - P.L2) ω - π.U2 (T' - P.L2) ω) - (S.N s ω - S.N T' ω) := by
        unfold IL2 netInv; ring_nf
      have hz : |IL2 π s ω| ≤ (|IL2 π T' ω| + (π.U2 T' ω - π.U2 (T' - P.L2) ω))
          + (π.U2 T ω - π.U2 (T' - P.L2) ω) + (S.N T ω - S.N T' ω) := by
        have := abs_sub_abs_le_abs_sub (IL2 π s ω) (IL2 π T' ω)
        rw [e] at this
        have h5 : |(π.U2 (s - P.L2) ω - π.U2 (T' - P.L2) ω) - (S.N s ω - S.N T' ω)|
            ≤ (π.U2 (s - P.L2) ω - π.U2 (T' - P.L2) ω) + (S.N s ω - S.N T' ω) := by
          rw [abs_le]; constructor <;> linarith
        linarith
      have n1 : (0 : ℝ) ≤ |(netInv P.L2 π.x2 π.U2 S.N T' ω : ℝ)| + ((π.U2 T' ω - π.U2 (T' - P.L2) ω : ℤ) : ℝ) := by
        have : (0 : ℝ) ≤ ((π.U2 T' ω - π.U2 (T' - P.L2) ω : ℤ) : ℝ) := by
          exact_mod_cast (by linarith : (0:ℤ) ≤ π.U2 T' ω - π.U2 (T' - P.L2) ω)
        positivity
      have n2 : (0 : ℝ) ≤ ((π.U2 T ω - π.U2 (T' - P.L2) ω : ℤ) : ℝ) := by
        exact_mod_cast (by linarith : (0:ℤ) ≤ π.U2 T ω - π.U2 (T' - P.L2) ω)
      have n3 : (0 : ℝ) ≤ ((S.N T ω - S.N T' ω : ℤ) : ℝ) := by
        exact_mod_cast (by linarith : (0:ℤ) ≤ S.N T ω - S.N T' ω)
      simp only [hDm]
      rw [e4, e3, ← ENNReal.ofReal_add n1 n2, ← ENNReal.ofReal_add (add_nonneg n1 n2) n3]
      apply ENNReal.ofReal_le_ofReal
      have h := (Int.cast_le (R := ℝ)).mpr hz
      rw [show netInv P.L2 π.x2 π.U2 S.N T' ω = IL2 π T' ω from rfl]
      push_cast at h ⊢
      linarith
    have hle : DI (fun p => ENNReal.ofReal |(IL2 π p.2 p.1 : ℝ)|) (Set.Ioc T' T)
        ≤ ∫⁻ ω, Dm ω * ENNReal.ofReal P.L1 ∂S.ν := by
      unfold DI
      refine lintegral_mono (fun ω => ?_)
      calc ∫⁻ t in Set.Ioc T' T, ENNReal.ofReal |(IL2 π t ω : ℝ)|
          ≤ ∫⁻ t in Set.Ioc T' T, Dm ω := setLIntegral_mono measurable_const (fun t ht => hpt ω t ht)
        _ = Dm ω * ENNReal.ofReal P.L1 := by
            rw [setLIntegral_const, Real.volume_Ioc, hT']; congr 2; ring
    refine le_trans hle ?_
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]
    refine mul_le_mul' le_rfl ?_
    have m1 : Measurable (fun ω => ENNReal.ofReal (|(netInv P.L2 π.x2 π.U2 S.N T' ω : ℝ)|
        + ((π.U2 T' ω - π.U2 (T' - P.L2) ω : ℤ) : ℝ))) := by
      have h := (measurable_of_countable (fun z : ℤ × ℤ × ℤ => ENNReal.ofReal (|(z.1 : ℝ)|
        + ((z.2.1 - z.2.2 : ℤ) : ℝ)))).comp ((IL2_m π T').prodMk ((U2_m π T').prodMk (U2_m π (T' - P.L2))))
      exact h
    have m2 : Measurable (fun ω => ENNReal.ofReal ((π.U2 (T - (P.L1 + P.L2) + (P.L1 + P.L2)) ω
        - π.U2 (T - (P.L1 + P.L2)) ω : ℤ) : ℝ)) := by
      have h := (measurable_of_countable (fun z : ℤ × ℤ => ENNReal.ofReal ((z.1 - z.2 : ℤ) : ℝ))).comp
        ((U2_m π (T - (P.L1 + P.L2) + (P.L1 + P.L2))).prodMk (U2_m π (T - (P.L1 + P.L2))))
      exact h
    have m12 : Measurable (fun ω => ENNReal.ofReal (|(netInv P.L2 π.x2 π.U2 S.N T' ω : ℝ)|
        + ((π.U2 T' ω - π.U2 (T' - P.L2) ω : ℤ) : ℝ)) + ENNReal.ofReal ((π.U2 (T - (P.L1 + P.L2)
        + (P.L1 + P.L2)) ω - π.U2 (T - (P.L1 + P.L2)) ω : ℤ) : ℝ)) := m1.add m2
    simp only [hDm]
    rw [lintegral_add_left m12, lintegral_add_left m1,
      S.lintegral_incr_val (by linarith : T' ≤ T), show T - T' = P.L1 by rw [hT']; ring]
  have hT1 := shift_tendsto hadm.terminal_2 hL1
  have hT2 := shift_tendsto hadm.window_U2 (add_nonneg hL1 hL2)
  have hT3 := const_tendsto (c := ENNReal.ofReal (P.lam * P.L1)) ENNReal.ofReal_ne_top
  have hsum := ENNReal.Tendsto.const_mul ((hT1.add hT2).add hT3) (Or.inr (ENNReal.ofReal_ne_top (r := P.L1)))
  simp only [add_zero, mul_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall (fun _ => zero_le)) ?_
  filter_upwards [eventually_ge_atTop (P.L1 + P.L2)] with T hT
  calc ENNReal.ofReal T⁻¹ * DI (fun p => ENNReal.ofReal |(IL2 π p.2 p.1 : ℝ)|) (Set.Ioc (T - P.L1) T)
      ≤ ENNReal.ofReal T⁻¹ * (ENNReal.ofReal P.L1 * (A (T - P.L1) + Bw (T - (P.L1 + P.L2))
          + ENNReal.ofReal (P.lam * P.L1))) := mul_le_mul' le_rfl (hbound T hT)
    _ = ENNReal.ofReal P.L1 * (ENNReal.ofReal T⁻¹ * A (T - P.L1) + ENNReal.ofReal T⁻¹ * Bw (T - (P.L1 + P.L2))
          + ENNReal.ofReal T⁻¹ * ENNReal.ofReal (P.lam * P.L1)) := by ring

end LBA

end TwoStageRnQ

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace LBA

open TwoStageRnQ.LB TwoStageRnQ.LBP TwoStageRnQ.LBE

variable {P : Params} {S : DemandSpace P} (π : ShipmentPolicy P S)

lemma jumpCount_mono {f : ℝ → ℤ} (hf : Monotone f) {T1 T : ℝ} (h : T1 ≤ T) :
    jumpCount f T1 ≤ jumpCount f T := by
  unfold jumpCount
  apply Set.ncard_le_ncard
  · intro t ht
    exact ⟨⟨ht.1.1, le_trans ht.1.2 h⟩, ht.2⟩
  · refine (jumps_finite hf T).subset (fun t ht => ⟨ht.1, (jump_iff hf t).mp ht.2⟩)

lemma cyc_shift_ge {F : ℝ → ℝ} (hF : ∀ x, 0 ≤ F x) {c k : ℝ} (hk : 0 ≤ k) :
    c + cycCost F k ≤ cycCost (fun x => c + F x) k := by
  refine le_ciInf (fun j => ?_)
  have h1 : cycCost F k ≤ k / ((j : ℕ) : ℝ) + latInf (j : ℕ) F :=
    ciInf_le (Params.cycCost_bddBelow hF hk) j
  have hj : ((j : ℕ) : ℝ) ≠ 0 := by positivity
  have h2 : c + latInf (j : ℕ) F ≤ latInf (j : ℕ) (fun x => c + F x) := by
    refine le_ciInf (fun x => ?_)
    have h3 : latInf (j : ℕ) F ≤ latAvg (j : ℕ) F x := ciInf_le (Params.latInf_bddBelow hF) x
    have h4 : latAvg (j : ℕ) (fun x => c + F x) x = c + latAvg (j : ℕ) F x := by
      unfold latAvg
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    linarith
  linarith

lemma F1_id {η ζ : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (hζ : ζ ∈ Set.Icc (0 : ℝ) 1) (x : ℝ) :
    η * P.H0 + P.allocF1 η ζ x
      = pexp P.mu1 (fun d : ℕ => phi P.h1 (ζ * P.p + η * P.h2) (x - d)) + η * P.h2 * x := by
  have hμ := P.mu1_nonneg
  have hb : 0 ≤ ζ * P.p + η * P.h2 :=
    add_nonneg (mul_nonneg hζ.1 P.p_nonneg) (mul_nonneg hη.1 P.h2_nonneg)
  unfold Params.allocF1
  have e : ∀ d : ℕ, phi (P.h1 + η * P.h2) (ζ * P.p) (x - d)
      = phi P.h1 (ζ * P.p + η * P.h2) (x - d) + η * P.h2 * (x - d) := by
    intro d
    unfold phi
    have := max_sub_max (x - d)
    linear_combination η * P.h2 * this
  simp_rw [e]
  rw [pexp_add hμ ((phi_linGrowth P.h1_nonneg hb x).pint hμ)
      (((pint_const x).sub hμ pint_nat).const_mul (η * P.h2)),
    pexp_const_mul, pexp_sub hμ (pint_const x) pint_nat, pexp_const, pexp_nat]
  unfold Params.H0 Params.mu1
  ring

lemma allocF1_nn {η ζ : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (hζ : ζ ∈ Set.Icc (0 : ℝ) 1) (x : ℝ) :
    0 ≤ η * P.H0 + P.allocF1 η ζ x :=
  add_nonneg (mul_nonneg hη.1 P.H0_nonneg) (P.allocF1_nonneg hη hζ x)

theorem zero_chain {Z : ℝ → S.Ω → ℝ} (hadm : π.Admissible Z) {T : ℝ}
    (hT : 2 * (P.L1 + P.L2) ≤ T) :
    ENNReal.ofReal P.V0 * ENNReal.ofReal (T - (P.L1 + P.L2))
      ≤ DI (fun p => ENNReal.ofReal (π.cI p.2 p.1)) (Set.Ioc 0 T) + ENNReal.ofReal P.h2 * Wb π T := by
  have hL1 := P.L1_nonneg
  have hL2 := P.L2_nonneg
  have h1mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hΨm : Measurable (fun p : S.Ω × ℝ => ENNReal.ofReal (E0 P (IL2 π p.2 p.1))) :=
    zmeas (fun z : ℤ => ENNReal.ofReal (E0 P z)) (IL2_joint π)
  have hc := comp1 π h1mem h1mem (fun p => E0 P (IL2 π p.2 p.1)) hΨm (fun p => E0_nonneg P _)
    (fun ω t ht => by
      have hm := mat π ht ω
      have hmr : ((IP1 π t ω : ℤ) : ℝ) ≤ ((IL2 π t ω : ℤ) : ℝ) := by exact_mod_cast hm
      have h1 := E0_le P hmr
      rw [G0_eq] at h1
      unfold Gadj at h1
      have e := max_sub_max (IL2 π t ω : ℝ)
      have e2 : P.h2 * max (IL2 π t ω : ℝ) 0 - P.h2 * max (-(IL2 π t ω : ℝ)) 0
          = P.h2 * (IL2 π t ω : ℝ) := by rw [← mul_sub, e]
      simp only [one_mul] at h1 ⊢
      linarith) (T := T) (by linarith) (IL2_fin π hadm (T := T) (by linarith))
  have hc1 : DI (fun p => ENNReal.ofReal (c1 π 1 1 p.2 p.1)) (Set.Ioc 0 T)
      = DI (fun p => ENNReal.ofReal (π.cI p.2 p.1)) (Set.Ioc 0 T) :=
    DI_congr measurableSet_Ioc (fun ω t _ => by
      show ENNReal.ofReal (c1 π 1 1 t ω) = ENNReal.ofReal (π.cI t ω)
      rw [cI_eq]; unfold c1; congr 1; ring)
  rw [hc1, one_mul] at hc
  have hlow : ENNReal.ofReal P.V0 * ENNReal.ofReal (T - (P.L1 + P.L2))
      ≤ DI (fun p => ENNReal.ofReal (E0 P (IL2 π p.2 p.1))) (Set.Ioc 0 (T - P.L1)) := by
    rw [DI_swap hΨm]
    calc ENNReal.ofReal P.V0 * ENNReal.ofReal (T - (P.L1 + P.L2))
        = ∫⁻ t in Set.Ioc 0 (T - (P.L1 + P.L2)), ENNReal.ofReal P.V0 := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
      _ ≤ ∫⁻ t in Set.Ioc 0 (T - (P.L1 + P.L2)),
            ∫⁻ ω, ENNReal.ofReal (E0 P (IL2 π (t + P.L2) ω)) ∂S.ν := by
          refine setLIntegral_mono' measurableSet_Ioc (fun t ht => ?_)
          have hcond := cond_f (v := t) (w := t + P.L2) ht.1.le (by linarith) (IP2_adapted π ht.1.le)
            (E0 P) (E0_nonneg P) (fun a => pint_E0 P (mul_nonneg P.lam_nonneg (by linarith)) a)
          rw [show P.lam * (t + P.L2 - t) = P.mu2 by unfold Params.mu2; ring] at hcond
          have e : ∀ ω, ENNReal.ofReal (E0 P (IL2 π (t + P.L2) ω))
              = ENNReal.ofReal (E0 P (((IP2 π t ω - (S.N (t + P.L2) ω - S.N t ω)) : ℤ) : ℝ)) := by
            intro ω; rw [IL2_shift]
          rw [lintegral_congr e, hcond]
          calc ENNReal.ofReal P.V0 = ∫⁻ _ω, ENNReal.ofReal P.V0 ∂S.ν := by
                rw [lintegral_const, measure_univ, mul_one]
            _ ≤ _ := lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal (envelope P _))
      _ = ∫⁻ s in Set.Ioc P.L2 (T - P.L1), ∫⁻ ω, ENNReal.ofReal (E0 P (IL2 π s ω)) ∂S.ν := by
          rw [lintegral_Ioc_shift (fun s => ∫⁻ ω, ENNReal.ofReal (E0 P (IL2 π s ω)) ∂S.ν) 0
            (T - (P.L1 + P.L2)) P.L2, zero_add, show T - (P.L1 + P.L2) + P.L2 = T - P.L1 by ring]
      _ ≤ ∫⁻ s in Set.Ioc 0 (T - P.L1), ∫⁻ ω, ENNReal.ofReal (E0 P (IL2 π s ω)) ∂S.ν :=
          lintegral_mono_set (Set.Ioc_subset_Ioc hL2 le_rfl)
  exact le_trans hlow hc

theorem chain1 {Z : ℝ → S.Ω → ℝ} (hadm : π.Admissible Z) (hlam : 0 < P.lam) {u : ℝ}
    (hu : u ∈ Set.Ioc (0 : ℝ) 1) {η ζ : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1)
    (hζ : ζ ∈ Set.Icc (0 : ℝ) 1) {T : ℝ} (hT : 2 * (P.L1 + P.L2) + 1 ≤ T) :
    ENNReal.ofReal ((η * P.H0 + cycCost (P.allocF1 η ζ) (P.k1 / u)) * (T - P.L1))
      ≤ DI (fun p => ENNReal.ofReal (c1 π η ζ p.2 p.1)) (Set.Ioc 0 T)
        + ENNReal.ofReal (η * P.h2) * Wb π T
        + ENNReal.ofReal (P.K1 / u) * ∫⁻ ω, ((jumpCount (fun t => π.U1 t ω) T : ℕ) : ℝ≥0∞) ∂S.ν
        + ENNReal.ofReal (cycCost (fun x => η * P.H0 + P.allocF1 η ζ x) (P.lam * (P.K1 / u)) / P.lam)
          * ∫⁻ ω, ((unfinishedCount (π.x1 ω) (fun t => π.U1 t ω) (fun t => S.N t ω)
              (T - P.L1) : ℕ) : ℝ≥0∞) ∂S.ν := by
  have hL1 := P.L1_nonneg
  have hL2 := P.L2_nonneg
  have hk : 0 ≤ P.lam * (P.K1 / u) := mul_nonneg P.lam_nonneg (div_nonneg P.K1_nonneg hu.1.le)
  set F : ℝ → ℝ := fun x => η * P.H0 + P.allocF1 η ζ x with hFdef
  have hF : ∀ x, 0 ≤ F x := allocF1_nn hη hζ
  set C := cycCost F (P.lam * (P.K1 / u)) with hC
  have hC0 : 0 ≤ C := cycCost_nonneg hF hk
  have hT1 : 0 < T - P.L1 := by linarith
  have cl := cycle_lemma (pr1 π) F hF hk hT1
  have hΨm : Measurable (fun p : S.Ω × ℝ => ENNReal.ofReal (F (IP1 π p.2 p.1))) :=
    zmeas (fun z : ℤ => ENNReal.ofReal (F z)) (IP1_joint π)
  have hc := comp1 π hη hζ (fun p => F (IP1 π p.2 p.1)) hΨm (fun p => hF _)
    (fun ω t ht => by
      have hm := mat π ht ω
      have hmr : ((IP1 π t ω : ℤ) : ℝ) ≤ ((IL2 π t ω : ℤ) : ℝ) := by exact_mod_cast hm
      have hid := F1_id (P := P) hη hζ ((IP1 π t ω : ℤ) : ℝ)
      have e := max_sub_max (IL2 π t ω : ℝ)
      have hc' : 0 ≤ η * P.h2 := mul_nonneg hη.1 P.h2_nonneg
      have e2 : η * P.h2 * max (IL2 π t ω : ℝ) 0 - η * P.h2 * max (-(IL2 π t ω : ℝ)) 0
          = η * P.h2 * (IL2 π t ω : ℝ) := by rw [← mul_sub, e]
      have e3 := mul_le_mul_of_nonneg_left hmr hc'
      simp only [hFdef]
      linarith) (T := T) (by linarith) (IL2_fin π hadm (T := T) (by linarith))
  have hJ : ∫⁻ ω, ((jumpCount (fun t => π.U1 t ω) (T - P.L1) : ℕ) : ℝ≥0∞) ∂S.ν
      ≤ ∫⁻ ω, ((jumpCount (fun t => π.U1 t ω) T : ℕ) : ℝ≥0∞) ∂S.ν :=
    lintegral_mono (fun ω => Nat.cast_le.mpr (jumpCount_mono (T1 := T - P.L1) (T := T) (π.U1_mono ω) (by linarith)))
  have key : ENNReal.ofReal P.lam * ENNReal.ofReal (C * (T - P.L1))
      ≤ ENNReal.ofReal P.lam * (DI (fun p => ENNReal.ofReal (c1 π η ζ p.2 p.1)) (Set.Ioc 0 T)
        + ENNReal.ofReal (η * P.h2) * Wb π T
        + ENNReal.ofReal (P.K1 / u) * ∫⁻ ω, ((jumpCount (fun t => π.U1 t ω) T : ℕ) : ℝ≥0∞) ∂S.ν
        + ENNReal.ofReal (C / P.lam)
          * ∫⁻ ω, ((unfinishedCount (π.x1 ω) (fun t => π.U1 t ω) (fun t => S.N t ω)
              (T - P.L1) : ℕ) : ℝ≥0∞) ∂S.ν) := by
    have e1 : ENNReal.ofReal P.lam * ENNReal.ofReal (C * (T - P.L1))
        = ENNReal.ofReal C * ENNReal.ofReal (P.lam * (T - P.L1)) := by
      rw [← ENNReal.ofReal_mul P.lam_nonneg, ← ENNReal.ofReal_mul hC0]; congr 1; ring
    have e2 : ENNReal.ofReal P.lam * ENNReal.ofReal (P.K1 / u) = ENNReal.ofReal (P.lam * (P.K1 / u)) :=
      (ENNReal.ofReal_mul P.lam_nonneg).symm
    have e3 : ENNReal.ofReal P.lam * ENNReal.ofReal (C / P.lam) = ENNReal.ofReal C := by
      rw [← ENNReal.ofReal_mul P.lam_nonneg]; congr 1; field_simp
    rw [e1, mul_add, mul_add, mul_add, ← mul_assoc (ENNReal.ofReal P.lam) (ENNReal.ofReal (P.K1 / u)), e2,
      ← mul_assoc (ENNReal.ofReal P.lam) (ENNReal.ofReal (C / P.lam)), e3]
    calc ENNReal.ofReal C * ENNReal.ofReal (P.lam * (T - P.L1))
        ≤ ENNReal.ofReal P.lam * DI (fun p => ENNReal.ofReal (F (IP1 π p.2 p.1))) (Set.Ioc 0 (T - P.L1))
          + ENNReal.ofReal (P.lam * (P.K1 / u))
            * ∫⁻ ω, ((jumpCount (fun t => π.U1 t ω) (T - P.L1) : ℕ) : ℝ≥0∞) ∂S.ν
          + ENNReal.ofReal C * ∫⁻ ω, ((unfinishedCount (π.x1 ω) (fun t => π.U1 t ω)
              (fun t => S.N t ω) (T - P.L1) : ℕ) : ℝ≥0∞) ∂S.ν := cl
      _ ≤ ENNReal.ofReal P.lam * (DI (fun p => ENNReal.ofReal (c1 π η ζ p.2 p.1)) (Set.Ioc 0 T)
            + ENNReal.ofReal (η * P.h2) * Wb π T)
          + ENNReal.ofReal (P.lam * (P.K1 / u))
            * ∫⁻ ω, ((jumpCount (fun t => π.U1 t ω) T : ℕ) : ℝ≥0∞) ∂S.ν
          + ENNReal.ofReal C * ∫⁻ ω, ((unfinishedCount (π.x1 ω) (fun t => π.U1 t ω)
              (fun t => S.N t ω) (T - P.L1) : ℕ) : ℝ≥0∞) ∂S.ν := by
          gcongr
          exact hc
      _ = _ := by ring
  have hlam0 : ENNReal.ofReal P.lam ≠ 0 := by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hlam
  have h2 := (ENNReal.mul_le_mul_iff_right hlam0 ENNReal.ofReal_ne_top).mp key
  have hcyc := cyc_shift_ge (P.allocF1_nonneg hη hζ) (c := η * P.H0) hk
  have hk1 : P.k1 / u = P.lam * (P.K1 / u) := by unfold Params.k1; ring
  rw [hk1]
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) h2
  exact mul_le_mul_of_nonneg_right hcyc hT1.le

theorem chain2 {Z : ℝ → S.Ω → ℝ} (hadm : π.Admissible Z) (hlam : 0 < P.lam) {u : ℝ}
    (hu : u ∈ Set.Ioc (0 : ℝ) 1) {η ζ : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1)
    (hζ : ζ ∈ Set.Icc (0 : ℝ) 1) {T : ℝ} (hT : 2 * (P.L1 + P.L2) + 1 ≤ T) :
    ENNReal.ofReal (cycCost (P.allocF2 η ζ) (P.k2 / u) * (T - (P.L1 + P.L2)))
      ≤ DI (fun p => ENNReal.ofReal (c2 π η ζ p.2 p.1)) (Set.Ioc 0 T)
        + ENNReal.ofReal (P.K2 / u) * ∫⁻ ω, ((jumpCount (fun t => π.U2 t ω) T : ℕ) : ℝ≥0∞) ∂S.ν
        + ENNReal.ofReal (cycCost (P.allocF2 η ζ) (P.lam * (P.K2 / u)) / P.lam)
          * ∫⁻ ω, ((unfinishedCount (π.x2 ω) (fun t => π.U2 t ω) (fun t => S.N t ω)
              (T - (P.L1 + P.L2)) : ℕ) : ℝ≥0∞) ∂S.ν := by
  have hL1 := P.L1_nonneg
  have hL2 := P.L2_nonneg
  have hk : 0 ≤ P.lam * (P.K2 / u) := mul_nonneg P.lam_nonneg (div_nonneg P.K2_nonneg hu.1.le)
  have hF : ∀ x, 0 ≤ P.allocF2 η ζ x := P.allocF2_nonneg hη hζ
  set C := cycCost (P.allocF2 η ζ) (P.lam * (P.K2 / u)) with hC
  have hC0 : 0 ≤ C := cycCost_nonneg hF hk
  have hT1 : 0 < T - (P.L1 + P.L2) := by linarith
  have cl := cycle_lemma (pr2 π) (P.allocF2 η ζ) hF hk hT1
  have hc := comp2 π hη hζ (T := T) (by linarith)
  have hJ : ∫⁻ ω, ((jumpCount (fun t => π.U2 t ω) (T - (P.L1 + P.L2)) : ℕ) : ℝ≥0∞) ∂S.ν
      ≤ ∫⁻ ω, ((jumpCount (fun t => π.U2 t ω) T : ℕ) : ℝ≥0∞) ∂S.ν :=
    lintegral_mono (fun ω => Nat.cast_le.mpr (jumpCount_mono (T1 := T - (P.L1 + P.L2)) (T := T) (π.U2_mono ω) (by linarith)))
  have key : ENNReal.ofReal P.lam * ENNReal.ofReal (C * (T - (P.L1 + P.L2)))
      ≤ ENNReal.ofReal P.lam * (DI (fun p => ENNReal.ofReal (c2 π η ζ p.2 p.1)) (Set.Ioc 0 T)
        + ENNReal.ofReal (P.K2 / u) * ∫⁻ ω, ((jumpCount (fun t => π.U2 t ω) T : ℕ) : ℝ≥0∞) ∂S.ν
        + ENNReal.ofReal (C / P.lam)
          * ∫⁻ ω, ((unfinishedCount (π.x2 ω) (fun t => π.U2 t ω) (fun t => S.N t ω)
              (T - (P.L1 + P.L2)) : ℕ) : ℝ≥0∞) ∂S.ν) := by
    have e1 : ENNReal.ofReal P.lam * ENNReal.ofReal (C * (T - (P.L1 + P.L2)))
        = ENNReal.ofReal C * ENNReal.ofReal (P.lam * (T - (P.L1 + P.L2))) := by
      rw [← ENNReal.ofReal_mul P.lam_nonneg, ← ENNReal.ofReal_mul hC0]; congr 1; ring
    have e2 : ENNReal.ofReal P.lam * ENNReal.ofReal (P.K2 / u) = ENNReal.ofReal (P.lam * (P.K2 / u)) :=
      (ENNReal.ofReal_mul P.lam_nonneg).symm
    have e3 : ENNReal.ofReal P.lam * ENNReal.ofReal (C / P.lam) = ENNReal.ofReal C := by
      rw [← ENNReal.ofReal_mul P.lam_nonneg]; congr 1; field_simp
    rw [e1, mul_add, mul_add, ← mul_assoc (ENNReal.ofReal P.lam) (ENNReal.ofReal (P.K2 / u)), e2,
      ← mul_assoc (ENNReal.ofReal P.lam) (ENNReal.ofReal (C / P.lam)), e3]
    calc ENNReal.ofReal C * ENNReal.ofReal (P.lam * (T - (P.L1 + P.L2)))
        ≤ ENNReal.ofReal P.lam * DI (fun p => ENNReal.ofReal (P.allocF2 η ζ (IP2 π p.2 p.1)))
            (Set.Ioc 0 (T - (P.L1 + P.L2)))
          + ENNReal.ofReal (P.lam * (P.K2 / u))
            * ∫⁻ ω, ((jumpCount (fun t => π.U2 t ω) (T - (P.L1 + P.L2)) : ℕ) : ℝ≥0∞) ∂S.ν
          + ENNReal.ofReal C * ∫⁻ ω, ((unfinishedCount (π.x2 ω) (fun t => π.U2 t ω)
              (fun t => S.N t ω) (T - (P.L1 + P.L2)) : ℕ) : ℝ≥0∞) ∂S.ν := cl
      _ ≤ ENNReal.ofReal P.lam * DI (fun p => ENNReal.ofReal (c2 π η ζ p.2 p.1)) (Set.Ioc 0 T)
          + ENNReal.ofReal (P.lam * (P.K2 / u))
            * ∫⁻ ω, ((jumpCount (fun t => π.U2 t ω) T : ℕ) : ℝ≥0∞) ∂S.ν
          + ENNReal.ofReal C * ∫⁻ ω, ((unfinishedCount (π.x2 ω) (fun t => π.U2 t ω)
              (fun t => S.N t ω) (T - (P.L1 + P.L2)) : ℕ) : ℝ≥0∞) ∂S.ν := by
          gcongr
      _ = _ := by ring
  have hlam0 : ENNReal.ofReal P.lam ≠ 0 := by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hlam
  have h2 := (ENNReal.mul_le_mul_iff_right hlam0 ENNReal.ofReal_ne_top).mp key
  have hk2 : P.k2 / u = P.lam * (P.K2 / u) := by unfold Params.k2; ring
  rw [hk2]
  exact h2

end LBA

end TwoStageRnQ

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

noncomputable section

namespace TwoStageRnQ

namespace LBA

open TwoStageRnQ.LB TwoStageRnQ.LBP TwoStageRnQ.LBE

lemma limsup_add_const_le (g : ℝ → ℝ≥0∞) (c : ℝ≥0∞) :
    limsup (fun T => g T + c) atTop ≤ limsup g atTop + c := by
  rw [limsup_eq (u := g), ENNReal.sInf_add]
  exact le_iInf₂ (fun b hb => limsup_le_of_le (by isBoundedDefault)
    (Eventually.mono hb (fun T hT => add_le_add hT le_rfl)))

lemma le_limsup_of_le_add {f g h : ℝ → ℝ≥0∞} {a : ℝ≥0∞} (hf : Tendsto f atTop (𝓝 a))
    (hh : Tendsto h atTop (𝓝 0)) (hfg : ∀ᶠ T in atTop, f T ≤ g T + h T) :
    a ≤ limsup g atTop := by
  refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
  have hε' : (0 : ℝ≥0∞) < ε := by exact_mod_cast hε
  have h1 : ∀ᶠ T in atTop, h T < ε := (tendsto_order.1 hh).2 _ hε'
  have h2 : ∀ᶠ T in atTop, f T ≤ g T + ε := by
    filter_upwards [hfg, h1] with T hT hT'
    exact le_trans hT (add_le_add le_rfl hT'.le)
  calc a = limsup f atTop := hf.limsup_eq.symm
    _ ≤ limsup (fun T => g T + (ε : ℝ≥0∞)) atTop := limsup_le_limsup h2
    _ ≤ limsup g atTop + ε := limsup_add_const_le g ε

lemma pexp_zero_mu (f : ℕ → ℝ) : pexp 0 f = f 0 := by
  unfold pexp
  rw [tsum_eq_single 0 (fun n hn => by unfold poisW; rw [zero_pow hn]; simp)]
  unfold poisW; simp

lemma V0_nonpos {P : Params} (hlam : P.lam = 0) : P.V0 ≤ 0 := by
  have h : P.V0 ≤ _ := ciInf_le (V0_bdd P) ((0 : ℝ), (0 : ℝ))
  have hm2 : P.mu2 = 0 := by unfold Params.mu2; rw [hlam, zero_mul]
  have hm1 : P.mu1 = 0 := by unfold Params.mu1; rw [hlam, zero_mul]
  have hH : P.H0 = 0 := by unfold Params.H0; rw [hlam]; ring
  refine le_trans h (le_of_eq ?_)
  simp only [hm2, pexp_zero_mu]
  unfold Params.G0 Params.lossDown
  rw [hm1, pexp_zero_mu, hH]
  simp [phi]

lemma LBsp_nonpos {P : Params} (hlam : P.lam = 0) : P.LBsp ≤ 0 := by
  have : Nonempty (Set.Ioc (0 : ℝ) 1) := ⟨⟨1, zero_lt_one, le_rfl⟩⟩
  refine ciSup_le (fun u => ?_)
  have hu0 : 0 < (u : ℝ) := u.2.1
  have hu1 : (u : ℝ) ≤ 1 := u.2.2
  have hk1 : P.k1 = 0 := by unfold Params.k1; rw [hlam, zero_mul]
  have hk2 : P.k2 = 0 := by unfold Params.k2; rw [hlam, zero_mul]
  have hH : P.H0 = 0 := by unfold Params.H0; rw [hlam]; ring
  have hm1 : P.mu1 = 0 := by unfold Params.mu1; rw [hlam, zero_mul]
  have hm2 : P.mu2 = 0 := by unfold Params.mu2; rw [hlam, zero_mul]
  have hA : P.allocBound (P.k1 / u) (P.k2 / u) ≤ 0 := by
    have h := P.allocBound_le (c1 := P.k1 / u) (c2 := P.k2 / u) (by rw [hk1, zero_div])
      (by rw [hk2, zero_div])
    rw [hk1, hk2, hH, hm1, hm2, zero_div] at h
    rw [hk1, hk2, zero_div]
    simpa using h
  have hV := V0_nonpos hlam
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 1 - (u : ℝ)) hV,
    mul_nonpos_of_nonneg_of_nonpos hu0.le hA]

lemma comb {α β c0 c1 m1 m2 e1 e2 K1 K2 L0 L1 L2 D D1 D2 W J1 J2 E1 E2 Sz E : ℝ≥0∞}
    (hαβ : α + β = 1) (h0 : L0 ≤ D + c0 * W) (h1 : L1 ≤ D1 + c1 * W + m1 * J1 + e1 * E1)
    (h2 : L2 ≤ D2 + m2 * J2 + e2 * E2) (hs : D1 + D2 = D) (hm1 : β * m1 = K1) (hm2 : β * m2 = K2)
    (hS : K1 * J1 + K2 * J2 ≤ Sz) (hE : D + Sz ≤ E) :
    α * L0 + β * L1 + β * L2 ≤ E + ((α * c0 + β * c1) * W + β * e1 * E1 + β * e2 * E2) := by
  calc α * L0 + β * L1 + β * L2
      ≤ α * (D + c0 * W) + β * (D1 + c1 * W + m1 * J1 + e1 * E1)
          + β * (D2 + m2 * J2 + e2 * E2) := by gcongr
    _ = (α + β) * D + ((β * m1) * J1 + (β * m2) * J2)
          + ((α * c0 + β * c1) * W + β * e1 * E1 + β * e2 * E2) := by rw [← hs]; ring
    _ = D + (K1 * J1 + K2 * J2) + ((α * c0 + β * c1) * W + β * e1 * E1 + β * e2 * E2) := by
        rw [hαβ, one_mul, hm1, hm2]
    _ ≤ E + ((α * c0 + β * c1) * W + β * e1 * E1 + β * e2 * E2) :=
        add_le_add (le_trans (add_le_add le_rfl hS) hE) le_rfl

variable {P : Params} {S : DemandSpace P} (π : ShipmentPolicy P S)

theorem fin_bound (hlam : 0 < P.lam) (hadm : π.Admissible π.shipSetup) {u : ℝ}
    (hu : u ∈ Set.Ioc (0 : ℝ) 1) {η ζ : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1)
    (hζ : ζ ∈ Set.Icc (0 : ℝ) 1) {T : ℝ} (hT : 2 * (P.L1 + P.L2) + 1 ≤ T) :
    ENNReal.ofReal (1 - u) * (ENNReal.ofReal P.V0 * ENNReal.ofReal (T - (P.L1 + P.L2)))
      + ENNReal.ofReal u * ENNReal.ofReal ((η * P.H0 + cycCost (P.allocF1 η ζ) (P.k1 / u)) * (T - P.L1))
      + ENNReal.ofReal u * ENNReal.ofReal (cycCost (P.allocF2 η ζ) (P.k2 / u) * (T - (P.L1 + P.L2)))
    ≤ (∫⁻ ω, ((∫⁻ t in Set.Ioc 0 T, ENNReal.ofReal (π.cI t ω))
          + ENNReal.ofReal (π.shipSetup T ω)) ∂S.ν)
      + ((ENNReal.ofReal (1 - u) * ENNReal.ofReal P.h2 + ENNReal.ofReal u * ENNReal.ofReal (η * P.h2))
          * Wb π T
        + ENNReal.ofReal u
          * ENNReal.ofReal (cycCost (fun x => η * P.H0 + P.allocF1 η ζ x) (P.lam * (P.K1 / u)) / P.lam)
          * ∫⁻ ω, ((unfinishedCount (π.x1 ω) (fun t => π.U1 t ω) (fun t => S.N t ω)
              (T - P.L1) : ℕ) : ℝ≥0∞) ∂S.ν
        + ENNReal.ofReal u
          * ENNReal.ofReal (cycCost (P.allocF2 η ζ) (P.lam * (P.K2 / u)) / P.lam)
          * ∫⁻ ω, ((unfinishedCount (π.x2 ω) (fun t => π.U2 t ω) (fun t => S.N t ω)
              (T - (P.L1 + P.L2)) : ℕ) : ℝ≥0∞) ∂S.ν) := by
  have hu0 : 0 < u := hu.1
  have hu1 : u ≤ 1 := hu.2
  have hαβ : ENNReal.ofReal (1 - u) + ENNReal.ofReal u = 1 := by
    rw [← ENNReal.ofReal_add (by linarith) hu0.le, sub_add_cancel, ENNReal.ofReal_one]
  have hs : DI (fun p => ENNReal.ofReal (c1 π η ζ p.2 p.1)) (Set.Ioc 0 T)
      + DI (fun p => ENNReal.ofReal (c2 π η ζ p.2 p.1)) (Set.Ioc 0 T)
      = DI (fun p => ENNReal.ofReal (π.cI p.2 p.1)) (Set.Ioc 0 T) := by
    have h := DI_add (c1_meas π η ζ) (c2_meas π η ζ) 1 (Set.Ioc 0 T)
    simp only [one_mul] at h
    rw [← h]
    exact DI_congr measurableSet_Ioc (fun ω t ht => by
      show ENNReal.ofReal (c1 π η ζ t ω) + ENNReal.ofReal (c2 π η ζ t ω) = ENNReal.ofReal (π.cI t ω)
      rw [← ENNReal.ofReal_add (c1_nonneg π hη hζ ht.1.le ω) (c2_nonneg π hη hζ ht.1.le ω),
        c1_add_c2])
  have hm1 : ENNReal.ofReal u * ENNReal.ofReal (P.K1 / u) = ENNReal.ofReal P.K1 := by
    rw [← ENNReal.ofReal_mul hu0.le]; congr 1; field_simp
  have hm2 : ENNReal.ofReal u * ENNReal.ofReal (P.K2 / u) = ENNReal.ofReal P.K2 := by
    rw [← ENNReal.ofReal_mul hu0.le]; congr 1; field_simp
  have hS : ENNReal.ofReal P.K1 * ∫⁻ ω, ((jumpCount (fun t => π.U1 t ω) T : ℕ) : ℝ≥0∞) ∂S.ν
      + ENNReal.ofReal P.K2 * ∫⁻ ω, ((jumpCount (fun t => π.U2 t ω) T : ℕ) : ℝ≥0∞) ∂S.ν
      ≤ ∫⁻ ω, ENNReal.ofReal (π.shipSetup T ω) ∂S.ν := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine le_trans (le_lintegral_add _ _) (le_of_eq (lintegral_congr (fun ω => ?_)))
    show _ = ENNReal.ofReal (P.K1 * (jumpCount (fun t => π.U1 t ω) T : ℝ)
      + P.K2 * (jumpCount (fun t => π.U2 t ω) T : ℝ))
    rw [ENNReal.ofReal_add (mul_nonneg P.K1_nonneg (Nat.cast_nonneg _))
        (mul_nonneg P.K2_nonneg (Nat.cast_nonneg _)),
      ENNReal.ofReal_mul P.K1_nonneg, ENNReal.ofReal_mul P.K2_nonneg, ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast]
  have hE : DI (fun p => ENNReal.ofReal (π.cI p.2 p.1)) (Set.Ioc 0 T)
      + ∫⁻ ω, ENNReal.ofReal (π.shipSetup T ω) ∂S.ν
      ≤ ∫⁻ ω, ((∫⁻ t in Set.Ioc 0 T, ENNReal.ofReal (π.cI t ω))
          + ENNReal.ofReal (π.shipSetup T ω)) ∂S.ν :=
    le_lintegral_add _ _
  exact comb hαβ (zero_chain π hadm (T := T) (by linarith)) (chain1 π hadm hlam hu hη hζ hT)
    (chain2 π hadm hlam hu hη hζ hT) hs hm1 hm2 hS hE

theorem main_bound (hlam : 0 < P.lam) (hadm : π.Admissible π.shipSetup) {u : ℝ}
    (hu : u ∈ Set.Ioc (0 : ℝ) 1) {η ζ : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1)
    (hζ : ζ ∈ Set.Icc (0 : ℝ) 1) :
    ENNReal.ofReal ((1 - u) * P.V0 + u * (η * P.H0 + cycCost (P.allocF1 η ζ) (P.k1 / u)
      + cycCost (P.allocF2 η ζ) (P.k2 / u))) ≤ π.shipCost := by
  have hL1 := P.L1_nonneg
  have hL2 := P.L2_nonneg
  have hu0 : 0 < u := hu.1
  have hu1 : u ≤ 1 := hu.2
  have hk1 : 0 ≤ P.k1 / u := div_nonneg (mul_nonneg P.lam_nonneg P.K1_nonneg) hu0.le
  have hk2 : 0 ≤ P.k2 / u := div_nonneg (mul_nonneg P.lam_nonneg P.K2_nonneg) hu0.le
  have ha0 : 0 ≤ P.V0 := V0_nonneg P
  have ha1 : 0 ≤ η * P.H0 + cycCost (P.allocF1 η ζ) (P.k1 / u) :=
    add_nonneg (mul_nonneg hη.1 P.H0_nonneg) (cycCost_nonneg (P.allocF1_nonneg hη hζ) hk1)
  have ha2 : 0 ≤ cycCost (P.allocF2 η ζ) (P.k2 / u) :=
    cycCost_nonneg (P.allocF2_nonneg hη hζ) hk2
  have h1u : 0 ≤ 1 - u := by linarith
  show _ ≤ limsup (fun T : ℝ => ENNReal.ofReal T⁻¹ *
    ∫⁻ ω, ((∫⁻ t in Set.Ioc 0 T, ENNReal.ofReal (π.cI t ω))
      + ENNReal.ofReal (π.shipSetup T ω)) ∂S.ν) atTop
  refine le_limsup_of_le_add
    (f := fun T => ENNReal.ofReal T⁻¹ *
      (ENNReal.ofReal (1 - u) * (ENNReal.ofReal P.V0 * ENNReal.ofReal (T - (P.L1 + P.L2)))
      + ENNReal.ofReal u * ENNReal.ofReal ((η * P.H0 + cycCost (P.allocF1 η ζ) (P.k1 / u)) * (T - P.L1))
      + ENNReal.ofReal u * ENNReal.ofReal (cycCost (P.allocF2 η ζ) (P.k2 / u) * (T - (P.L1 + P.L2)))))
    (h := fun T => ENNReal.ofReal T⁻¹ *
      ((ENNReal.ofReal (1 - u) * ENNReal.ofReal P.h2 + ENNReal.ofReal u * ENNReal.ofReal (η * P.h2))
          * Wb π T
        + ENNReal.ofReal u
          * ENNReal.ofReal (cycCost (fun x => η * P.H0 + P.allocF1 η ζ x) (P.lam * (P.K1 / u)) / P.lam)
          * ∫⁻ ω, ((unfinishedCount (π.x1 ω) (fun t => π.U1 t ω) (fun t => S.N t ω)
              (T - P.L1) : ℕ) : ℝ≥0∞) ∂S.ν
        + ENNReal.ofReal u
          * ENNReal.ofReal (cycCost (P.allocF2 η ζ) (P.lam * (P.K2 / u)) / P.lam)
          * ∫⁻ ω, ((unfinishedCount (π.x2 ω) (fun t => π.U2 t ω) (fun t => S.N t ω)
              (T - (P.L1 + P.L2)) : ℕ) : ℝ≥0∞) ∂S.ν)) ?_ ?_ ?_
  ·
    set A := (1 - u) * P.V0 + u * (η * P.H0 + cycCost (P.allocF1 η ζ) (P.k1 / u)
      + cycCost (P.allocF2 η ζ) (P.k2 / u)) with hA
    set B := (1 - u) * P.V0 * (P.L1 + P.L2)
      + u * (η * P.H0 + cycCost (P.allocF1 η ζ) (P.k1 / u)) * P.L1
      + u * cycCost (P.allocF2 η ζ) (P.k2 / u) * (P.L1 + P.L2) with hB
    have hreal : Tendsto (fun T : ℝ => A - B * T⁻¹) atTop (𝓝 A) := by
      have := (tendsto_const_nhds (x := A)).sub (tendsto_inv_atTop_zero.const_mul B)
      simpa using this
    refine (ENNReal.tendsto_ofReal hreal).congr' ?_
    filter_upwards [eventually_gt_atTop (P.L1 + P.L2)] with T hT
    have hT0 : 0 < T := by linarith
    have hT1 : 0 ≤ T - P.L1 := by linarith
    have hTS : 0 ≤ T - (P.L1 + P.L2) := by linarith
    have e : A - B * T⁻¹ = T⁻¹ * ((1 - u) * (P.V0 * (T - (P.L1 + P.L2)))
        + u * ((η * P.H0 + cycCost (P.allocF1 η ζ) (P.k1 / u)) * (T - P.L1))
        + u * (cycCost (P.allocF2 η ζ) (P.k2 / u) * (T - (P.L1 + P.L2)))) := by
      rw [hA, hB]; field_simp; ring
    rw [e, ENNReal.ofReal_mul (inv_nonneg.2 hT0.le),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul h1u, ENNReal.ofReal_mul ha0, ENNReal.ofReal_mul hu0.le,
      ENNReal.ofReal_mul hu0.le]
  ·
    have hW := Wb_tendsto π hadm
    have hU1 := shift_tendsto hadm.unfinished_1 hL1
    have hU2 := shift_tendsto hadm.unfinished_2 (add_nonneg hL1 hL2)
    have hc0 : ENNReal.ofReal (1 - u) * ENNReal.ofReal P.h2
        + ENNReal.ofReal u * ENNReal.ofReal (η * P.h2) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩
    have hc1 : ENNReal.ofReal u
        * ENNReal.ofReal (cycCost (fun x => η * P.H0 + P.allocF1 η ζ x) (P.lam * (P.K1 / u)) / P.lam)
        ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    have hc2 : ENNReal.ofReal u
        * ENNReal.ofReal (cycCost (P.allocF2 η ζ) (P.lam * (P.K2 / u)) / P.lam) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    have t := ((ENNReal.Tendsto.const_mul (a := _) hW (Or.inr hc0)).add
      (ENNReal.Tendsto.const_mul (a := _) hU1 (Or.inr hc1))).add
      (ENNReal.Tendsto.const_mul (a := _) hU2 (Or.inr hc2))
    simp only [mul_zero, add_zero] at t
    refine t.congr (fun T => ?_)
    ring
  · filter_upwards [eventually_ge_atTop (2 * (P.L1 + P.L2) + 1)] with T hT
    exact (mul_le_mul' le_rfl (fin_bound π hlam hadm hu hη hζ hT)).trans_eq (mul_add _ _ _)

theorem LBsp_le_shipCost (hadm : π.Admissible π.shipSetup) :
    ENNReal.ofReal P.LBsp ≤ π.shipCost := by
  rcases P.lam_nonneg.eq_or_lt with h0 | hlam
  · rw [ENNReal.ofReal_of_nonpos (LBsp_nonpos h0.symm)]; exact zero_le
  · by_cases htop : π.shipCost = ⊤
    · rw [htop]; exact le_top
    · rw [ENNReal.ofReal_le_iff_le_toReal htop]
      have : Nonempty (Set.Ioc (0 : ℝ) 1) := ⟨⟨1, zero_lt_one, le_rfl⟩⟩
      refine ciSup_le (fun u => ?_)
      have hu : (u : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := u.2
      have : Nonempty {q : ℝ × ℝ // q.1 ∈ Set.Icc (0 : ℝ) 1 ∧ q.2 ∈ Set.Icc (0 : ℝ) 1} :=
        ⟨⟨(0, 0), ⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩⟩
      have hAq : P.allocBound (P.k1 / u) (P.k2 / u)
          ≤ (π.shipCost.toReal - (1 - (u : ℝ)) * P.V0) / u := by
        refine ciSup_le (fun q => ?_)
        rw [le_div_iff₀ hu.1]
        have hb := main_bound π hlam hadm hu q.2.1 q.2.2
        have hb' := (ENNReal.ofReal_le_iff_le_toReal htop).mp hb
        linarith
      have h2 := (le_div_iff₀ hu.1).mp hAq
      linarith

end LBA

theorem LBsp_le_OPTsh_pf (P : Params) : ENNReal.ofReal P.LBsp ≤ OPTsh P :=
  le_iInf (fun _S => le_iInf (fun π => le_iInf (fun hadm => LBA.LBsp_le_shipCost π hadm)))

end TwoStageRnQ

namespace TwoStageRnQ

theorem _root_.solution (P : Params) :
    ENNReal.ofReal P.LBsp ≤ OPTsh P :=
  LBsp_le_OPTsh_pf P

end TwoStageRnQ
