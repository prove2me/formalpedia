-- Prove2me | solution 1 for ProbabilityTheory.integral_prod_pow_thinnedCount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:35:54.159111+00:00
-- url     : https://prove2.me/submissions/6e7cde0d-bfbe-4d61-9575-d7007ccdb2ff

import Definitions.Def_LeanLevy_Probability_Poisson
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Order.Disjointed
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ProbabilityTheory MeasureTheory Complex
open scoped ENNReal NNReal

variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
  {m : Measure E} [SigmaFinite m] [Nonempty E] {μ : Measure Ω} {k : ℕ}
  {A B : Set E}

private lemma prod_ite_const {ι : Type*} (s : Finset ι) (p : ι → Prop) [DecidablePred p] (z : ℂ) :
    ∏ i ∈ s, (if p i then z else 1) = z ^ (s.filter p).card := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

private lemma integral_indicator_const_complex {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {s : Set α} (c : ℂ) (hs : MeasurableSet s) :
    ∫ x, s.indicator (fun _ => c) x ∂ν = (ν.real s : ℂ) * c := by
  rw [integral_indicator_const c hs]; exact Complex.real_smul

private theorem prmPieceLaw_of_ne_zero (hk : m (prmPiece m k) ≠ 0) :
    prmPieceLaw m k = (m (prmPiece m k))⁻¹ • m.restrict (prmPiece m k) := by
  unfold prmPieceLaw
  rw [if_neg hk]

private lemma toReal_mul_real_prmPieceLaw (hA : MeasurableSet A) :
    (m (prmPiece m k)).toReal * (prmPieceLaw m k).real A = (m (prmPiece m k ∩ A)).toReal := by
  by_cases h : m (prmPiece m k) = 0
  · have h2 : m (prmPiece m k ∩ A) = 0 := measure_mono_null Set.inter_subset_left h
    rw [h, ENNReal.toReal_zero, zero_mul, h2, ENNReal.toReal_zero]
  · rw [prmPieceLaw_of_ne_zero h, measureReal_def, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply hA, ENNReal.toReal_mul, ENNReal.toReal_inv, ← mul_assoc,
      mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨h, measure_prmPiece_lt_top.ne⟩), one_mul,
      Set.inter_comm]

open Classical in
omit [MeasurableSpace E] [Nonempty E] in
private lemma prod_ite_eq_one_add_sum_indicator {ι : Type} [Fintype ι] {A : ι → Set E}
    (hdisj : Pairwise (Function.onFun Disjoint A)) (z : ι → ℂ) (x : E) :
    ∏ i, (if x ∈ A i then z i else 1)
      = 1 + ∑ i, (A i).indicator (fun _ => z i - 1) x := by
  by_cases hx : ∃ i, x ∈ A i
  · obtain ⟨i₀, hi₀⟩ := hx
    have huniq : ∀ i, i ≠ i₀ → x ∉ A i := fun i hi hmem =>
      Set.disjoint_left.mp (hdisj hi) hmem hi₀
    rw [Finset.prod_eq_single i₀ (fun i _ hi => if_neg (huniq i hi)) (by simp), if_pos hi₀,
      Finset.sum_eq_single i₀ (fun i _ hi => Set.indicator_of_notMem (huniq i hi) _) (by simp),
      Set.indicator_of_mem hi₀]
    ring
  · push Not at hx
    rw [Finset.prod_eq_one (fun i _ => if_neg (hx i)),
      Finset.sum_eq_zero (fun i _ => Set.indicator_of_notMem (hx i) _)]
    ring

theorem solution {ι : Type} [Fintype ι] [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) {A : ι → Set E} (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A)) (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ∫ ω, ∏ i, (z i) ^ (thinnedCount K X (A i) k ω) ∂μ
      = ∏ i, Complex.exp ((m (prmPiece m k ∩ A i)).toReal * (z i - 1)) := by
  classical
  set w : E → ℂ := fun x => ∏ i, (if x ∈ A i then z i else 1) with hw_def
  have hwmeas : Measurable w :=
    Finset.measurable_prod _ fun i _ => Measurable.ite (hA i) measurable_const measurable_const
  have hwbdd : ∀ x, ‖w x‖ ≤ 1 := by
    intro x
    rw [hw_def, norm_prod]
    refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => ?_
    split_ifs with hx
    · exact hz i
    · simp
  have hprod : ∀ ω, ∏ i, (z i) ^ (thinnedCount K X (A i) k ω)
      = ∏ n ∈ Finset.range (K k ω), w (X k n ω) := by
    intro ω
    simp only [hw_def]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [prod_ite_const (Finset.range (K k ω)) (fun n => X k n ω ∈ A i) (z i), thinnedCount]
  simp_rw [hprod]
  rw [integral_pieceProd_eq_exp hd hwmeas hwbdd]
  have hint : ∫ x, w x ∂(prmPieceLaw m k)
      = 1 + ∑ i, (z i - 1) * ((prmPieceLaw m k).real (A i)) := by
    have hwrw : w = fun x => (1 : ℂ) + ∑ i, (A i).indicator (fun _ => z i - 1) x := by
      funext x; rw [hw_def]; exact prod_ite_eq_one_add_sum_indicator hdisj z x
    have hintegrable : ∀ i,
        Integrable (fun x => (A i).indicator (fun _ => z i - 1) x) (prmPieceLaw m k) :=
      fun i => (integrable_const (z i - 1)).indicator (hA i)
    have hone : ∫ _ : E, (1 : ℂ) ∂(prmPieceLaw m k) = 1 := by simp
    rw [hwrw, integral_add (integrable_const 1) (integrable_finsetSum _ fun i _ => hintegrable i),
      integral_finsetSum _ (fun i _ => hintegrable i), hone]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_indicator_const_complex (z i - 1) (hA i)]
    ring
  rw [hint,
    show ((m (prmPiece m k)).toReal : ℂ)
          * ((1 + ∑ i, (z i - 1) * ((prmPieceLaw m k).real (A i))) - 1)
        = ∑ i, (((m (prmPiece m k)).toReal * (prmPieceLaw m k).real (A i) : ℝ) : ℂ) * (z i - 1) from ?_]
  · rw [Complex.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [toReal_mul_real_prmPieceLaw (hA i)]
  · push_cast
    rw [add_sub_cancel_left, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
