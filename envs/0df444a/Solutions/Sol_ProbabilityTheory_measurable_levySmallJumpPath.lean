-- Prove2me | solution 1 for ProbabilityTheory.measurable_levySmallJumpPath
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:09:13.297668+00:00
-- url     : https://prove2.me/submissions/f2391794-f7b6-4475-acf5-c1de73f83eb7

import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Theorems.Thm_ProbabilityTheory_isCadlag_stepIndicator
import Theorems.Thm_ProbabilityTheory_measurable_bandFun
import Theorems.Thm_ProbabilityTheory_levyTruncationSeq_spec
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Definitions.Def_LeanLevy_Probability_Poisson
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Processes_PoissonProcess
import Definitions.Def_LeanLevy_Processes_StochasticProcess
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpLaw
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_LeanLevy_RandomMeasure_PoissonMartingale
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.ConjExponents
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.PiSystem
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Disjointed
import Mathlib.Order.Preorder.Finite
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.ProductMeasure
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Sequences
open ProbabilityTheory
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ}
  {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω} {A : Set ℝ}
open Filter Set Topology
open scoped NNReal
namespace ProbabilityTheory
variable {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [Preorder α]
theorem IsCadlag.rightContinuous {f : α → β} (hf : IsCadlag f) (t : α) :
    ContinuousWithinAt f (Ici t) t :=
  (hf t).1
end ProbabilityTheory
namespace ProbabilityTheory
variable {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [Preorder α]
theorem IsCadlagAt.congr {f g : α → β} {t : α} (hf : IsCadlagAt f t) (h : f =ᶠ[𝓝 t] g) :
    IsCadlagAt g t := by
  obtain ⟨hc, l, hl⟩ := hf
  refine ⟨?_, l, ?_⟩
  · exact hc.congr_of_eventuallyEq (h.filter_mono nhdsWithin_le_nhds).symm h.eq_of_nhds.symm
  · exact hl.congr' (h.filter_mono nhdsWithin_le_nhds)
theorem IsCadlagAt.add {β : Type*} [TopologicalSpace β] [AddCommMonoid β] [ContinuousAdd β]
    {f g : α → β} {t : α} (hf : IsCadlagAt f t) (hg : IsCadlagAt g t) :
    IsCadlagAt (fun s => f s + g s) t := by
  obtain ⟨hfc, lf, hlf⟩ := hf
  obtain ⟨hgc, lg, hlg⟩ := hg
  exact ⟨hfc.add hgc, lf + lg, hlf.add hlg⟩
theorem IsCadlag.add {β : Type*} [TopologicalSpace β] [AddCommMonoid β] [ContinuousAdd β]
    {f g : α → β} (hf : IsCadlag f) (hg : IsCadlag g) : IsCadlag (fun s => f s + g s) :=
  fun t => (hf t).add (hg t)
theorem IsCadlag.finsetSum {β : Type*} [TopologicalSpace β] [AddCommMonoid β] [ContinuousAdd β]
    {ι : Type*} (s : Finset ι) {f : ι → α → β} (h : ∀ i ∈ s, IsCadlag (f i)) :
    IsCadlag (fun t => ∑ i ∈ s, f i t) := by
  classical
  intro t
  refine ⟨tendsto_finsetSum s (fun i hi => (h i hi t).1), ?_⟩
  choose! l hl using fun i (hi : i ∈ s) => (h i hi t).2
  exact ⟨∑ i ∈ s, l i, tendsto_finsetSum s (fun i hi => hl i hi)⟩
end ProbabilityTheory
variable {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [Preorder α]
theorem Continuous.isCadlag {f : α → β} (hf : Continuous f) : ProbabilityTheory.IsCadlag f :=
  fun t => ⟨hf.continuousWithinAt, f t, (hf.tendsto t).mono_left nhdsWithin_le_nhds⟩
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
namespace ProbabilityTheory
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ}
  {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω} {A : Set ℝ}
theorem measurable_bandJumpSum (hK : ∀ k, Measurable (K k)) (hX : ∀ k n, Measurable (X k n))
    (hA : MeasurableSet A) (t : ℝ) : Measurable (bandJumpSum K X A t) :=
  Measurable.tsum fun k =>
    measurable_pieceSum (hK k) (fun n => hX k n) (measurable_bandFun hA 0 t)
private noncomputable def bandStepFinsetSum (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → ℝ × ℝ)
    (A : Set ℝ) (ω : Ω) (S : Finset ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ S, ∑ n ∈ Finset.range (K k ω),
    (if (X k n ω).1 ≤ t then
      ({p : ℝ × ℝ | 0 < p.1 ∧ p.2 ∈ A}).indicator (fun p : ℝ × ℝ => p.2) (X k n ω) else 0)
omit [MeasurableSpace Ω] in
private lemma isCadlag_bandStepFinsetSum (A : Set ℝ) (ω : Ω) (S : Finset ℕ) :
    IsCadlag (fun t : ℝ => bandStepFinsetSum K X A ω S t) := by
  simp only [bandStepFinsetSum]
  exact IsCadlag.finsetSum _ fun k _ => IsCadlag.finsetSum _ fun n _ => isCadlag_stepIndicator
omit [MeasurableSpace Ω] in
private lemma bandJumpSum_eqOn_Iio (A : Set ℝ) (ω : Ω) {T : ℕ}
    (hfin : {k | ∃ n ∈ Finset.range (K k ω), X k n ω ∈ Set.Ioc 0 (T : ℝ) ×ˢ A}.Finite) :
    Set.EqOn (fun t : ℝ => bandJumpSum K X A t ω)
      (fun t : ℝ => bandStepFinsetSum K X A ω hfin.toFinset t) (Set.Iio (T : ℝ)) := by
  intro t ht
  simp only [Set.mem_Iio] at ht
  have htT : t ≤ (T : ℝ) := le_of_lt ht
  have hvanish : ∀ k ∉ hfin.toFinset,
      pieceSum K X ((Set.Ioc 0 t ×ˢ A).indicator fun p : ℝ × ℝ => p.2) k ω = 0 := by
    intro k hk
    simp only [pieceSum]
    refine Finset.sum_eq_zero fun n hn => ?_
    refine Set.indicator_of_notMem ?_ _
    intro hmem
    exact hk (hfin.mem_toFinset.mpr ⟨n, hn, Set.mem_prod.mpr
      ⟨Set.Ioc_subset_Ioc le_rfl htT (Set.mem_prod.mp hmem).1, (Set.mem_prod.mp hmem).2⟩⟩)
  simp only [bandJumpSum, bandStepFinsetSum]
  rw [tsum_eq_sum hvanish]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [pieceSum]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hut : (X k n ω).1 ≤ t
  · rw [if_pos hut]
    rcases em (X k n ω ∈ Set.Ioc 0 t ×ˢ A) with hm | hm
    · rw [Set.indicator_of_mem hm,
        Set.indicator_of_mem (show X k n ω ∈ {p : ℝ × ℝ | 0 < p.1 ∧ p.2 ∈ A} from
          ⟨(Set.mem_Ioc.mp (Set.mem_prod.mp hm).1).1, (Set.mem_prod.mp hm).2⟩)]
    · rw [Set.indicator_of_notMem hm,
        Set.indicator_of_notMem (show X k n ω ∉ {p : ℝ × ℝ | 0 < p.1 ∧ p.2 ∈ A} from
          fun hc => hm (Set.mem_prod.mpr ⟨Set.mem_Ioc.mpr ⟨hc.1, hut⟩, hc.2⟩))]
  · rw [if_neg hut,
      Set.indicator_of_notMem (fun hmem => hut (Set.mem_Ioc.mp (Set.mem_prod.mp hmem).1).2)]
omit [SigmaFinite ν] in
theorem measurable_levyBandPath (hK : ∀ k, Measurable (K k)) (hX : ∀ k n, Measurable (X k n))
    (hA : MeasurableSet A) (t : ℝ) : Measurable (levyBandPath K X ν A t) :=
  (measurable_bandJumpSum hK hX hA t).sub measurable_const
lemma levyAnnulus_mono : Monotone levyAnnulus := by
  intro m n hmn
  refine Set.inter_subset_inter_right _ fun x hx => ?_
  simp only [Set.mem_setOf_eq] at hx ⊢
  refine le_trans ?_ hx
  have h : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hmn
  gcongr
omit [SigmaFinite ν] in
lemma levySlice_subset (hν : IsLevyMeasure ν) (j : ℕ) : levySlice hν j ⊆ Set.Ioo (-1 : ℝ) 1 :=
  Set.sdiff_subset.trans (levyAnnulus_subset _)
omit [SigmaFinite ν] in
lemma measurableSet_levySlice (hν : IsLevyMeasure ν) (j : ℕ) : MeasurableSet (levySlice hν j) :=
  (measurableSet_levyAnnulus _).diff (measurableSet_levyAnnulus _)
omit [SigmaFinite ν] in
lemma levySlice_finite_mass (hν : IsLevyMeasure ν) (j : ℕ) : ν (levySlice hν j) < ⊤ :=
  (measure_mono Set.sdiff_subset).trans_lt (levyAnnulus_finite_mass hν _)
lemma levyAnnulus_succ_eq (hν : IsLevyMeasure ν) (j : ℕ) :
    levyAnnulus (levyTruncationSeq hν (j + 1))
      = levyAnnulus (levyTruncationSeq hν j) ∪ levySlice hν j :=
  (Set.union_sdiff_cancel
    (levyAnnulus_mono ((levyTruncationSeq_spec hν).1 (Nat.lt_succ_self j)).le)).symm
omit [SigmaFinite ν] in
lemma disjoint_levyAnnulus_levySlice (hν : IsLevyMeasure ν) (j : ℕ) :
    Disjoint (levyAnnulus (levyTruncationSeq hν j)) (levySlice hν j) :=
  disjoint_sdiff_self_right
theorem measurableSet_levySmallJumpGoodSet
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν) :
    MeasurableSet (levySmallJumpGoodSet hd hν) :=
  (measurableSet_toMeasurable _ _).compl
lemma levySmallJumpRaw_of_mem_goodSet
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {ω : Ω} (hω : ω ∈ levySmallJumpGoodSet hd hν) : levySmallJumpRaw hd hν ω := by
  by_contra h
  exact hω (subset_toMeasurable μ {ω | ¬ levySmallJumpRaw hd hν ω} h)
omit [MeasurableSpace Ω] in
private lemma finite_pieces_Ioc_of_forall_nat {A : Set ℝ} {ω : Ω}
    (hfin : ∀ T : ℕ, {k | ∃ n ∈ Finset.range (K k ω),
      X k n ω ∈ Set.Ioc 0 (T : ℝ) ×ˢ A}.Finite) (t : ℝ) :
    {k | ∃ n ∈ Finset.range (K k ω), X k n ω ∈ Set.Ioc 0 t ×ˢ A}.Finite := by
  obtain ⟨T, hT⟩ := exists_nat_gt t
  refine (hfin T).subset fun k hk => ?_
  obtain ⟨n, hn, hmem⟩ := hk
  exact ⟨n, hn, Set.mem_prod.mpr
    ⟨Set.Ioc_subset_Ioc (le_refl 0) hT.le (Set.mem_prod.mp hmem).1, (Set.mem_prod.mp hmem).2⟩⟩
omit [MeasurableSpace Ω] in
private lemma summable_pieceSum_band_of_finite {A : Set ℝ} {ω : Ω} (t : ℝ)
    (hfin : {k | ∃ n ∈ Finset.range (K k ω), X k n ω ∈ Set.Ioc 0 t ×ˢ A}.Finite) :
    Summable (fun k => pieceSum K X ((Set.Ioc 0 t ×ˢ A).indicator fun p : ℝ × ℝ => p.2) k ω) := by
  refine summable_of_ne_finset_zero (s := hfin.toFinset) fun k hk => ?_
  simp only [pieceSum]
  refine Finset.sum_eq_zero fun n hn => ?_
  exact Set.indicator_of_notMem (fun hmem => hk (hfin.mem_toFinset.mpr ⟨n, hn, hmem⟩)) _
omit [MeasurableSpace Ω] [SigmaFinite ν] in
private lemma integrableOn_id_of_subset {A : Set ℝ} (hA : MeasurableSet A)
    (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤) :
    IntegrableOn (fun x : ℝ => x) A ν := by
  refine IntegrableOn.of_bound hAfin measurable_id.aestronglyMeasurable 1 ?_
  filter_upwards [ae_restrict_mem hA] with x hx
  have hx' := hAsub hx
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
omit [MeasurableSpace Ω] [SigmaFinite ν] in
private lemma levyBandPath_union_of_finite {A B : Set ℝ} {ω : Ω} (t : ℝ)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤)
    (hB : MeasurableSet B) (hBsub : B ⊆ Set.Ioo (-1 : ℝ) 1) (hBfin : ν B < ⊤)
    (hAB : Disjoint A B)
    (hfinA : {k | ∃ n ∈ Finset.range (K k ω), X k n ω ∈ Set.Ioc 0 t ×ˢ A}.Finite)
    (hfinB : {k | ∃ n ∈ Finset.range (K k ω), X k n ω ∈ Set.Ioc 0 t ×ˢ B}.Finite) :
    levyBandPath K X ν (A ∪ B) t ω = levyBandPath K X ν A t ω + levyBandPath K X ν B t ω := by
  have hind : ((Set.Ioc 0 t ×ˢ (A ∪ B)).indicator fun p : ℝ × ℝ => p.2)
      = ((Set.Ioc 0 t ×ˢ A).indicator fun p : ℝ × ℝ => p.2)
        + ((Set.Ioc 0 t ×ˢ B).indicator fun p : ℝ × ℝ => p.2) := by
    rw [Set.prod_union]
    exact Set.indicator_union_of_disjoint (Set.Disjoint.set_prod_right hAB _ _) _
  have hbjs : bandJumpSum K X (A ∪ B) t ω = bandJumpSum K X A t ω + bandJumpSum K X B t ω := by
    simp only [bandJumpSum]
    rw [← (summable_pieceSum_band_of_finite t hfinA).tsum_add
      (summable_pieceSum_band_of_finite t hfinB)]
    refine tsum_congr fun k => ?_
    simp only [pieceSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simpa using congrFun hind (X k n ω)
  have hdrift : ∫ x in A ∪ B, x ∂ν = (∫ x in A, x ∂ν) + ∫ x in B, x ∂ν :=
    setIntegral_union hAB hB (integrableOn_id_of_subset hA hAsub hAfin)
      (integrableOn_id_of_subset hB hBsub hBfin)
  simp only [levyBandPath, hbjs, hdrift]; ring
private lemma levyBandPath_annulus_succ
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {ω : Ω} (hraw : levySmallJumpRaw hd hν ω) (j : ℕ) (t : ℝ) :
    levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν (j + 1))) t ω
      = levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν j)) t ω
        + levyBandPath K X ν (levySlice hν j) t ω := by
  rw [levyAnnulus_succ_eq hν j]
  exact levyBandPath_union_of_finite t
    (measurableSet_levyAnnulus _) (levyAnnulus_subset _)
    (levyAnnulus_finite_mass hν _) (measurableSet_levySlice hν j)
    (levySlice_subset hν j) (levySlice_finite_mass hν j)
    (disjoint_levyAnnulus_levySlice hν j)
    (finite_pieces_Ioc_of_forall_nat (fun T => hraw.1 T j) t)
    (finite_pieces_Ioc_of_forall_nat (fun T => hraw.2.1 T j) t)
omit [MeasurableSpace Ω] in
private lemma isCadlag_bandJumpSum_of_finite {A : Set ℝ} (ω : Ω)
    (hfin : ∀ T : ℕ, {k | ∃ n ∈ Finset.range (K k ω),
      X k n ω ∈ Set.Ioc 0 (T : ℝ) ×ˢ A}.Finite) :
    IsCadlag (fun t : ℝ => bandJumpSum K X A t ω) := by
  intro t
  obtain ⟨T, hT⟩ := exists_nat_gt t
  refine (isCadlag_bandStepFinsetSum (K := K) (X := X) A ω (hfin T).toFinset t).congr ?_
  filter_upwards [Iio_mem_nhds hT] with s hs
  exact (bandJumpSum_eqOn_Iio A ω (hfin T) hs).symm
omit [MeasurableSpace Ω] [SigmaFinite ν] in
private lemma isCadlag_levyBandPath_of_finite {A : Set ℝ} (ω : Ω)
    (hfin : ∀ T : ℕ, {k | ∃ n ∈ Finset.range (K k ω),
      X k n ω ∈ Set.Ioc 0 (T : ℝ) ×ˢ A}.Finite) :
    IsCadlag (fun t : ℝ => levyBandPath K X ν A t ω) := by
  have hcont : Continuous (fun t : ℝ => -(t * ∫ x in A, x ∂ν)) := by fun_prop
  simpa only [levyBandPath, sub_eq_add_neg] using
    (isCadlag_bandJumpSum_of_finite ω hfin).add hcont.isCadlag
omit [MeasurableSpace Ω] in
private lemma abs_le_of_isCadlag_of_grid {g : ℝ → ℝ} {T : ℕ} {c : ℝ} (hg : IsCadlag g)
    (hgrid : ∀ q ∈ levyGrid T, |g q| ≤ c) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (T : ℝ)) :
    |g t| ≤ c := by
  rcases eq_or_lt_of_le ht.2 with htT | htT
  · rw [htT]; exact hgrid (T : ℝ) (Or.inr rfl)
  · set d : ℝ := (T : ℝ) - t with hddef
    have hdpos : 0 < d := by rw [hddef]; linarith
    have hex : ∀ n : ℕ, ∃ q : ℚ, t < (q : ℝ) ∧ (q : ℝ) < t + d / ((n : ℝ) + 2) := fun n =>
      exists_rat_btwn (by
        have hpos : (0 : ℝ) < d / ((n : ℝ) + 2) := by positivity
        linarith)
    choose q hq using hex
    have hqT : ∀ n, (q n : ℝ) < (T : ℝ) := fun n => by
      have hle : d / ((n : ℝ) + 2) ≤ d :=
        div_le_self hdpos.le (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
      calc (q n : ℝ) < t + d / ((n : ℝ) + 2) := (hq n).2
        _ ≤ t + d := by linarith
        _ = (T : ℝ) := by rw [hddef]; ring
    have hqmem : ∀ n, (q n : ℝ) ∈ levyGrid T := fun n =>
      Or.inl ⟨⟨q n, rfl⟩, ⟨le_of_lt (lt_of_le_of_lt ht.1 (hq n).1), le_of_lt (hqT n)⟩⟩
    have hd0 : Tendsto (fun n : ℕ => d / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds
        (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
    have hqtend : Tendsto (fun n => (q n : ℝ)) atTop (𝓝 t) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (by simpa using tendsto_const_nhds.add hd0)
        (Filter.Eventually.of_forall fun n => (hq n).1.le)
        (Filter.Eventually.of_forall fun n => (hq n).2.le)
    have hmem : Tendsto (fun n => (q n : ℝ)) atTop (𝓝[Set.Ici t] t) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hqtend
        (Filter.Eventually.of_forall fun n => (hq n).1.le)
    have hgq : Tendsto (fun n => g (q n : ℝ)) atTop (𝓝 (g t)) :=
      (hg.rightContinuous t).tendsto.comp hmem
    refine le_of_tendsto ((continuous_abs.tendsto _).comp hgq) ?_
    exact Filter.Eventually.of_forall fun n => hgrid _ (hqmem n)
private lemma abs_annulusPath_sub_le
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {ω : Ω} (hraw : levySmallJumpRaw hd hν ω) (T : ℕ) {N₀ : ℕ}
    (hbound : ∀ j, N₀ ≤ j → ∀ y ∈ Set.Icc (0 : ℝ) (T : ℝ),
      |levyBandPath K X ν (levySlice hν j) y ω| ≤ ((2 : ℝ)⁻¹) ^ j)
    {m n : ℕ} (hm : N₀ ≤ m) (hmn : m ≤ n) {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) (T : ℝ)) :
    |levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν n)) y ω
        - levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν m)) y ω| ≤ 2 * ((2 : ℝ)⁻¹) ^ m := by
  set f : ℕ → ℝ := fun i => levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν (m + i))) y ω
    with hf
  have htel : levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν n)) y ω
        - levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν m)) y ω
      = ∑ i ∈ Finset.range (n - m), levyBandPath K X ν (levySlice hν (m + i)) y ω := by
    have hstep : ∀ i, f (i + 1) - f i = levyBandPath K X ν (levySlice hν (m + i)) y ω := by
      intro i
      simp only [hf, show m + (i + 1) = (m + i) + 1 from by ring]
      rw [levyBandPath_annulus_succ hd hν hraw (m + i) y]; ring
    calc levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν n)) y ω
          - levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν m)) y ω
        = f (n - m) - f 0 := by simp only [hf]; rw [Nat.add_sub_cancel' hmn, Nat.add_zero]
      _ = ∑ i ∈ Finset.range (n - m), (f (i + 1) - f i) := (Finset.sum_range_sub f (n - m)).symm
      _ = _ := Finset.sum_congr rfl fun i _ => hstep i
  rw [htel]
  have hgeo : ∑ i ∈ Finset.range (n - m), ((2 : ℝ)⁻¹) ^ i ≤ 2 :=
    (Summable.sum_le_tsum _ (fun i _ => by positivity)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))).trans tsum_geometric_inv_two.le
  calc |∑ i ∈ Finset.range (n - m), levyBandPath K X ν (levySlice hν (m + i)) y ω|
      ≤ ∑ i ∈ Finset.range (n - m), |levyBandPath K X ν (levySlice hν (m + i)) y ω| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (n - m), ((2 : ℝ)⁻¹) ^ (m + i) :=
        Finset.sum_le_sum fun i _ => hbound (m + i) (hm.trans (Nat.le_add_right m i)) y hy
    _ = ((2 : ℝ)⁻¹) ^ m * ∑ i ∈ Finset.range (n - m), ((2 : ℝ)⁻¹) ^ i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => pow_add _ _ _
    _ ≤ ((2 : ℝ)⁻¹) ^ m * 2 := by
        exact mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ = 2 * ((2 : ℝ)⁻¹) ^ m := by ring
private lemma uniformCauchySeqOn_annulusPath_max
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {ω : Ω} (hraw : levySmallJumpRaw hd hν ω) (T : ℕ) :
    UniformCauchySeqOn
      (fun j (t : ℝ) => levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν j)) (max t 0) ω)
      atTop (Set.Iic (T : ℝ)) := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hraw.2.2 T)
  have hbound : ∀ j, N₀ ≤ j → ∀ y ∈ Set.Icc (0 : ℝ) (T : ℝ),
      |levyBandPath K X ν (levySlice hν j) y ω| ≤ ((2 : ℝ)⁻¹) ^ j := fun j hj y hy =>
    abs_le_of_isCadlag_of_grid (isCadlag_levyBandPath_of_finite ω (fun T' => hraw.2.1 T' j))
      (fun q hq => (hN₀ j hj q hq).le) hy
  have hgeo : Tendsto (fun n : ℕ => 2 * ((2 : ℝ)⁻¹) ^ n) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num)).const_mul (2 : ℝ)
    simpa using this
  obtain ⟨N, hNε, hNN₀⟩ :=
    ((hgeo.eventually (Iio_mem_nhds hε)).and (eventually_ge_atTop N₀)).exists
  refine ⟨N, fun m hm n hn x hx => ?_⟩
  have hmax : max x 0 ∈ Set.Icc (0 : ℝ) (T : ℝ) :=
    ⟨le_max_right _ _, max_le (Set.mem_Iic.mp hx) (Nat.cast_nonneg T)⟩
  rw [Real.dist_eq]
  rcases le_total m n with hmn | hnm
  · calc |levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν m)) (max x 0) ω
            - levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν n)) (max x 0) ω|
        = |levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν n)) (max x 0) ω
            - levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν m)) (max x 0) ω| :=
          abs_sub_comm _ _
      _ ≤ 2 * ((2 : ℝ)⁻¹) ^ m :=
          abs_annulusPath_sub_le hd hν hraw T hbound (hNN₀.trans hm) hmn hmax
      _ ≤ 2 * ((2 : ℝ)⁻¹) ^ N := by
          have : ((2 : ℝ)⁻¹) ^ m ≤ ((2 : ℝ)⁻¹) ^ N :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
          linarith [this, (by positivity : (0 : ℝ) ≤ ((2 : ℝ)⁻¹) ^ N)]
      _ < ε := hNε
  · calc |levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν m)) (max x 0) ω
            - levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν n)) (max x 0) ω|
        ≤ 2 * ((2 : ℝ)⁻¹) ^ n :=
          abs_annulusPath_sub_le hd hν hraw T hbound (hNN₀.trans hn) hnm hmax
      _ ≤ 2 * ((2 : ℝ)⁻¹) ^ N := by
          have : ((2 : ℝ)⁻¹) ^ n ≤ ((2 : ℝ)⁻¹) ^ N :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
          linarith [this, (by positivity : (0 : ℝ) ≤ ((2 : ℝ)⁻¹) ^ N)]
      _ < ε := hNε
private lemma exists_tendsto_annulusPath
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {ω : Ω} (hraw : levySmallJumpRaw hd hν ω) {s : ℝ} (hs : 0 ≤ s) :
    ∃ L, Tendsto (fun j => levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν j)) s ω)
      atTop (𝓝 L) := by
  obtain ⟨T, hT⟩ := exists_nat_gt s
  have hcauchy := (uniformCauchySeqOn_annulusPath_max hd hν hraw T).cauchySeq
    (Set.mem_Iic.mpr hT.le)
  rw [max_eq_left hs] at hcauchy
  exact cauchySeq_tendsto_of_complete hcauchy
open scoped Classical in
private lemma tendsto_annulusPath_max_levySmallJumpPath
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {ω : Ω} (hω : ω ∈ levySmallJumpGoodSet hd hν) (t : ℝ) :
    Tendsto (fun j => levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν j)) (max t 0) ω)
      atTop (𝓝 (levySmallJumpPath hd hν t ω)) := by
  obtain ⟨L, hL⟩ := exists_tendsto_annulusPath hd hν
    (levySmallJumpRaw_of_mem_goodSet hd hν hω) (le_max_right t 0)
  have hval : levySmallJumpPath hd hν t ω = L := by
    simp only [levySmallJumpPath]
    rw [show (fun j => if ω ∈ levySmallJumpGoodSet hd hν
        then levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν j)) (max t 0) ω else 0)
        = fun j => levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν j)) (max t 0) ω
        from by funext j; rw [if_pos hω]]
    exact hL.limUnder_eq
  rw [hval]; exact hL
end ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace ProbabilityTheory
end ProbabilityTheory
open scoped Classical
section P2MSourceRelocation
open ProbabilityTheory
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ}
  {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω} {A : Set ℝ}
theorem solution
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν) (t : ℝ) :
    Measurable (levySmallJumpPath hd hν t) := by
  set g : ℕ → Ω → ℝ := fun j ω =>
    if ω ∈ levySmallJumpGoodSet hd hν
    then levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν j)) (max t 0) ω else 0 with hg
  have hgmeas : ∀ j, Measurable (g j) := fun j =>
    Measurable.ite (measurableSet_levySmallJumpGoodSet hd hν)
      (measurable_levyBandPath hd.measurable_count hd.measurable_point
        (measurableSet_levyAnnulus _) (max t 0)) measurable_const
  have htend : ∀ ω, Tendsto (fun j => g j ω) atTop (𝓝 (levySmallJumpPath hd hν t ω)) := by
    intro ω
    by_cases hω : ω ∈ levySmallJumpGoodSet hd hν
    · simpa only [hg, if_pos hω] using tendsto_annulusPath_max_levySmallJumpPath hd hν hω t
    · have hval : levySmallJumpPath hd hν t ω = 0 := by
        simp only [levySmallJumpPath]
        rw [show (fun j => if ω ∈ levySmallJumpGoodSet hd hν
            then levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν j)) (max t 0) ω else 0)
            = fun _ => (0 : ℝ) from by funext j; rw [if_neg hω]]
        exact tendsto_const_nhds.limUnder_eq
      simp only [hg, if_neg hω, hval]
      exact tendsto_const_nhds
  exact measurable_of_tendsto_metrizable hgmeas (tendsto_pi_nhds.mpr htend)
end P2MSourceRelocation