-- Prove2me | solution 1 for PettisIntegral.setOf_complexWeakIntegral_eq_closure_absConvexHull
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:54:27.283794+00:00
-- url     : https://prove2.me/submissions/f16000d9-4094-421e-b049-cf43eaada2a9

import Mathlib
import Definitions.Def_PettisIntegral_Basic
import Definitions.Def_PettisIntegral_ComplexMeasure
import Theorems.Thm_PettisIntegral_complexWeakIntegral_mem_smul_closure_absConvexHull
import Theorems.Thm_PettisIntegral_setOf_weakIntegral_probabilityMeasure_eq_closure_convexHull

open MeasureTheory

set_option autoImplicit false

namespace Sol_PettisIntegral_setOf_complexWeakIntegral_eq_closure_absConvexHull

open Set Filter Topology
open scoped ENNReal Pointwise

/-- A measure dominated by a finite regular measure on a Hausdorff Borel space is regular. -/
theorem regular_of_le_finite_regular {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ ν : Measure X) [IsFiniteMeasure ν]
    [ν.Regular] (h : μ ≤ ν) : μ.Regular := by
  have : IsFiniteMeasure μ := isFiniteMeasure_of_le ν h
  have : μ.InnerRegularCompactLTTop := by
    constructor
    intro A hA r hr
    have he : μ A - r ≠ 0 := ne_of_gt (tsub_pos_of_lt hr)
    obtain ⟨K, hKA, hK, hsmall⟩ :=
      hA.1.exists_isCompact_sdiff_lt (μ := ν) (measure_ne_top ν A) he
    refine ⟨K, hKA, hK, ?_⟩
    have hd : μ (A \ K) < μ A - r := lt_of_le_of_lt (h (A \ K)) hsmall
    have hsum : μ A = μ K + μ (A \ K) := by
      simpa [union_eq_right.mpr hKA] using
        (measure_add_sdiff (μ := μ) hK.measurableSet.nullMeasurableSet A).symm
    rw [lt_tsub_iff_right] at hd
    rw [hsum] at hd
    exact (ENNReal.add_lt_add_iff_right (measure_ne_top μ (A \ K))).mp
      (by simpa [add_comm] using hd)
  infer_instance

/-- Integrating a bounded complex test function against a complex density amounts to
multiplying by the density inside the Bochner integral. -/
theorem integral_withDensityᵥ_mul {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    {w g : Y → ℂ} (hw : Integrable w ν) (hg : StronglyMeasurable g)
    {C : ℝ} (hC : 0 ≤ C) (hgb : ∀ y, ‖g y‖ ≤ C) :
    (ν.withDensityᵥ w).integral g (ContinuousLinearMap.mul ℝ ℂ) = ∫ y, g y * w y ∂ν := by
  let μ := ν.withDensityᵥ w
  let B := ContinuousLinearMap.mul ℝ ℂ
  have : IsFiniteMeasure μ.variation := ⟨by
    rw [show μ.variation = _ from Measure.variation_withDensityᵥ hw,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hw.2⟩
  have hsint (s : SimpleFunc Y ℂ) : Integrable (fun y ↦ s y * w y) ν := by
    obtain ⟨M, hM⟩ := (s.finite_range.image norm).bddAbove
    exact (hw.norm.const_mul M).mono (s.stronglyMeasurable.aestronglyMeasurable.mul
      hw.aestronglyMeasurable) (ae_of_all _ fun y ↦ by
        rw [norm_mul, Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_right (hM ⟨_, mem_range_self y, rfl⟩) (norm_nonneg _)).trans
          (le_abs_self _))
  have hs (s : SimpleFunc Y ℂ) : μ.integral s B = ∫ y, s y * w y ∂ν := by
    induction s using SimpleFunc.induction with
    | const c ht =>
      rename_i t
      change μ.integral (t.indicator (fun _ ↦ c)) B = ∫ y, t.indicator (fun _ ↦ c) y * w y ∂ν
      rw [VectorMeasure.integral_indicator_const c ht, show μ t = _ from withDensityᵥ_apply hw ht]
      simp_rw [← Set.indicator_mul_left, integral_indicator ht, integral_const_mul]
      rfl
    | add h h₁ h₂ =>
      rename_i s t
      simp only [SimpleFunc.coe_add, Pi.add_apply, add_mul]
      rw [VectorMeasure.integral_add (μ := μ) (B := B) s.integrable_of_isFiniteMeasure
        t.integrable_of_isFiniteMeasure, integral_add (hsint s) (hsint t), h₁, h₂]
  let s := hg.approxBounded C
  have hb := hg.norm_approxBounded_le hC
  have hl (y : Y) := hg.tendsto_approxBounded_of_norm_le (hgb y)
  apply tendsto_nhds_unique (VectorMeasure.tendsto_integral_of_dominated_convergence
    (μ := μ) (B := B) (f := g) (fun _ ↦ C)
    (fun n ↦ (s n).stronglyMeasurable.aestronglyMeasurable) (integrable_const _)
    (fun n ↦ ae_of_all _ (hb n)) (ae_of_all _ hl))
  simp_rw [hs]
  apply tendsto_integral_of_dominated_convergence (fun y ↦ C * ‖w y‖)
    (fun n ↦ (s n).stronglyMeasurable.aestronglyMeasurable.mul hw.aestronglyMeasurable)
    (hw.norm.const_mul C)
  · exact fun n ↦ ae_of_all _ fun y ↦ by
      rw [Pi.mul_apply, norm_mul]; exact mul_le_mul_of_nonneg_right (hb n y) (norm_nonneg _)
  · exact ae_of_all _ fun y ↦ (hl y).mul_const _


noncomputable section

/-- The product of `X` with the closed unit disc of `ℂ`, with its Borel σ-algebra. -/
def DiscProd (X : Type*) : Type _ := X × Metric.closedBall (0 : ℂ) 1

section DiscProd

variable (X : Type*) [TopologicalSpace X]

instance : TopologicalSpace (DiscProd X) :=
  inferInstanceAs (TopologicalSpace (X × Metric.closedBall (0 : ℂ) 1))

instance [T2Space X] : T2Space (DiscProd X) :=
  inferInstanceAs (T2Space (X × Metric.closedBall (0 : ℂ) 1))

instance [CompactSpace X] : CompactSpace (DiscProd X) :=
  inferInstanceAs (CompactSpace (X × Metric.closedBall (0 : ℂ) 1))

instance : MeasurableSpace (DiscProd X) := borel _

instance : BorelSpace (DiscProd X) := ⟨rfl⟩

/-- The projection onto `X`. -/
def DiscProd.fst : DiscProd X → X := fun y => (show X × Metric.closedBall (0 : ℂ) 1 from y).1

/-- The disc coordinate. -/
def DiscProd.snd : DiscProd X → ℂ :=
  fun y => ((show X × Metric.closedBall (0 : ℂ) 1 from y).2 : ℂ)

theorem DiscProd.continuous_fst : Continuous (DiscProd.fst X) :=
  (_root_.continuous_fst : Continuous fun y : X × Metric.closedBall (0 : ℂ) 1 => y.1)

theorem DiscProd.continuous_snd : Continuous (DiscProd.snd X) :=
  continuous_subtype_val.comp
    (_root_.continuous_snd : Continuous fun y : X × Metric.closedBall (0 : ℂ) 1 => y.2)

omit [TopologicalSpace X] in
theorem DiscProd.norm_snd_le (y : DiscProd X) : ‖DiscProd.snd X y‖ ≤ 1 := by
  exact mem_closedBall_zero_iff.mp (show X × Metric.closedBall (0 : ℂ) 1 from y).2.property

/-- Every point of `X` together with a scalar of the unit disc. -/
def DiscProd.mk (x : X) (c : ℂ) (hc : ‖c‖ ≤ 1) : DiscProd X :=
  ((x, ⟨c, by simpa [Metric.mem_closedBall, dist_zero_right] using hc⟩) :
    X × Metric.closedBall (0 : ℂ) 1)

omit [TopologicalSpace X] in
@[simp] theorem DiscProd.fst_mk (x : X) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    DiscProd.fst X (DiscProd.mk X x c hc) = x := rfl

omit [TopologicalSpace X] in
@[simp] theorem DiscProd.snd_mk (x : X) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    DiscProd.snd X (DiscProd.mk X x c hc) = c := rfl

end DiscProd

end

open PettisIntegral

theorem toWeakCompletion_smul {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (c : ℂ) (u : E) : toWeakCompletion ℂ (c • u) = c • toWeakCompletion ℂ u := by
  funext φ
  simp [toWeakCompletion, map_smul]

/-- The values of `(x, c) ↦ c • f x` on `X × 𝔻` fill the balanced hull of `f(X) ∪ {0}` in the weak
completion. -/
theorem range_discProd_eq {E X : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [TopologicalSpace X] [Nonempty X] (f : X → E) :
    (Set.range fun y : DiscProd X => toWeakCompletion ℂ (DiscProd.snd X y • f (DiscProd.fst X y))) =
      balancedHull ℂ (insert 0 (Set.range fun x : X => toWeakCompletion ℂ (f x))) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨y, rfl⟩
    rw [mem_balancedHull_iff]
    refine ⟨DiscProd.snd X y, DiscProd.norm_snd_le X y, ?_⟩
    show toWeakCompletion ℂ (DiscProd.snd X y • f (DiscProd.fst X y)) ∈ _
    rw [toWeakCompletion_smul]
    exact Set.smul_mem_smul_set (Set.mem_insert_of_mem _ ⟨DiscProd.fst X y, rfl⟩)
  · intro v hv
    obtain ⟨c, hc, hv⟩ := mem_balancedHull_iff.mp hv
    obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.mp hv
    rcases hu with rfl | ⟨x, rfl⟩
    · refine ⟨DiscProd.mk X (Classical.arbitrary X) 0 (by simp), ?_⟩
      simp only [DiscProd.snd_mk, zero_smul, smul_zero]
      funext φ
      simp [toWeakCompletion]
    · refine ⟨DiscProd.mk X x c hc, ?_⟩
      simp only [DiscProd.snd_mk, DiscProd.fst_mk]
      rw [toWeakCompletion_smul]

/-- Mean value theorem step: a weak integral against a complex Radon measure of total variation
at most one lies in the closed absolutely convex hull. -/
theorem complexWeakIntegral_mem_hull {E X : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    [T2Space E] [TopologicalSpace X] [T2Space X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] [Nonempty X] (f : X → E) (hf : Continuous f) (μ : ComplexMeasure X)
    (hreg : μ.variation.Regular) (hmass : μ.variation Set.univ ≤ 1) :
    complexWeakIntegral μ f ∈ closure (convexHull ℝ (balancedHull ℂ
        (insert 0 (Set.range fun x : X => toWeakCompletion ℂ (f x))))) := by
  have : IsFiniteMeasure μ.variation := ⟨hmass.trans_lt ENNReal.one_lt_top⟩
  have := hreg
  have hfi : ComplexWeaklyIntegrable μ f := fun φ =>
    (φ.continuous.comp hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := complexWeakIntegral_mem_smul_closure_absConvexHull μ f hf hfi
  obtain ⟨u, hu, hEq⟩ := Set.mem_smul_set.mp h
  rw [← hEq]
  have hconv : Convex ℝ (closure (convexHull ℝ (balancedHull ℂ
      (insert 0 (Set.range fun x : X => toWeakCompletion ℂ (f x)))))) :=
    (convex_convexHull ℝ _).closure
  have h0 : (0 : StrongDual ℂ E → ℂ) ∈ closure (convexHull ℝ (balancedHull ℂ
      (insert 0 (Set.range fun x : X => toWeakCompletion ℂ (f x))))) :=
    subset_closure (subset_convexHull ℝ _ (subset_balancedHull ℂ (Set.mem_insert _ _)))
  have hu' : u ∈ closure (convexHull ℝ (balancedHull ℂ
      (insert 0 (Set.range fun x : X => toWeakCompletion ℂ (f x))))) :=
    closure_mono (convexHull_mono (balancedHull_mono (Set.subset_insert _ _))) hu
  refine hconv.smul_mem_of_zero_mem h0 hu' ⟨ENNReal.toReal_nonneg, ?_⟩
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hmass)

/-- Projecting `c dν(x, c)` to `X` gives a complex Radon measure of total variation at most one
whose weak integral is the weak integral of `(x, c) ↦ c • f x` against `ν`. -/
theorem exists_complexMeasure {E X : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (f : X → E) (hf : Continuous f) (ν : Measure (DiscProd X)) [IsProbabilityMeasure ν]
    [ν.Regular] :
    ∃ μ : ComplexMeasure X, μ.variation.Regular ∧ μ.variation Set.univ ≤ 1 ∧
      weakIntegral ℂ ν (fun y => DiscProd.snd X y • f (DiscProd.fst X y)) =
        complexWeakIntegral μ f := by
  have hq : Continuous (DiscProd.fst X) := DiscProd.continuous_fst X
  have hw : Continuous (DiscProd.snd X) := DiscProd.continuous_snd X
  have hqm : Measurable (DiscProd.fst X) := hq.measurable
  have hwi : Integrable (DiscProd.snd X) ν :=
    hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hvar : (ν.withDensityᵥ (DiscProd.snd X)).variation ≤ ν := by
    rw [show (ν.withDensityᵥ (DiscProd.snd X)).variation = _ from
      Measure.variation_withDensityᵥ hwi]
    refine (withDensity_mono (g := 1) (ae_of_all _ fun y ↦ ?_)).trans_eq withDensity_one
    rw [Pi.one_apply, ← ofReal_norm]
    exact ENNReal.ofReal_le_one.mpr (DiscProd.norm_snd_le X y)
  have hdom : ((ν.withDensityᵥ (DiscProd.snd X)).map (DiscProd.fst X)).variation ≤
      ν.map (DiscProd.fst X) :=
    VectorMeasure.variation_map_le.trans (Measure.map_mono hvar hqm)
  have : (ν.map (DiscProd.fst X)).InnerRegularCompactLTTop :=
    Measure.InnerRegularCompactLTTop.map_of_continuous hq
  have : (ν.map (DiscProd.fst X)).Regular := inferInstance
  have : IsFiniteMeasure (ν.withDensityᵥ (DiscProd.snd X)).variation :=
    isFiniteMeasure_of_le ν hvar
  refine ⟨(ν.withDensityᵥ (DiscProd.snd X)).map (DiscProd.fst X),
    regular_of_le_finite_regular _ (ν.map (DiscProd.fst X)) hdom, ?_, ?_⟩
  · calc _ ≤ ν.map (DiscProd.fst X) Set.univ := hdom Set.univ
      _ = 1 := by
        rw [Measure.map_apply hqm MeasurableSet.univ, Set.preimage_univ, measure_univ]
  · funext φ
    rw [weakIntegral_apply, complexWeakIntegral_apply]
    let t := BoundedContinuousFunction.mkOfCompact
      (⟨fun x ↦ φ (f x), φ.continuous.comp hf⟩ : C(X, ℂ))
    have ht : Continuous fun x => φ (f x) := φ.continuous.comp hf
    rw [VectorMeasure.integral_map hqm ht.aestronglyMeasurable
      (show Integrable ((fun x => φ (f x)) ∘ DiscProd.fst X)
          (ν.withDensityᵥ (DiscProd.snd X)).variation from
        (ht.comp hq).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    rw [integral_withDensityᵥ_mul (g := fun y => φ (f (DiscProd.fst X y))) hwi
      (ht.comp hq).stronglyMeasurable (norm_nonneg t)
      (fun y ↦ t.norm_coe_le_norm (DiscProd.fst X y))]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [map_smul, smul_eq_mul]
    ring

end Sol_PettisIntegral_setOf_complexWeakIntegral_eq_closure_absConvexHull

open PettisIntegral Sol_PettisIntegral_setOf_complexWeakIntegral_eq_closure_absConvexHull

theorem solution {E X : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (f : X → E) (hf : Continuous f) :
    {a : StrongDual ℂ E → ℂ | ∃ μ : ComplexMeasure X, μ.variation.Regular ∧
        μ.variation Set.univ ≤ 1 ∧ a = complexWeakIntegral μ f} =
      closure (convexHull ℝ (balancedHull ℂ
        (insert 0 (Set.range fun x : X => toWeakCompletion ℂ (f x))))) ∧
    IsCompact (closure (convexHull ℝ (balancedHull ℂ
        (insert 0 (Set.range fun x : X => toWeakCompletion ℂ (f x)))))) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · -- Empty space: both sides are `{0}`.
    have h1 : (Set.range fun x : X => toWeakCompletion ℂ (f x)) = ∅ := Set.range_eq_empty _
    have h2 : balancedHull ℂ ({0} : Set (StrongDual ℂ E → ℂ)) = {0} := by
      apply Set.Subset.antisymm
      · intro x hx
        rw [mem_balancedHull_iff] at hx
        obtain ⟨r, -, hr⟩ := hx
        simpa using hr
      · exact subset_balancedHull ℂ
    have hC : closure (convexHull ℝ (balancedHull ℂ
        (insert 0 (Set.range fun x : X => toWeakCompletion ℂ (f x))))) =
          ({0} : Set (StrongDual ℂ E → ℂ)) := by
      rw [h1, show (insert (0 : StrongDual ℂ E → ℂ) (∅ : Set (StrongDual ℂ E → ℂ))) = {0} from
        by simp, h2, convexHull_singleton, closure_singleton]
    rw [hC]
    refine ⟨?_, isCompact_singleton⟩
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨μ, -, -, rfl⟩
      funext φ
      simp [complexWeakIntegral, VectorMeasure.integral_of_isEmpty]
    · rintro rfl
      refine ⟨0, ?_, ?_, ?_⟩
      · rw [VectorMeasure.variation_zero]; infer_instance
      · simp [VectorMeasure.variation_zero]
      · funext φ
        simp [complexWeakIntegral, VectorMeasure.integral_of_isEmpty]
  · obtain ⟨h1, h2⟩ := setOf_weakIntegral_probabilityMeasure_eq_closure_convexHull (𝕜 := ℂ)
      (fun y : DiscProd X => DiscProd.snd X y • f (DiscProd.fst X y))
      ((DiscProd.continuous_snd X).smul (hf.comp (DiscProd.continuous_fst X)))
    rw [range_discProd_eq f] at h1 h2
    refine ⟨Set.Subset.antisymm ?_ ?_, h2⟩
    · rintro a ⟨μ, hreg, hmass, rfl⟩
      exact complexWeakIntegral_mem_hull f hf μ hreg hmass
    · intro a ha
      rw [← h1] at ha
      obtain ⟨ν, hν1, hν2, rfl⟩ := ha
      obtain ⟨μ, hμ1, hμ2, hμ3⟩ := exists_complexMeasure f hf ν
      exact ⟨μ, hμ1, hμ2, hμ3⟩
