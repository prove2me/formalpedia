-- Prove2me | solution 1 for PettisIntegral.setOf_weakIntegral_probabilityMeasure_eq_closure_convexHull
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:06:03.846451+00:00
-- url     : https://prove2.me/submissions/0d06050d-2e01-40c4-804c-2ed172a89892

import Mathlib
import Definitions.Def_PettisIntegral_Basic

open MeasureTheory

set_option autoImplicit false

namespace Sol_PettisIntegral_setOf_weakIntegral_probabilityMeasure_eq_closure_convexHull

/-- A point `g` of a product space lies in the closure of a set `A` as soon as, for every finite
set `I` of coordinates, the restriction of `g` to `I` lies in the closure of the set of
restrictions to `I` of the elements of `A`. -/
theorem mem_closure_pi_of_forall_finset {ι : Type*} {Y : ι → Type*}
    [∀ i, TopologicalSpace (Y i)] {A : Set (∀ i, Y i)} {g : ∀ i, Y i}
    (h : ∀ I : Finset ι, (fun i : I => g i.1) ∈
      closure ((fun (a : ∀ i, Y i) (i : I) => a i.1) '' A)) :
    g ∈ closure A := by
  rw [mem_closure_iff]
  intro U hU hgU
  obtain ⟨I, u, hu, huU⟩ := isOpen_pi_iff.mp hU g hgU
  have hV : IsOpen {b : ∀ i : I, Y i.1 | ∀ i : I, b i ∈ u i.1} := by
    have hset : {b : ∀ i : I, Y i.1 | ∀ i : I, b i ∈ u i.1} =
        ⋂ i : I, (fun b : ∀ i : I, Y i.1 => b i) ⁻¹' u i.1 := by
      ext b
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
    rw [hset]
    exact isOpen_iInter_of_finite fun i => (hu i.1 i.2).1.preimage (continuous_apply i)
  obtain ⟨b, hbV, a, haA, rfl⟩ :=
    mem_closure_iff.mp (h I) _ hV (fun i => (hu i.1 i.2).2)
  exact ⟨a, huU (fun i hi => hbV ⟨i, hi⟩), haA⟩

end Sol_PettisIntegral_setOf_weakIntegral_probabilityMeasure_eq_closure_convexHull

open PettisIntegral Sol_PettisIntegral_setOf_weakIntegral_probabilityMeasure_eq_closure_convexHull

theorem solution {𝕜 E X : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E]
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (f : X → E) (hf : Continuous f) :
    {a : StrongDual 𝕜 E → 𝕜 | ∃ μ : Measure X, IsProbabilityMeasure μ ∧ μ.Regular ∧
        a = weakIntegral 𝕜 μ f} =
      closure (convexHull ℝ (Set.range fun x : X => toWeakCompletion 𝕜 (f x))) ∧
    IsCompact (closure (convexHull ℝ (Set.range fun x : X => toWeakCompletion 𝕜 (f x)))) := by
  -- the scalar functions `φ ∘ f`, as bounded continuous functions on the compact space `X`
  let g : StrongDual 𝕜 E → BoundedContinuousFunction X 𝕜 := fun φ =>
    BoundedContinuousFunction.mkOfCompact ⟨fun x => φ (f x), φ.continuous.comp hf⟩
  have hint : ∀ (μ : Measure X) [IsFiniteMeasure μ] (φ : StrongDual 𝕜 E),
      Integrable (fun x => φ (f x)) μ := fun μ _ φ => (g φ).integrable μ
  -- the weak integral as a map on the space of all Borel probability measures
  let Φ : ProbabilityMeasure X → (StrongDual 𝕜 E → 𝕜) :=
    fun μ => weakIntegral 𝕜 (μ : Measure X) f
  have hΦ : Continuous Φ := by
    refine continuous_pi fun φ => ?_
    rw [continuous_iff_continuousAt]
    intro μ
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto 𝕜).1
      Filter.tendsto_id (g φ)
  have hcomp : IsCompact (Set.range Φ) := isCompact_range hΦ
  have hclosed : IsClosed (Set.range Φ) := hcomp.isClosed
  -- Dirac measures: the range of `Φ` contains the image of `f`
  have hrange : (Set.range fun x : X => toWeakCompletion 𝕜 (f x)) ⊆ Set.range Φ := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨Measure.dirac x, Measure.dirac.isProbabilityMeasure⟩, ?_⟩
    funext φ
    simp only [Φ, weakIntegral_apply, ProbabilityMeasure.coe_mk, toWeakCompletion_apply]
    exact integral_dirac _ x
  -- convex combinations of probability measures: the range of `Φ` is convex
  have hconv : Convex ℝ (Set.range Φ) := by
    rintro _ ⟨μ, rfl⟩ _ ⟨ν, rfl⟩ a b ha hb hab
    have hprob : IsProbabilityMeasure
        (ENNReal.ofReal a • (μ : Measure X) + ENNReal.ofReal b • (ν : Measure X)) := by
      constructor
      simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ,
        smul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one]
    refine ⟨⟨_, hprob⟩, ?_⟩
    funext φ
    simp only [Φ, weakIntegral_apply, ProbabilityMeasure.coe_mk, Pi.add_apply, Pi.smul_apply]
    rw [integral_add_measure ((hint _ φ).smul_measure ENNReal.ofReal_ne_top)
      ((hint _ φ).smul_measure ENNReal.ofReal_ne_top), integral_smul_measure,
      integral_smul_measure, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]
  have hC_sub : closure (convexHull ℝ (Set.range fun x : X => toWeakCompletion 𝕜 (f x))) ⊆
      Set.range Φ := closure_minimal (convexHull_min hrange hconv) hclosed
  -- mean value theorem: the range of `Φ` is contained in the closed convex hull
  have hsub_C : Set.range Φ ⊆
      closure (convexHull ℝ (Set.range fun x : X => toWeakCompletion 𝕜 (f x))) := by
    rintro _ ⟨μ, rfl⟩
    refine mem_closure_pi_of_forall_finset fun I => ?_
    let F : X → (I → 𝕜) := fun x i => i.1 (f x)
    have hFi : Integrable F (μ : Measure X) := Integrable.of_eval fun i => hint _ i.1
    have hmem : (∫ x, F x ∂(μ : Measure X)) ∈ closure (convexHull ℝ (Set.range F)) :=
      (convex_convexHull ℝ (Set.range F)).closure.integral_mem isClosed_closure
        (Filter.Eventually.of_forall fun x =>
          subset_closure (subset_convexHull ℝ _ (Set.mem_range_self x))) hFi
    have hval : (∫ x, F x ∂(μ : Measure X)) = fun i : I => Φ μ i.1 := by
      funext i
      exact eval_integral (f := F) (fun j : I => hint _ j.1) i
    rw [← hval]
    refine closure_mono ?_ hmem
    let R : (StrongDual 𝕜 E → 𝕜) →ₗ[ℝ] (I → 𝕜) :=
      { toFun := fun a i => a i.1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hrangeF : Set.range F = R '' (Set.range fun x : X => toWeakCompletion 𝕜 (f x)) := by
      rw [← Set.range_comp]
      rfl
    rw [hrangeF, ← R.image_convexHull]
    exact subset_rfl
  have hC_eq : closure (convexHull ℝ (Set.range fun x : X => toWeakCompletion 𝕜 (f x))) =
      Set.range Φ := Set.Subset.antisymm hC_sub hsub_C
  -- Riesz–Markov–Kakutani: every Borel probability measure can be replaced by a regular one
  have hreg : Set.range Φ ⊆ {a : StrongDual 𝕜 E → 𝕜 | ∃ μ : Measure X,
      IsProbabilityMeasure μ ∧ μ.Regular ∧ a = weakIntegral 𝕜 μ f} := by
    rintro _ ⟨μ, rfl⟩
    obtain ⟨ν, hνreg, hνfin, hν⟩ := Measure.exists_regular_eq_of_compactSpace (μ : Measure X)
    have hνprob : IsProbabilityMeasure ν := by
      constructor
      have h1 := hν (BoundedContinuousFunction.const X 1)
      simp only [BoundedContinuousFunction.const_apply, integral_const, smul_eq_mul, mul_one,
        probReal_univ] at h1
      have h2 : (ν Set.univ).toReal = 1 := h1.symm
      exact (ENNReal.toReal_eq_one_iff _).mp h2
    refine ⟨ν, hνprob, hνreg, ?_⟩
    funext φ
    simp only [Φ, weakIntegral_apply]
    apply RCLike.ext
    · rw [← integral_re (hint _ φ), ← integral_re (hint _ φ)]
      exact hν (BoundedContinuousFunction.mkOfCompact
        ⟨fun x => RCLike.re (φ (f x)), RCLike.continuous_re.comp (φ.continuous.comp hf)⟩)
    · rw [← integral_im (hint _ φ), ← integral_im (hint _ φ)]
      exact hν (BoundedContinuousFunction.mkOfCompact
        ⟨fun x => RCLike.im (φ (f x)), RCLike.continuous_im.comp (φ.continuous.comp hf)⟩)
  refine ⟨?_, hC_eq ▸ hcomp⟩
  rw [hC_eq]
  refine Set.Subset.antisymm ?_ hreg
  rintro _ ⟨μ, hμ, -, rfl⟩
  exact ⟨⟨μ, hμ⟩, rfl⟩
