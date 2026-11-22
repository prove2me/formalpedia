-- Prove2me | solution 1 for PettisIntegral.weakIntegral_mem_smul_closure_convexHull
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T11:59:29.956989+00:00
-- url     : https://prove2.me/submissions/e29c0b0f-d93c-4a5d-ae52-77aa9f9ed6f8

import Mathlib
import Definitions.Def_PettisIntegral_Basic

open MeasureTheory
open scoped Pointwise

set_option autoImplicit false

namespace Sol_PettisIntegral_weakIntegral_mem_smul_closure_convexHull

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

end Sol_PettisIntegral_weakIntegral_mem_smul_closure_convexHull

open PettisIntegral Sol_PettisIntegral_weakIntegral_mem_smul_closure_convexHull

theorem solution {𝕜 E X : Type*} [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [PolynormableSpace 𝕜 E] [T2Space E]
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [Nonempty X] (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular] (f : X → E) (hf : Continuous f)
    (hfi : WeaklyIntegrable 𝕜 μ f) :
    weakIntegral 𝕜 μ f ∈
      (μ Set.univ).toReal •
        closure (convexHull ℝ (Set.range fun x : X => toWeakCompletion 𝕜 (f x))) := by
  have _ := hf
  by_cases hμ : μ = 0
  · -- the zero measure: both sides reduce to `0`
    have hw : weakIntegral 𝕜 μ f = 0 := by
      funext φ
      simp [weakIntegral, hμ]
    have hm0 : (μ Set.univ).toReal = 0 := by simp [hμ]
    have hne : (closure (convexHull ℝ
        (Set.range fun x : X => toWeakCompletion 𝕜 (f x)))).Nonempty := by
      obtain ⟨x⟩ := ‹Nonempty X›
      exact ⟨_, subset_closure (subset_convexHull ℝ _ (Set.mem_range_self x))⟩
    rw [hw, hm0, Set.zero_smul_set hne]
    exact Set.mem_zero.mpr rfl
  · have hne : NeZero μ := ⟨hμ⟩
    have hm : (μ Set.univ).toReal ≠ 0 := by
      refine (ENNReal.toReal_pos ?_ (measure_ne_top μ Set.univ)).ne'
      exact fun h => hμ (Measure.measure_univ_eq_zero.mp h)
    refine Set.mem_smul_set.mpr
      ⟨(μ Set.univ).toReal⁻¹ • weakIntegral 𝕜 μ f, ?_, smul_inv_smul₀ hm _⟩
    refine mem_closure_pi_of_forall_finset fun I => ?_
    -- the finitely many coordinates `φ ∈ I` of `f`
    let F : X → (I → 𝕜) := fun x i => i.1 (f x)
    have hFi : Integrable F μ := Integrable.of_eval fun i => hfi i.1
    -- finite-dimensional mean value theorem
    have hmem : (⨍ x, F x ∂μ) ∈ closure (convexHull ℝ (Set.range F)) :=
      (convex_convexHull ℝ (Set.range F)).closure.average_mem isClosed_closure
        (Filter.Eventually.of_forall fun x =>
          subset_closure (subset_convexHull ℝ _ (Set.mem_range_self x))) hFi
    have havg : (⨍ x, F x ∂μ) =
        fun i : I => ((μ Set.univ).toReal⁻¹ • weakIntegral 𝕜 μ f) i.1 := by
      rw [average_eq]
      funext i
      have hev : (∫ x, F x ∂μ) i = ∫ x, i.1 (f x) ∂μ :=
        eval_integral (f := F) (fun j : I => hfi j.1) i
      rw [Pi.smul_apply, Pi.smul_apply, hev]
      rfl
    rw [← havg]
    refine closure_mono ?_ hmem
    -- restriction to the coordinates in `I`, as an `ℝ`-linear map
    let R : (StrongDual 𝕜 E → 𝕜) →ₗ[ℝ] (I → 𝕜) :=
      { toFun := fun a i => a i.1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hrange : Set.range F = R '' (Set.range fun x : X => toWeakCompletion 𝕜 (f x)) := by
      rw [← Set.range_comp]
      rfl
    rw [hrange, ← R.image_convexHull]
    exact subset_rfl
