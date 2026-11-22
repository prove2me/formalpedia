-- Prove2me | solution 1 for PettisIntegral.pettisIntegrable_of_continuous_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:10:46.447455+00:00
-- url     : https://prove2.me/submissions/bf4493b0-7d6b-4d18-8077-a11427da07bb

import Mathlib
import Definitions.Def_PettisIntegral_Basic

open MeasureTheory

set_option autoImplicit false

namespace Sol_PettisIntegral_pettisIntegrable_of_continuous_of_hasCompactSupport

open PettisIntegral

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

/-- Mean-value theorem in the weak completion: for a nonzero finite measure `μ` and a weakly
integrable function `f`, the normalized weak integral `μ(X)⁻¹ • ∫ f dμ` lies in the closure, for
the topology of pointwise convergence on the dual, of the convex hull of the image of `f`. -/
theorem inv_smul_weakIntegral_mem_closure_convexHull {𝕜 E X : Type*} [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : μ ≠ 0) (f : X → E) (hfi : WeaklyIntegrable 𝕜 μ f) :
    (μ Set.univ).toReal⁻¹ • weakIntegral 𝕜 μ f ∈
      closure (convexHull ℝ (Set.range fun x : X => toWeakCompletion 𝕜 (f x))) := by
  have hne : NeZero μ := ⟨hμ⟩
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

end Sol_PettisIntegral_pettisIntegrable_of_continuous_of_hasCompactSupport

open PettisIntegral Sol_PettisIntegral_pettisIntegrable_of_continuous_of_hasCompactSupport

theorem solution {𝕜 E X : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
    [PolynormableSpace 𝕜 E] [T2Space E] [QuasiCompleteSpace 𝕜 E]
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular] (f : X → E) (hf : Continuous f)
    (hc : HasCompactSupport f) :
    PettisIntegrable 𝕜 μ f := by
  -- `f` is weakly integrable: `φ ∘ f` is continuous with compact support
  have hfi : WeaklyIntegrable 𝕜 μ f := fun φ =>
    (φ.continuous.comp hf).integrable_of_hasCompactSupport (hc.comp_left (map_zero φ))
  by_cases hμ : μ = 0
  · -- the zero measure: the integral is `0`
    refine ⟨0, hfi, fun φ => ?_⟩
    rw [hμ, integral_zero_measure, map_zero]
  -- the underlying real locally convex structure of `E`
  let _ : Module ℝ E := .restrictScalars ℝ 𝕜 E
  have hST : IsScalarTower ℝ 𝕜 E := .restrictScalars ℝ 𝕜 E
  have hCS : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  have hLC : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms 𝕜 E).toLocallyConvexSpace
  -- the closed convex hull `C` of the compact set `f(X)` is compact
  have hKc : IsCompact (Set.range f) := hc.isCompact_range hf
  have hCc : IsCompact (closure (convexHull ℝ (Set.range f))) :=
    isCompact_closure_of_totallyBounded_quasiComplete (𝕜 := 𝕜) hKc.totallyBounded.convexHull
  have hCconv : Convex ℝ (closure (convexHull ℝ (Set.range f))) :=
    (convex_convexHull ℝ (Set.range f)).closure
  -- the canonical map into the weak completion, as a continuous `ℝ`-linear map
  let L : E →ₗ[ℝ] (StrongDual 𝕜 E → 𝕜) :=
    { toFun := toWeakCompletion 𝕜
      map_add' := fun u v => funext fun φ => map_add φ u v
      map_smul' := fun r u => funext fun φ => φ.map_smul_of_tower r u }
  have hLcont : Continuous L := continuous_pi fun φ => φ.continuous
  -- the image of `C` is compact, hence closed, and convex
  have hLCc : IsCompact (L '' closure (convexHull ℝ (Set.range f))) := hCc.image hLcont
  have hLCconv : Convex ℝ (L '' closure (convexHull ℝ (Set.range f))) := hCconv.linear_image L
  have hsub : closure (convexHull ℝ (Set.range fun x : X => toWeakCompletion 𝕜 (f x))) ⊆
      L '' closure (convexHull ℝ (Set.range f)) := by
    refine closure_minimal (convexHull_min ?_ hLCconv) hLCc.isClosed
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, subset_closure (subset_convexHull ℝ _ (Set.mem_range_self x)), rfl⟩
  -- the normalized weak integral is represented by a point `c` of `C`
  obtain ⟨c, -, hcW⟩ := hsub (inv_smul_weakIntegral_mem_closure_convexHull μ hμ f hfi)
  have hm : (μ Set.univ).toReal ≠ 0 := by
    refine (ENNReal.toReal_pos ?_ (measure_ne_top μ Set.univ)).ne'
    exact fun h => hμ (Measure.measure_univ_eq_zero.mp h)
  refine ⟨(μ Set.univ).toReal • c, hfi, fun φ => ?_⟩
  have h1 : φ c = (μ Set.univ).toReal⁻¹ • ∫ x, φ (f x) ∂μ := congrFun hcW φ
  rw [φ.map_smul_of_tower, h1, smul_inv_smul₀ hm]
