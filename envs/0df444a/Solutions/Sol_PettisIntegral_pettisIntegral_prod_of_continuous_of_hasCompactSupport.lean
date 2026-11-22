-- Prove2me | solution 1 for PettisIntegral.pettisIntegral_prod_of_continuous_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:37:00.871843+00:00
-- url     : https://prove2.me/submissions/f1528a99-bbcd-4185-995b-e2808aca3c16

import Mathlib
import Definitions.Def_PettisIntegral_Basic

open MeasureTheory

set_option autoImplicit false

namespace Sol_PettisIntegral_pettisIntegral_prod_of_continuous_of_hasCompactSupport

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

/-- Pettis integrability for a finite measure on an arbitrary measurable space: a weakly
integrable function with totally bounded range, with values in a quasi-complete locally convex
space, is Pettis integrable. -/
theorem pettisIntegrable_of_totallyBounded {𝕜 E Z : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
    [PolynormableSpace 𝕜 E] [QuasiCompleteSpace 𝕜 E] [MeasurableSpace Z]
    (μ : Measure Z) [IsFiniteMeasure μ] (f : Z → E) (hfi : WeaklyIntegrable 𝕜 μ f)
    (hK : TotallyBounded (Set.range f)) :
    PettisIntegrable 𝕜 μ f := by
  by_cases hμ : μ = 0
  · -- the zero measure: the integral is `0`
    refine ⟨0, hfi, fun φ => ?_⟩
    rw [hμ, integral_zero_measure, map_zero]
  -- the underlying real locally convex structure of `E`
  let _ : Module ℝ E := .restrictScalars ℝ 𝕜 E
  have hST : IsScalarTower ℝ 𝕜 E := .restrictScalars ℝ 𝕜 E
  have hCS : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  have hLC : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms 𝕜 E).toLocallyConvexSpace
  -- the closed convex hull `C` of the totally bounded set `f(Z)` is compact
  have hCc : IsCompact (closure (convexHull ℝ (Set.range f))) :=
    isCompact_closure_of_totallyBounded_quasiComplete (𝕜 := 𝕜) hK.convexHull
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
  have hsub : closure (convexHull ℝ (Set.range fun x : Z => toWeakCompletion 𝕜 (f x))) ⊆
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

/-- The same for an arbitrary measure, when the function vanishes outside a measurable set of
finite measure. -/
theorem pettisIntegrable_of_forall_notMem_eq_zero {𝕜 E Z : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
    [PolynormableSpace 𝕜 E] [QuasiCompleteSpace 𝕜 E] [MeasurableSpace Z]
    (μ : Measure Z) (S : Set Z) (hμS : μ S ≠ ⊤) (f : Z → E)
    (hfS : ∀ z, z ∉ S → f z = 0) (hfi : WeaklyIntegrable 𝕜 μ f)
    (hK : TotallyBounded (Set.range f)) :
    PettisIntegrable 𝕜 μ f := by
  have : IsFiniteMeasure (μ.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hμS⟩
  obtain ⟨a, -, ha⟩ :=
    pettisIntegrable_of_totallyBounded (𝕜 := 𝕜) (μ.restrict S) f (fun φ => (hfi φ).restrict) hK
  refine ⟨a, hfi, fun φ => ?_⟩
  rw [ha φ]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by rw [hfS z hz, map_zero]

/-- The Pettis integral of a Pettis integrable function represents its weak integral. -/
theorem apply_pettisIntegral {𝕜 E X : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [MeasurableSpace X] {μ : Measure X} {g : X → E}
    (h : PettisIntegrable 𝕜 μ g) (φ : StrongDual 𝕜 E) :
    φ (pettisIntegral 𝕜 μ g) = ∫ x, φ (g x) ∂μ := by
  have hspec : HasPettisIntegral 𝕜 μ g (Classical.choose h) := Classical.choose_spec h
  have heq : pettisIntegral 𝕜 μ g = Classical.choose h := by
    unfold pettisIntegral
    exact dif_pos h
  rw [heq]
  exact hspec.2 φ

/-- Continuous linear forms separate the points of a Hausdorff locally convex space. -/
theorem eq_of_forall_dual_eq {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E]
    [T2Space E] {a b : E} (h : ∀ φ : StrongDual 𝕜 E, φ a = φ b) : a = b := by
  by_contra hab
  let _ : Module ℝ E := .restrictScalars ℝ 𝕜 E
  have : IsScalarTower ℝ 𝕜 E := .restrictScalars ℝ 𝕜 E
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  have : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms 𝕜 E).toLocallyConvexSpace
  obtain ⟨φ, hφ⟩ := RCLike.geometric_hahn_banach_point_point (𝕜 := 𝕜) hab
  rw [h φ] at hφ
  exact lt_irrefl _ hφ

end Sol_PettisIntegral_pettisIntegral_prod_of_continuous_of_hasCompactSupport

open PettisIntegral Sol_PettisIntegral_pettisIntegral_prod_of_continuous_of_hasCompactSupport

theorem solution {𝕜 E X Y : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
    [PolynormableSpace 𝕜 E] [T2Space E] [QuasiCompleteSpace 𝕜 E]
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SigmaCompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y] [SigmaCompactSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) [μ.Regular] (ν : Measure Y) [ν.Regular]
    (f : X × Y → E) (hf : Continuous f) (hc : HasCompactSupport f) :
    (∀ x : X, PettisIntegrable 𝕜 ν (fun y => f (x, y))) ∧
    (∀ y : Y, PettisIntegrable 𝕜 μ (fun x => f (x, y))) ∧
    PettisIntegrable 𝕜 (μ.prod ν) f ∧
    PettisIntegrable 𝕜 μ (fun x => pettisIntegral 𝕜 ν (fun y => f (x, y))) ∧
    PettisIntegrable 𝕜 ν (fun y => pettisIntegral 𝕜 μ (fun x => f (x, y))) ∧
    pettisIntegral 𝕜 μ (fun x => pettisIntegral 𝕜 ν (fun y => f (x, y))) =
      pettisIntegral 𝕜 (μ.prod ν) f ∧
    pettisIntegral 𝕜 ν (fun y => pettisIntegral 𝕜 μ (fun x => f (x, y))) =
      pettisIntegral 𝕜 (μ.prod ν) f := by
  -- the projections `K_X`, `K_Y` of the support of `f`: compact sets of finite measure
  set KX : Set X := Prod.fst '' tsupport f with hKX
  set KY : Set Y := Prod.snd '' tsupport f with hKY
  have hKXc : IsCompact KX := hc.image continuous_fst
  have hKYc : IsCompact KY := hc.image continuous_snd
  have hμK : μ KX ≠ ⊤ := hKXc.measure_lt_top.ne
  have hνK : ν KY ≠ ⊤ := hKYc.measure_lt_top.ne
  have hzero : ∀ p : X × Y, p ∉ KX ×ˢ KY → f p = 0 := by
    intro p hp
    refine image_eq_zero_of_notMem_tsupport fun hpt => hp ?_
    exact ⟨⟨p, hpt, rfl⟩, ⟨p, hpt, rfl⟩⟩
  have hzeroY : ∀ x : X, ∀ y : Y, y ∉ KY → f (x, y) = 0 := fun x y hy =>
    hzero (x, y) fun h => hy h.2
  have hzeroX : ∀ y : Y, ∀ x : X, x ∉ KX → f (x, y) = 0 := fun y x hx =>
    hzero (x, y) fun h => hx h.1
  -- the range of `f` is compact, hence totally bounded
  have hTB : TotallyBounded (Set.range f) := (hc.isCompact_range hf).totallyBounded
  have hTBY : ∀ x : X, TotallyBounded (Set.range fun y : Y => f (x, y)) := fun x =>
    hTB.subset (Set.range_subset_iff.mpr fun y => Set.mem_range_self _)
  have hTBX : ∀ y : Y, TotallyBounded (Set.range fun x : X => f (x, y)) := fun y =>
    hTB.subset (Set.range_subset_iff.mpr fun x => Set.mem_range_self _)
  -- weak integrability of the partial functions
  have hWY : ∀ x : X, WeaklyIntegrable 𝕜 ν (fun y => f (x, y)) := by
    intro x φ
    have hcont : Continuous fun y : Y => φ (f (x, y)) :=
      φ.continuous.comp (hf.comp (Continuous.prodMk_right x))
    refine hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro hKYc fun y hy => ?_)
    rw [hzeroY x y hy, map_zero]
  have hWX : ∀ y : Y, WeaklyIntegrable 𝕜 μ (fun x => f (x, y)) := by
    intro y φ
    have hcont : Continuous fun x : X => φ (f (x, y)) :=
      φ.continuous.comp (hf.comp (Continuous.prodMk_left y))
    refine hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro hKXc fun x hx => ?_)
    rw [hzeroX y x hx, map_zero]
  -- weak integrability of `f` for the product measure
  have hW : WeaklyIntegrable 𝕜 (μ.prod ν) f := by
    intro φ
    have hcont : Continuous fun p : X × Y => φ (f p) := φ.continuous.comp hf
    have hcs : HasCompactSupport fun p : X × Y => φ (f p) := hc.comp_left (map_zero φ)
    have hsupp : Function.support (fun p : X × Y => φ (f p)) ⊆ KX ×ˢ KY := by
      intro p hp
      by_contra hnot
      exact hp (show φ (f p) = 0 by rw [hzero p hnot, map_zero])
    refine (integrableOn_iff_integrable_of_support_subset hsupp).mp ?_
    obtain ⟨C, hC⟩ : ∃ C, ∀ p, ‖φ (f p)‖ ≤ C := hcont.bounded_above_of_compact_support hcs
    refine Measure.integrableOn_of_bounded (M := C) ?_
      (hcs.stronglyMeasurable_of_prod hcont).aestronglyMeasurable (Filter.Eventually.of_forall hC)
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top hμK hνK
  -- Pettis integrability of the partial functions and of `f`
  have hPY : ∀ x : X, PettisIntegrable 𝕜 ν (fun y => f (x, y)) := fun x =>
    pettisIntegrable_of_forall_notMem_eq_zero ν KY hνK _ (hzeroY x) (hWY x) (hTBY x)
  have hPX : ∀ y : Y, PettisIntegrable 𝕜 μ (fun x => f (x, y)) := fun y =>
    pettisIntegrable_of_forall_notMem_eq_zero μ KX hμK _ (hzeroX y) (hWX y) (hTBX y)
  have hP : PettisIntegrable 𝕜 (μ.prod ν) f := by
    refine pettisIntegrable_of_forall_notMem_eq_zero (μ.prod ν) (KX ×ˢ KY) ?_ f hzero hW hTB
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top hμK hνK
  -- scalar Fubini for each continuous linear form
  set a : E := pettisIntegral 𝕜 (μ.prod ν) f with ha
  have hgX : ∀ φ : StrongDual 𝕜 E,
      (fun x => φ (pettisIntegral 𝕜 ν (fun y => f (x, y)))) =
        fun x => ∫ y, φ (f (x, y)) ∂ν := fun φ =>
    funext fun x => apply_pettisIntegral (hPY x) φ
  have hgY : ∀ φ : StrongDual 𝕜 E,
      (fun y => φ (pettisIntegral 𝕜 μ (fun x => f (x, y)))) =
        fun y => ∫ x, φ (f (x, y)) ∂μ := fun φ =>
    funext fun y => apply_pettisIntegral (hPX y) φ
  have hHX : HasPettisIntegral 𝕜 μ (fun x => pettisIntegral 𝕜 ν (fun y => f (x, y))) a := by
    refine ⟨fun φ => ?_, fun φ => ?_⟩
    · rw [hgX φ]
      exact (hW φ).integral_prod_left
    · rw [ha, apply_pettisIntegral hP φ, hgX φ]
      exact integral_prod _ (hW φ)
  have hHY : HasPettisIntegral 𝕜 ν (fun y => pettisIntegral 𝕜 μ (fun x => f (x, y))) a := by
    refine ⟨fun φ => ?_, fun φ => ?_⟩
    · rw [hgY φ]
      exact (hW φ).integral_prod_right
    · rw [ha, apply_pettisIntegral hP φ, hgY φ]
      exact integral_prod_symm _ (hW φ)
  refine ⟨hPY, hPX, hP, ⟨a, hHX⟩, ⟨a, hHY⟩, ?_, ?_⟩
  · refine eq_of_forall_dual_eq (𝕜 := 𝕜) fun φ => ?_
    rw [apply_pettisIntegral ⟨a, hHX⟩ φ, hHX.2 φ]
  · refine eq_of_forall_dual_eq (𝕜 := 𝕜) fun φ => ?_
    rw [apply_pettisIntegral ⟨a, hHY⟩ φ, hHY.2 φ]
