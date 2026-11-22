-- Prove2me | solution 1 for PettisIntegral.complexWeakIntegral_mem_smul_closure_absConvexHull
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:40:13.035429+00:00
-- url     : https://prove2.me/submissions/ff394707-af3a-484c-b1e4-e927a4431b37

import Mathlib
import Definitions.Def_PettisIntegral_Basic
import Definitions.Def_PettisIntegral_ComplexMeasure

open MeasureTheory
open scoped Pointwise

set_option autoImplicit false

namespace Sol_PettisIntegral_complexWeakIntegral_mem_smul_closure_absConvexHull

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

variable {X : Type*} [MeasurableSpace X]

/-- The scalar integral against a complex measure is `ℂ`-homogeneous. -/
theorem integral_const_mul (μ : ComplexMeasure X) (a : ℂ) (g : X → ℂ) :
    VectorMeasure.integral μ (fun x => a * g x) (ContinuousLinearMap.mul ℝ ℂ) =
      a * VectorMeasure.integral μ g (ContinuousLinearMap.mul ℝ ℂ) := by
  rw [VectorMeasure.integral_eq_setToFun, VectorMeasure.integral_eq_setToFun]
  have hsm : ∀ (c : ℂ) (s : Set X) (x : ℂ),
      μ.transpose (ContinuousLinearMap.mul ℝ ℂ) s (c • x) =
        c • μ.transpose (ContinuousLinearMap.mul ℝ ℂ) s x := by
    intro c s x
    rw [transpose_eq_cbmApplyMeasure, cbmApplyMeasure_apply, cbmApplyMeasure_apply,
      ContinuousLinearMap.mul_apply', ContinuousLinearMap.mul_apply', smul_eq_mul, smul_eq_mul,
      mul_assoc]
  exact setToFun_smul _ hsm a g

/-- A `ℂ`-linear form on `ℂ^ι` commutes with the scalar integral against a complex measure,
applied coordinatewise. -/
theorem linearMap_integral (μ : ComplexMeasure X) {ι : Type*} [Fintype ι] (G : X → ι → ℂ)
    (hG : ∀ i, Integrable (fun x => G x i) μ.variation) (ℓ : (ι → ℂ) →ₗ[ℂ] ℂ) :
    ℓ (fun i => VectorMeasure.integral μ (fun x => G x i) (ContinuousLinearMap.mul ℝ ℂ)) =
      VectorMeasure.integral μ (fun x => ℓ (G x)) (ContinuousLinearMap.mul ℝ ℂ) := by
  classical
  have hexp : ∀ v : ι → ℂ, ℓ v = ∑ i, ℓ (fun j => if i = j then 1 else 0) * v i := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ ℓ v]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
  rw [hexp]
  simp_rw [hexp (G _)]
  rw [VectorMeasure.integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]
  · intro i _
    exact (hG i).const_mul _

end Sol_PettisIntegral_complexWeakIntegral_mem_smul_closure_absConvexHull

open PettisIntegral Sol_PettisIntegral_complexWeakIntegral_mem_smul_closure_absConvexHull

theorem solution {E X : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [PolynormableSpace ℂ E] [T2Space E]
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [Nonempty X] (μ : ComplexMeasure X) [IsFiniteMeasure μ.variation] [μ.variation.Regular]
    (f : X → E) (hf : Continuous f) (hfi : ComplexWeaklyIntegrable μ f) :
    complexWeakIntegral μ f ∈
      (μ.variation Set.univ).toReal •
        closure (convexHull ℝ (balancedHull ℂ
          (Set.range fun x : X => toWeakCompletion ℂ (f x)))) := by
  have _ := hf
  set H := convexHull ℝ (balancedHull ℂ (Set.range fun x : X => toWeakCompletion ℂ (f x)))
    with hH
  have hne : (closure H).Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty X›
    exact ⟨_, subset_closure (subset_convexHull ℝ _
      (subset_balancedHull ℂ (Set.mem_range_self x)))⟩
  by_cases hm : (μ.variation Set.univ).toReal = 0
  · -- the total variation vanishes: both sides reduce to `0`
    have hv : μ.variation = 0 := by
      have h0 : μ.variation Set.univ = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff _).mp hm with h | h
        · exact h
        · exact absurd h (measure_ne_top _ _)
      exact Measure.measure_univ_eq_zero.mp h0
    have hw : complexWeakIntegral μ f = 0 := by
      funext φ
      simp only [complexWeakIntegral_apply, Pi.zero_apply]
      apply VectorMeasure.integral_eq_zero_of_ae
      rw [hv, MeasureTheory.ae_zero]
      exact Filter.eventually_bot
    rw [hw, hm, Set.zero_smul_set hne]
    exact Set.mem_zero.mpr rfl
  · set c := (μ.variation Set.univ).toReal with hc
    have hpos : 0 < c := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hm)
    refine Set.mem_smul_set.mpr ⟨c⁻¹ • complexWeakIntegral μ f, ?_, smul_inv_smul₀ hm _⟩
    refine mem_closure_pi_of_forall_finset fun I => ?_
    -- the finitely many coordinates `φ ∈ I` of `f`
    let F : X → (I → ℂ) := fun x i => i.1 (f x)
    -- restriction to the coordinates in `I`
    let R : (StrongDual ℂ E → ℂ) →ₗ[ℂ] (I → ℂ) :=
      { toFun := fun a i => a i.1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hsub : convexHull ℝ (balancedHull ℂ (Set.range F)) ⊆
        (fun (a : StrongDual ℂ E → ℂ) (i : I) => a i.1) '' H := by
      have h1 : balancedHull ℂ (Set.range F) ⊆ (R.restrictScalars ℝ) ''
          balancedHull ℂ (Set.range fun x : X => toWeakCompletion ℂ (f x)) := by
        intro y hy
        obtain ⟨r, hr, hyr⟩ := mem_balancedHull_iff.mp hy
        obtain ⟨z, ⟨x, rfl⟩, rfl⟩ := Set.mem_smul_set.mp hyr
        refine ⟨r • toWeakCompletion ℂ (f x), mem_balancedHull_iff.mpr
          ⟨r, hr, Set.smul_mem_smul_set (Set.mem_range_self x)⟩, ?_⟩
        rfl
      calc convexHull ℝ (balancedHull ℂ (Set.range F))
          ⊆ convexHull ℝ ((R.restrictScalars ℝ) ''
              balancedHull ℂ (Set.range fun x : X => toWeakCompletion ℂ (f x))) :=
            convexHull_mono h1
        _ = (R.restrictScalars ℝ) '' H := (LinearMap.image_convexHull _ _).symm
        _ = _ := rfl
    refine closure_mono hsub ?_
    -- finite-dimensional mean value theorem, by Hahn–Banach separation
    by_contra hnot
    obtain ⟨ℓ, u, hℓv, hℓK⟩ := RCLike.geometric_hahn_banach_point_closed (𝕜 := ℂ)
      (convex_convexHull ℝ _).closure isClosed_closure hnot
    have hbound : ∀ x, ‖ℓ (F x)‖ ≤ -u := by
      intro x
      set w := ℓ (F x) with hw
      set z : ℂ := -(starRingEnd ℂ w) / (‖w‖ : ℂ) with hz
      have hz1 : ‖z‖ ≤ 1 := by
        rw [hz, norm_div, norm_neg, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
          abs_norm]
        exact div_self_le_one _
      have hzw : z * w = -(‖w‖ : ℂ) := by
        by_cases hw0 : w = 0
        · simp [hw0]
        · have hn : (‖w‖ : ℂ) ≠ 0 := by
            exact_mod_cast norm_ne_zero_iff.mpr hw0
          rw [hz, div_mul_eq_mul_div, neg_mul, Complex.conj_mul', div_eq_iff hn]
          ring
      have hmem : z • F x ∈ closure (convexHull ℝ (balancedHull ℂ (Set.range F))) :=
        subset_closure (subset_convexHull ℝ _ (mem_balancedHull_iff.mpr
          ⟨z, hz1, Set.smul_mem_smul_set (Set.mem_range_self x)⟩))
      have h2 := hℓK _ hmem
      rw [map_smul, smul_eq_mul, hzw] at h2
      simp only [map_neg] at h2
      have h3 : RCLike.re (-(‖w‖ : ℂ)) = -‖w‖ := by simp
      linarith [h3 ▸ h2]
    have hu : 0 ≤ -u := by
      obtain ⟨x⟩ := ‹Nonempty X›
      exact (norm_nonneg _).trans (hbound x)
    -- `ℓ` commutes with the integral
    have hint : ℓ (fun i : I => (c⁻¹ • complexWeakIntegral μ f) i.1) =
        (c : ℂ)⁻¹ * VectorMeasure.integral μ (fun x => ℓ (F x))
          (ContinuousLinearMap.mul ℝ ℂ) := by
      have heq : (fun i : I => (c⁻¹ • complexWeakIntegral μ f) i.1) =
          (c : ℂ)⁻¹ • fun i : I => VectorMeasure.integral μ (fun x => F x i)
            (ContinuousLinearMap.mul ℝ ℂ) := by
        funext i
        simp only [Pi.smul_apply, complexWeakIntegral_apply, F, Complex.real_smul, smul_eq_mul,
          Complex.ofReal_inv]
      rw [heq, map_smul, smul_eq_mul]
      congr 1
      exact linearMap_integral μ F (fun i => hfi i.1) ℓ.toLinearMap
    have hnorm : ‖ℓ (fun i : I => (c⁻¹ • complexWeakIntegral μ f) i.1)‖ ≤ -u := by
      rw [hint, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      have h4 := VectorMeasure.norm_integral_le_of_norm_le_const (μ := μ)
        (B := ContinuousLinearMap.mul ℝ ℂ) (f := fun x => ℓ (F x))
        (Filter.Eventually.of_forall hbound)
      have h5 : ‖(ContinuousLinearMap.mul ℝ ℂ : ℂ →L[ℝ] ℂ →L[ℝ] ℂ)‖ ≤ 1 :=
        ContinuousLinearMap.opNorm_mul_le _ _
      have h6 : μ.variation.real Set.univ = c := rfl
      rw [h6] at h4
      calc c⁻¹ * ‖VectorMeasure.integral μ (fun x => ℓ (F x)) (ContinuousLinearMap.mul ℝ ℂ)‖
          ≤ c⁻¹ * (-u * ‖(ContinuousLinearMap.mul ℝ ℂ : ℂ →L[ℝ] ℂ →L[ℝ] ℂ)‖ * c) := by
            gcongr
        _ ≤ c⁻¹ * (-u * 1 * c) := by gcongr
        _ = -u := by field_simp
    have h7 := RCLike.abs_re_le_norm (ℓ (fun i : I => (c⁻¹ • complexWeakIntegral μ f) i.1))
    have h8 := neg_abs_le (RCLike.re (ℓ (fun i : I => (c⁻¹ • complexWeakIntegral μ f) i.1)))
    linarith
