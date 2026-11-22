-- Prove2me | solution 1 for VectorValuedHolomorphy.differentiableOn_iterate_deriv
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:00:02.581804+00:00
-- url     : https://prove2.me/submissions/02172d97-9ddf-42fd-b865-26174b1fdd7c

import Mathlib

open Filter Topology Metric
open scoped Real

set_option autoImplicit false

namespace Sol_VectorValuedHolomorphy_differentiableOn_iterate_deriv

open Bornology Set

/-- Mackey: a weakly bounded subset of a polynormable space is von Neumann bounded. -/
theorem isVonNBounded_of_dual_bounded {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [PolynormableSpace 𝕜 E] {s : Set E}
    (h : ∀ f : StrongDual 𝕜 E, ∃ C : ℝ, ∀ x ∈ s, ‖f x‖ ≤ C) : IsVonNBounded 𝕜 s := by
  let hp := PolynormableSpace.withSeminorms 𝕜 E
  refine hp.isVonNBounded_iff_seminorm_bddAbove.mpr fun p ↦ ?_
  rw [bddAbove_def]
  let e : ULift.{0} E ≃ₗ[𝕜] E := ULift.moduleEquiv
  let q := p.val.comp e.toLinearMap
  let : SeminormedAddCommGroup (ULift.{0} E) := q.toSeminormedAddCommGroup
  let : TopologicalSpace (ULift.{0} E) := q.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace
  let : NormedSpace 𝕜 (ULift.{0} E) := ⟨fun c x ↦ (map_smul_eq_mul q c x).le⟩
  let : IsTopologicalAddGroup E := hp.topologicalAddGroup
  have he : Continuous e.symm := by
    refine (Metric.continuous_iff' (f := fun y : E ↦ e.symm y)).mpr fun x ε hε ↦ ?_
    have hcont : Continuous (fun y : E ↦ p.val (y - x)) :=
      p.property.comp (continuous_id.sub continuous_const)
    have hsmall := hcont.continuousAt (x := x).eventually_lt continuousAt_const
      (show p.val (x - x) < ε by simpa)
    simp only [dist_eq_norm, ← map_sub]
    exact hsmall
  -- Apply uniform boundedness to the evaluations on the Banach dual for this seminorm.
  let ev (x : s) := NormedSpace.inclusionInDoubleDual 𝕜 (ULift E) (e.symm x)
  obtain ⟨C, hC⟩ := banach_steinhaus (g := ev) fun f ↦ by
    obtain ⟨C, hC⟩ := h (f.comp ⟨e.symm.toLinearMap, he⟩)
    exact ⟨C, fun x ↦ hC x x.property⟩
  refine ⟨C, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  change ‖e.symm x‖ ≤ C
  rw [← (NormedSpace.inclusionInDoubleDualLi 𝕜).norm_map (e.symm x)]
  exact hC ⟨x, hx⟩

/-- The derivative of a curve in a topological vector space is the limit of its slopes. -/
theorem hasDerivAt_iff_tendsto_slope_tvs {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] (f : ℂ → E) (z : ℂ)
    (v : E) : HasDerivAt f v z ↔
      Tendsto (fun w ↦ (w - z)⁻¹ • (f w - f z)) (𝓝[≠] z) (𝓝 v) := by
  rw [hasDerivAt_iff_hasFDerivAt, ← hasFDerivWithinAt_univ,
    ← hasFDerivWithinAt_sdiff_singleton_self, ← Set.compl_eq_univ_sdiff,
    hasFDerivWithinAt_iff_isLittleOTVS]
  change (fun w ↦ f w - f z - (w - z) • v) =o[ℂ; 𝓝[≠] z] (fun w ↦ w - z) ↔ _
  rw [Asymptotics.isLittleOTVS_iff_tendsto_inv_smul (by
    filter_upwards with w hw
    simp [sub_eq_zero.mp hw])]
  conv_rhs => rw [← tendsto_sub_nhds_zero_iff]
  apply tendsto_congr'
  filter_upwards [eventually_mem_nhdsWithin] with w hw
  simp [smul_sub, inv_smul_smul₀ (sub_ne_zero.mpr hw)]

/-- The divided slopes of a scalar holomorphic function are Lipschitz on a closed disc. -/
theorem exists_dslope_lipschitz {U : Set ℂ} (hU : IsOpen U) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ U) {z₀ : ℂ} {r : ℝ} (hr : closedBall z₀ r ⊆ U)
    (hz₀ : z₀ ∈ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ closedBall z₀ r, ∀ w ∈ closedBall z₀ r,
      ‖dslope φ z₀ z - dslope φ z₀ w‖ ≤ C * ‖z - w‖ := by
  have hψ : DifferentiableOn ℂ (dslope φ z₀) U :=
    (Complex.differentiableOn_dslope (hU.mem_nhds hz₀)).mpr hφ
  have hψ' : ContinuousOn (deriv (dslope φ z₀)) U := (hψ.deriv hU).continuousOn
  obtain ⟨C, hC⟩ := ((isCompact_closedBall z₀ r).image_of_continuousOn
    (hψ'.mono hr)).isBounded.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, fun z hz w hw ↦ ?_⟩
  exact (convex_closedBall z₀ r).norm_image_sub_le_of_norm_deriv_le
    (fun x hx ↦ hψ.differentiableAt (hU.mem_nhds (hr hx)))
    (fun x hx ↦ (hC _ (mem_image_of_mem _ hx)).trans (le_max_left _ _)) hw hz

/-- The divided slopes of a scalar holomorphic function are bounded on a closed disc. -/
theorem exists_dslope_bound {U : Set ℂ} (hU : IsOpen U) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ U) {z₀ : ℂ} {r : ℝ} (hr : closedBall z₀ r ⊆ U)
    (hz₀ : z₀ ∈ U) :
    ∃ C : ℝ, ∀ z ∈ closedBall z₀ r, ‖dslope φ z₀ z‖ ≤ C := by
  have hψ : DifferentiableOn ℂ (dslope φ z₀) U :=
    (Complex.differentiableOn_dslope (hU.mem_nhds hz₀)).mpr hφ
  obtain ⟨C, hC⟩ := ((isCompact_closedBall z₀ r).image_of_continuousOn
    (hψ.continuousOn.mono hr)).isBounded.exists_norm_le
  exact ⟨C, fun z hz ↦ hC _ (mem_image_of_mem _ hz)⟩

/-- Grothendieck: a weakly holomorphic function with values in a quasi-complete Hausdorff
locally convex space is complex differentiable. -/
theorem differentiableOn_of_weak {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    [T2Space E] [QuasiCompleteSpace ℂ E] {U : Set ℂ} (hU : IsOpen U) (f : ℂ → E)
    (hf : ∀ ℓ : StrongDual ℂ E, DifferentiableOn ℂ (fun z => ℓ (f z)) U) :
    DifferentiableOn ℂ f U := by
  intro z₀ hz₀
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz₀)
  let q : ℂ → E := fun w ↦ (w - z₀)⁻¹ • (f w - f z₀)
  let B : Set ℂ := closedBall z₀ r \ {z₀}
  let D : ℂ × ℂ → E := fun p ↦ (p.1 - p.2)⁻¹ • (q p.1 - q p.2)
  have hℓq : ∀ (ℓ : StrongDual ℂ E) (w : ℂ), w ≠ z₀ →
      ℓ (q w) = dslope (fun z => ℓ (f z)) z₀ w := by
    intro ℓ w hw
    rw [dslope_of_ne _ hw, slope_def_module]
    simp [q]
  have hS : IsVonNBounded ℂ (D '' (B ×ˢ B)) := by
    apply isVonNBounded_of_dual_bounded
    intro ℓ
    obtain ⟨C, hC0, hC⟩ := exists_dslope_lipschitz hU (hf ℓ) hsub hz₀
    refine ⟨C, ?_⟩
    rintro _ ⟨⟨z, w⟩, ⟨hz, hw⟩, rfl⟩
    simp only [D, map_smul, map_sub, smul_eq_mul, norm_mul, norm_inv]
    rw [hℓq ℓ z hz.2, hℓq ℓ w hw.2]
    have h := hC z hz.1 w hw.1
    by_cases hzw : z = w
    · simp [hzw, hC0]
    · rw [inv_mul_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hzw))]
      linarith [mul_comm C ‖z - w‖]
  have hBmem : B ∈ 𝓝[≠] z₀ := sdiff_mem_nhdsWithin_compl (closedBall_mem_nhds z₀ hr) {z₀}
  have hdiff : Tendsto (fun p : ℂ × ℂ ↦ q p.1 - q p.2) (𝓝[≠] z₀ ×ˢ 𝓝[≠] z₀) (𝓝 0) := by
    have hε : Tendsto (fun p : ℂ × ℂ ↦ p.1 - p.2) (𝓝[≠] z₀ ×ˢ 𝓝[≠] z₀) (𝓝 0) := by
      have h1 : Tendsto (fun p : ℂ × ℂ ↦ p.1) (𝓝[≠] z₀ ×ˢ 𝓝[≠] z₀) (𝓝 z₀) :=
        tendsto_fst.mono_right nhdsWithin_le_nhds
      have h2 : Tendsto (fun p : ℂ × ℂ ↦ p.2) (𝓝[≠] z₀ ×ˢ 𝓝[≠] z₀) (𝓝 z₀) :=
        tendsto_snd.mono_right nhdsWithin_le_nhds
      simpa using h1.sub h2
    have hmem : ∀ᶠ p in 𝓝[≠] z₀ ×ˢ 𝓝[≠] z₀, D p ∈ D '' (B ×ˢ B) := by
      filter_upwards [prod_mem_prod hBmem hBmem] with p hp
      exact mem_image_of_mem D hp
    refine (hS.smul_tendsto_zero hmem hε).congr fun p ↦ ?_
    by_cases h : p.1 = p.2
    · simp [h]
    · simp [D, smul_inv_smul₀ (sub_ne_zero.mpr h)]
  have hcauchy : Cauchy (map q (𝓝[≠] z₀)) := by
    rw [cauchy_map_iff]
    refine ⟨inferInstance, ?_⟩
    rw [uniformity_eq_comap_nhds_zero_swapped E, tendsto_comap_iff]
    exact hdiff
  have hbdd : IsVonNBounded ℂ (q '' B) := by
    apply isVonNBounded_of_dual_bounded
    intro ℓ
    obtain ⟨C, hC⟩ := exists_dslope_bound hU (hf ℓ) hsub hz₀
    refine ⟨C, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    rw [hℓq ℓ w hw.2]
    exact hC w hw.1
  have hcomplete : IsComplete (closure (q '' B)) :=
    QuasiCompleteSpace.quasiComplete hbdd.closure isClosed_closure
  obtain ⟨L, -, hL⟩ := hcomplete _ hcauchy (le_principal_iff.mpr
    (mem_map.mpr (mem_of_superset hBmem fun w hw ↦ subset_closure (mem_image_of_mem q hw))))
  have hderiv : HasDerivAt f L z₀ := (hasDerivAt_iff_tendsto_slope_tvs f z₀ L).mpr hL
  exact hderiv.hasFDerivAt.differentiableAt.differentiableWithinAt

/-- A continuous linear functional commutes with the complex derivative of a curve in a
topological vector space. -/
theorem hasDerivAt_strongDual_comp {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] {f : ℂ → E} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (ℓ : StrongDual ℂ E) :
    HasDerivAt (fun w => ℓ (f w)) (ℓ (deriv f z)) z := by
  have hf' : HasFDerivAt f (fderiv ℂ f z) z := hf.hasFDerivAt
  have h : HasFDerivAt (fun w => ℓ (f w)) (ℓ.comp (fderiv ℂ f z)) z := by
    refine HasFDerivAt.of_isLittleOTVS ?_
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, map_sub]
      using ℓ.isBigOTVS_comp.trans_isLittleOTVS hf'.isLittleOTVS
  exact hasFDerivAt_iff_hasDerivAt.mp h

/-- The statement, by induction on the order of the derivative, for all weakly holomorphic
functions simultaneously. -/
theorem main {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    [T2Space E] [QuasiCompleteSpace ℂ E] {U : Set ℂ} (hU : IsOpen U) (k : ℕ) :
    ∀ f : ℂ → E, (∀ ℓ : StrongDual ℂ E, DifferentiableOn ℂ (fun z => ℓ (f z)) U) →
      DifferentiableOn ℂ (deriv^[k] f) U ∧
        ∀ ℓ : StrongDual ℂ E, ∀ z ∈ U,
          ℓ (deriv^[k] f z) = iteratedDeriv k (fun w => ℓ (f w)) z := by
  induction k with
  | zero =>
    intro f hf
    refine ⟨differentiableOn_of_weak hU f hf, fun ℓ z _ ↦ ?_⟩
    rw [iteratedDeriv_zero, Function.iterate_zero, id_eq]
  | succ k ih =>
    intro f hf
    -- `f` is differentiable on `U`, and `ℓ ∘ f' = (ℓ ∘ f)'` there
    have hfd : DifferentiableOn ℂ f U := differentiableOn_of_weak hU f hf
    have hd : ∀ ℓ : StrongDual ℂ E, ∀ z ∈ U,
        ℓ (deriv f z) = deriv (fun w => ℓ (f w)) z := fun ℓ z hz ↦
      ((hasDerivAt_strongDual_comp (hfd.differentiableAt (hU.mem_nhds hz)) ℓ).deriv).symm
    -- hence `f'` is weakly holomorphic on `U`
    have hf' : ∀ ℓ : StrongDual ℂ E, DifferentiableOn ℂ (fun z => ℓ (deriv f z)) U :=
      fun ℓ ↦ ((hf ℓ).deriv hU).congr fun z hz ↦ hd ℓ z hz
    obtain ⟨h1, h2⟩ := ih (deriv f) hf'
    rw [Function.iterate_succ_apply]
    refine ⟨h1, fun ℓ z hz ↦ ?_⟩
    rw [h2 ℓ z hz, iteratedDeriv_succ']
    have hev : (fun w => ℓ (deriv f w)) =ᶠ[𝓝 z] deriv (fun w => ℓ (f w)) := by
      filter_upwards [hU.mem_nhds hz] with w hw using hd ℓ w hw
    exact (hev.iteratedDeriv k).eq_of_nhds

end Sol_VectorValuedHolomorphy_differentiableOn_iterate_deriv

theorem solution {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    [T2Space E] [QuasiCompleteSpace ℂ E] {U : Set ℂ} (hU : IsOpen U) {f : ℂ → E}
    (hf : ∀ ℓ : StrongDual ℂ E, DifferentiableOn ℂ (fun z => ℓ (f z)) U) (k : ℕ) :
    DifferentiableOn ℂ (deriv^[k] f) U ∧
      ∀ ℓ : StrongDual ℂ E, ∀ z ∈ U,
        ℓ (deriv^[k] f z) = iteratedDeriv k (fun w => ℓ (f w)) z :=
  Sol_VectorValuedHolomorphy_differentiableOn_iterate_deriv.main hU k f hf
