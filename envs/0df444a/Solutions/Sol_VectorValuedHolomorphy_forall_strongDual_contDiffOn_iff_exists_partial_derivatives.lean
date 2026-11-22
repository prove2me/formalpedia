-- Prove2me | solution 1 for VectorValuedHolomorphy.forall_strongDual_contDiffOn_iff_exists_partial_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:31:58.885061+00:00
-- url     : https://prove2.me/submissions/540cc8b2-bcbf-4159-b985-e664f1733646

import Mathlib

open Filter Topology Metric
open scoped Real

set_option autoImplicit false

namespace Sol_VectorValuedHolomorphy_forall_strongDual_contDiffOn_iff_exists_partial_derivatives

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
theorem hasDerivAt_iff_tendsto_slope_tvs {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] (f : ℝ → E) (z : ℝ)
    (v : E) : HasDerivAt f v z ↔
      Tendsto (fun w ↦ (w - z)⁻¹ • (f w - f z)) (𝓝[≠] z) (𝓝 v) := by
  rw [hasDerivAt_iff_hasFDerivAt, ← hasFDerivWithinAt_univ,
    ← hasFDerivWithinAt_sdiff_singleton_self, ← Set.compl_eq_univ_sdiff,
    hasFDerivWithinAt_iff_isLittleOTVS]
  change (fun w ↦ f w - f z - (w - z) • v) =o[ℝ; 𝓝[≠] z] (fun w ↦ w - z) ↔ _
  rw [Asymptotics.isLittleOTVS_iff_tendsto_inv_smul (by
    filter_upwards with w hw
    simp [sub_eq_zero.mp hw])]
  conv_rhs => rw [← tendsto_sub_nhds_zero_iff]
  apply tendsto_congr'
  filter_upwards [eventually_mem_nhdsWithin] with w hw
  simp [smul_sub, inv_smul_smul₀ (sub_ne_zero.mpr hw)]

/-- A continuous linear functional maps the derivative of a curve to the derivative of the
scalar curve. -/
theorem hasDerivAt_strongDual_comp {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] (ℓ : StrongDual ℝ E)
    {φ : ℝ → E} {v : E} {z : ℝ} (h : HasDerivAt φ v z) :
    HasDerivAt (fun t => ℓ (φ t)) (ℓ v) z := by
  rw [hasDerivAt_iff_tendsto_slope_tvs] at h ⊢
  have := (ℓ.continuous.tendsto v).comp h
  refine this.congr fun w => ?_
  simp [map_sub]

/-- Second order Taylor estimate at `0` for a scalar `C²` function. -/
theorem exists_taylor_bound {U : Set ℝ} (hU : IsOpen U) {ψ : ℝ → ℝ}
    (hψ : ContDiffOn ℝ 2 ψ U) {r : ℝ} (hr : closedBall (0 : ℝ) r ⊆ U) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ closedBall (0 : ℝ) r,
      ‖ψ t - ψ 0 - t * deriv ψ 0‖ ≤ M * ‖t‖ * ‖t‖ := by
  have hd1 : DifferentiableOn ℝ ψ U := hψ.differentiableOn (by norm_num)
  have hψ1 : ContDiffOn ℝ 1 (deriv ψ) U := hψ.deriv_of_isOpen hU (by norm_num)
  have hd2 : DifferentiableOn ℝ (deriv ψ) U := hψ1.differentiableOn one_ne_zero
  have hc2 : ContinuousOn (deriv (deriv ψ)) U := hψ1.continuousOn_deriv_of_isOpen hU le_rfl
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : ℝ) r).image_of_continuousOn
    (hc2.mono hr)).isBounded.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, fun t ht ↦ ?_⟩
  -- first order estimate for the derivative
  have h1 : ∀ s ∈ closedBall (0 : ℝ) r, ‖deriv ψ s - deriv ψ 0‖ ≤ max C 0 * ‖s‖ := by
    intro s hs
    have := (convex_closedBall (0 : ℝ) r).norm_image_sub_le_of_norm_deriv_le
      (f := deriv ψ) (C := max C 0)
      (fun x hx ↦ hd2.differentiableAt (hU.mem_nhds (hr hx)))
      (fun x hx ↦ (hC _ (mem_image_of_mem _ hx)).trans (le_max_left _ _))
      (mem_closedBall_self (by
        have := dist_nonneg.trans (mem_closedBall.mp ht)
        exact this)) hs
    simpa using this
  have htr : ‖t‖ ≤ r := by simpa using ht
  have hsub : closedBall (0 : ℝ) ‖t‖ ⊆ closedBall (0 : ℝ) r := closedBall_subset_closedBall htr
  have h2 := (convex_closedBall (0 : ℝ) ‖t‖).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s ↦ ψ s - s * deriv ψ 0) (f' := fun s ↦ deriv ψ s - deriv ψ 0)
    (C := max C 0 * ‖t‖) (x := 0) (y := t)
    (fun s hs ↦ by
      have hds : HasDerivAt ψ (deriv ψ s) s :=
        (hd1.differentiableAt (hU.mem_nhds (hr (hsub hs)))).hasDerivAt
      have h3 : HasDerivAt (fun y : ℝ ↦ y * deriv ψ 0) (deriv ψ 0) s := by
        simpa using (hasDerivAt_id s).mul_const (deriv ψ 0)
      exact (hds.sub h3).hasDerivWithinAt)
    (fun s hs ↦ (h1 s (hsub hs)).trans (by
      have : ‖s‖ ≤ ‖t‖ := by simpa using hs
      exact mul_le_mul_of_nonneg_left this (le_max_right _ _)))
    (mem_closedBall_self (norm_nonneg t)) (by simp)
  have h4 : ψ t - ψ 0 - t * deriv ψ 0 = (ψ t - t * deriv ψ 0) - (ψ 0 - 0 * deriv ψ 0) := by ring
  rw [h4]
  simpa using h2

/-- A curve in a quasi-complete locally convex space which is weakly `C²` near `0` has a
derivative at `0`. -/
theorem exists_hasDerivAt_of_weak {E : Type*} [AddCommGroup E] [Module ℝ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℝ E] [PolynormableSpace ℝ E]
    [T2Space E] [QuasiCompleteSpace ℝ E] {U : Set ℝ} (hU : IsOpen U) (h0 : (0 : ℝ) ∈ U)
    (φ : ℝ → E) (hφ : ∀ ℓ : StrongDual ℝ E, ContDiffOn ℝ 2 (fun t => ℓ (φ t)) U) :
    ∃ v : E, HasDerivAt φ v 0 := by
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds h0)
  let q : ℝ → E := fun w ↦ (w - 0)⁻¹ • (φ w - φ 0)
  let B : Set ℝ := closedBall 0 r \ {0}
  let D : ℝ × ℝ → E := fun p ↦ (‖p.1‖ + ‖p.2‖)⁻¹ • (q p.1 - q p.2)
  -- the weak estimate
  have key : ∀ ℓ : StrongDual ℝ E, ∃ c M : ℝ, 0 ≤ M ∧ ∀ t ∈ B, ‖ℓ (q t) - c‖ ≤ M * ‖t‖ := by
    intro ℓ
    obtain ⟨M, hM0, hM⟩ := exists_taylor_bound hU (hφ ℓ) hsub
    refine ⟨deriv (fun t => ℓ (φ t)) 0, M, hM0, fun t ht ↦ ?_⟩
    have ht0 : t ≠ 0 := ht.2
    have hnt : 0 < ‖t‖ := norm_pos_iff.mpr ht0
    have h := hM t ht.1
    have heq : ℓ (q t) - deriv (fun t => ℓ (φ t)) 0 =
        t⁻¹ * (ℓ (φ t) - ℓ (φ 0) - t * deriv (fun t => ℓ (φ t)) 0) := by
      simp only [q, sub_zero, map_smul, map_sub, smul_eq_mul]
      field_simp
    rw [heq, norm_mul, norm_inv, inv_mul_le_iff₀ hnt]
    linarith [mul_comm ‖t‖ (M * ‖t‖)]
  have hBmem : B ∈ 𝓝[≠] (0 : ℝ) := sdiff_mem_nhdsWithin_compl (closedBall_mem_nhds 0 hr) {0}
  have hS : IsVonNBounded ℝ (D '' (B ×ˢ B)) := by
    apply isVonNBounded_of_dual_bounded
    intro ℓ
    obtain ⟨c, M, hM0, hM⟩ := key ℓ
    refine ⟨M, ?_⟩
    rintro _ ⟨⟨t, s⟩, ⟨ht, hs⟩, rfl⟩
    have hnt : 0 < ‖t‖ := norm_pos_iff.mpr ht.2
    have hpos : 0 < ‖t‖ + ‖s‖ := add_pos_of_pos_of_nonneg hnt (norm_nonneg s)
    have h1 := hM t ht
    have h2 := hM s hs
    have h3 : ‖ℓ (q t) - ℓ (q s)‖ ≤ M * (‖t‖ + ‖s‖) := by
      calc ‖ℓ (q t) - ℓ (q s)‖ = ‖(ℓ (q t) - c) - (ℓ (q s) - c)‖ := by congr 1; ring
        _ ≤ ‖ℓ (q t) - c‖ + ‖ℓ (q s) - c‖ := norm_sub_le _ _
        _ ≤ M * ‖t‖ + M * ‖s‖ := add_le_add h1 h2
        _ = M * (‖t‖ + ‖s‖) := by ring
    simp only [D, map_smul, map_sub, smul_eq_mul, norm_mul, norm_inv]
    rw [Real.norm_of_nonneg hpos.le, inv_mul_le_iff₀ hpos]
    linarith [mul_comm M (‖t‖ + ‖s‖)]
  have hdiff : Tendsto (fun p : ℝ × ℝ ↦ q p.1 - q p.2) (𝓝[≠] 0 ×ˢ 𝓝[≠] 0) (𝓝 0) := by
    have hε : Tendsto (fun p : ℝ × ℝ ↦ ‖p.1‖ + ‖p.2‖) (𝓝[≠] 0 ×ˢ 𝓝[≠] 0) (𝓝 0) := by
      have h1 : Tendsto (fun p : ℝ × ℝ ↦ p.1) (𝓝[≠] 0 ×ˢ 𝓝[≠] 0) (𝓝 0) :=
        tendsto_fst.mono_right nhdsWithin_le_nhds
      have h2 : Tendsto (fun p : ℝ × ℝ ↦ p.2) (𝓝[≠] 0 ×ˢ 𝓝[≠] 0) (𝓝 0) :=
        tendsto_snd.mono_right nhdsWithin_le_nhds
      simpa using h1.norm.add h2.norm
    have hmem : ∀ᶠ p in 𝓝[≠] (0 : ℝ) ×ˢ 𝓝[≠] (0 : ℝ), D p ∈ D '' (B ×ˢ B) := by
      filter_upwards [prod_mem_prod hBmem hBmem] with p hp
      exact mem_image_of_mem D hp
    refine (hS.smul_tendsto_zero hmem hε).congr' ?_
    filter_upwards [prod_mem_prod hBmem hBmem] with p hp
    have hnt : 0 < ‖p.1‖ := norm_pos_iff.mpr hp.1.2
    have hpos : 0 < ‖p.1‖ + ‖p.2‖ := add_pos_of_pos_of_nonneg hnt (norm_nonneg _)
    exact smul_inv_smul₀ hpos.ne' _
  have hcauchy : Cauchy (map q (𝓝[≠] (0 : ℝ))) := by
    rw [cauchy_map_iff]
    refine ⟨inferInstance, ?_⟩
    rw [uniformity_eq_comap_nhds_zero_swapped E, tendsto_comap_iff]
    exact hdiff
  have hbdd : IsVonNBounded ℝ (q '' B) := by
    apply isVonNBounded_of_dual_bounded
    intro ℓ
    obtain ⟨c, M, hM0, hM⟩ := key ℓ
    refine ⟨‖c‖ + M * r, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have h1 := hM t ht
    have htr : ‖t‖ ≤ r := by simpa using ht.1
    calc ‖ℓ (q t)‖ = ‖c + (ℓ (q t) - c)‖ := by congr 1; ring
      _ ≤ ‖c‖ + ‖ℓ (q t) - c‖ := norm_add_le _ _
      _ ≤ ‖c‖ + M * r := by
        have := mul_le_mul_of_nonneg_left htr hM0
        linarith
  have hcomplete : IsComplete (closure (q '' B)) :=
    QuasiCompleteSpace.quasiComplete hbdd.closure isClosed_closure
  obtain ⟨L, -, hL⟩ := hcomplete _ hcauchy (le_principal_iff.mpr
    (mem_map.mpr (mem_of_superset hBmem fun w hw ↦ subset_closure (mem_image_of_mem q hw))))
  exact ⟨L, (hasDerivAt_iff_tendsto_slope_tvs φ 0 L).mpr hL⟩

/-- A weakly `C¹` function on an open subset of a finite-dimensional space with values in a
locally convex space is continuous. -/
theorem continuousOn_of_weak {E : Type*} [AddCommGroup E] [Module ℝ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℝ E] [PolynormableSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]
    {Ω : Set F} (hΩ : IsOpen Ω) (g : F → E)
    (hg : ∀ ℓ : StrongDual ℝ E, ContDiffOn ℝ 1 (fun x => ℓ (g x)) Ω) : ContinuousOn g Ω := by
  intro x hx
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hx)
  let Q : F → E := fun y ↦ ‖y - x‖⁻¹ • (g y - g x)
  have hS : IsVonNBounded ℝ (Q '' closedBall x r) := by
    apply isVonNBounded_of_dual_bounded
    intro ℓ
    have hc : ContinuousOn (fderiv ℝ (fun x => ℓ (g x))) Ω :=
      (hg ℓ).continuousOn_fderiv_of_isOpen hΩ le_rfl
    have hd : DifferentiableOn ℝ (fun x => ℓ (g x)) Ω := (hg ℓ).differentiableOn one_ne_zero
    obtain ⟨C, hC⟩ := ((isCompact_closedBall x r).image_of_continuousOn
      (hc.mono hsub)).isBounded.exists_norm_le
    refine ⟨max C 0, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have h1 := (convex_closedBall x r).norm_image_sub_le_of_norm_fderiv_le
      (f := fun x => ℓ (g x)) (C := max C 0)
      (fun z hz ↦ hd.differentiableAt (hΩ.mem_nhds (hsub hz)))
      (fun z hz ↦ (hC _ (mem_image_of_mem _ hz)).trans (le_max_left _ _))
      (mem_closedBall_self hr.le) hy
    simp only [Q, map_smul, map_sub, smul_eq_mul, norm_mul, norm_inv, norm_norm]
    by_cases hyx : y = x
    · simp [hyx]
    · rw [inv_mul_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hyx))]
      linarith [mul_comm (max C 0) ‖y - x‖]
  have hε : Tendsto (fun y : F ↦ ‖y - x‖) (𝓝 x) (𝓝 0) := by
    have : Tendsto (fun y : F ↦ y - x) (𝓝 x) (𝓝 0) := by
      simpa using (tendsto_id (x := 𝓝 x)).sub_const x
    simpa using this.norm
  have hmem : ∀ᶠ y in 𝓝 x, Q y ∈ Q '' closedBall x r := by
    filter_upwards [closedBall_mem_nhds x hr] with y hy
    exact mem_image_of_mem Q hy
  have hlim : Tendsto (fun y : F ↦ g y - g x) (𝓝 x) (𝓝 0) := by
    refine (hS.smul_tendsto_zero hmem hε).congr fun y ↦ ?_
    by_cases hyx : y = x
    · simp [hyx]
    · exact smul_inv_smul₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hyx)) _
  have hcont : ContinuousAt g x := tendsto_sub_nhds_zero_iff.mp hlim
  exact hcont.continuousWithinAt

/-- A scalar function on an open subset of `ℝ^d` whose partial derivatives exist and are
continuous is Fréchet differentiable, with the expected derivative. -/
theorem hasFDerivAt_of_partial {d : ℕ} {Ω : Set (Fin d → ℝ)} (hΩ : IsOpen Ω)
    (g : (Fin d → ℝ) → ℝ) (g' : Fin d → (Fin d → ℝ) → ℝ)
    (hc : ∀ i, ContinuousOn (g' i) Ω)
    (hd : ∀ i, ∀ x ∈ Ω, HasDerivAt (fun t : ℝ => g (x + t • Pi.single i (1 : ℝ))) (g' i x) 0)
    {x : Fin d → ℝ} (hx : x ∈ Ω) :
    HasFDerivAt g
      (∑ i, g' i x • (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ)) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hcpos
  set ε : ℝ := c / (d + 1) with hεdef
  have hεpos : 0 < ε := by positivity
  -- a ball on which all partial derivatives are `ε`-close to their value at `x`
  have hev : ∀ᶠ y in 𝓝 x, y ∈ Ω ∧ ∀ i, ‖g' i y - g' i x‖ ≤ ε := by
    have h1 : ∀ᶠ y in 𝓝 x, y ∈ Ω := hΩ.eventually_mem hx
    have h2 : ∀ᶠ y in 𝓝 x, ∀ i, ‖g' i y - g' i x‖ ≤ ε := by
      refine eventually_all.mpr fun i ↦ ?_
      have hci : ContinuousAt (g' i) x := (hc i).continuousAt (hΩ.mem_nhds hx)
      have := Metric.tendsto_nhds.mp hci ε hεpos
      filter_upwards [this] with y hy
      rw [← dist_eq_norm]
      exact hy.le
    exact h1.and h2
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  -- membership in the ball in coordinates
  have hmemball : ∀ u : Fin d → ℝ, (∀ j, |u j| < δ) → x + u ∈ ball x δ := by
    intro u hu
    rw [mem_ball_iff_norm, add_sub_cancel_left, pi_norm_lt_iff hδ]
    exact fun j ↦ by simpa using hu j
  have hcoord : ∀ u : Fin d → ℝ, u ∈ ball (0 : Fin d → ℝ) δ → ∀ j, |u j| < δ := by
    intro u hu j
    rw [mem_ball_zero_iff, pi_norm_lt_iff hδ] at hu
    simpa using hu j
  -- the main estimate: change the coordinates in `J` one at a time
  have main : ∀ J : Finset (Fin d), ∀ u u' : Fin d → ℝ, (∀ j, |u j| < δ) → (∀ j, |u' j| < δ) →
      (∀ j, j ∉ J → u' j = u j) →
      ‖g (x + u') - g (x + u) - ∑ j ∈ J, (u' j - u j) * g' j x‖ ≤ ∑ j ∈ J, ε * ‖u' j - u j‖ := by
    intro J
    induction J using Finset.induction_on with
    | empty =>
      intro u u' _ _ hoff
      have : u' = u := funext fun j ↦ hoff j (Finset.notMem_empty j)
      simp [this]
    | insert k J hk ih =>
      intro u u' hu hu' hoff
      set w : Fin d → ℝ := Function.update u' k (u k) with hwdef
      have hwk : w k = u k := by simp [hwdef]
      have hwne : ∀ j, j ≠ k → w j = u' j := fun j hj ↦ by simp [hwdef, hj]
      have hw : ∀ j, |w j| < δ := by
        intro j
        by_cases hj : j = k
        · rw [hj, hwk]; exact hu k
        · rw [hwne j hj]; exact hu' j
      have hwoff : ∀ j, j ∉ J → w j = u j := by
        intro j hj
        by_cases hjk : j = k
        · rw [hjk, hwk]
        · rw [hwne j hjk]
          exact hoff j (by simp [hjk, hj])
      have h1 := ih u w hu hw hwoff
      have hsum1 : ∑ j ∈ J, (w j - u j) * g' j x = ∑ j ∈ J, (u' j - u j) * g' j x :=
        Finset.sum_congr rfl fun j hj ↦ by
          rw [hwne j (fun h ↦ hk (h ▸ hj))]
      have hsum2 : ∑ j ∈ J, ε * ‖w j - u j‖ = ∑ j ∈ J, ε * ‖u' j - u j‖ :=
        Finset.sum_congr rfl fun j hj ↦ by
          rw [hwne j (fun h ↦ hk (h ▸ hj))]
      rw [hsum1, hsum2] at h1
      -- the one-dimensional step in the direction `k`
      set a : ℝ := u' k - u k with hadef
      set e : Fin d → ℝ := Pi.single k (1 : ℝ) with hedef
      have hu'eq : u' = w + a • e := by
        funext j
        by_cases hj : j = k
        · subst hj
          simp [hedef, hwk, hadef]
        · simp [hedef, hwne j hj, Pi.single_eq_of_ne hj]
      have hpt : ∀ s ∈ Set.uIcc (0 : ℝ) a, x + w + s • e ∈ ball x δ := by
        intro s hs
        rw [add_assoc]
        refine hmemball _ fun j ↦ ?_
        by_cases hj : j = k
        · subst hj
          have h2 := abs_lt.mp (hu j)
          have h3 := abs_lt.mp (hu' j)
          simp only [Pi.add_apply, Pi.smul_apply, hedef, Pi.single_eq_same, smul_eq_mul, mul_one,
            hwk]
          rw [abs_lt]
          rcases Set.mem_uIcc.mp hs with ⟨h4, h5⟩ | ⟨h4, h5⟩
          · constructor <;> linarith
          · constructor <;> linarith
        · simpa [hedef, Pi.single_eq_of_ne hj, hwne j hj] using hu' j
      have hder : ∀ s ∈ Set.uIcc (0 : ℝ) a,
          HasDerivWithinAt (fun s : ℝ ↦ g (x + w + s • e) - s * g' k x)
            (g' k (x + w + s • e) - g' k x) (Set.uIcc (0 : ℝ) a) s := by
        intro s hs
        have h2 := hd k (x + w + s • e) (hball _ (hpt s hs)).1
        have h3 : HasDerivAt (fun s' : ℝ ↦ g (x + w + s • e + (s' - s) • e))
            (g' k (x + w + s • e)) s :=
          HasDerivAt.comp_sub_const (f := fun t : ℝ ↦ g (x + w + s • e + t • e)) s s
            (by simpa using h2)
        have h4 : (fun s' : ℝ ↦ g (x + w + s • e + (s' - s) • e)) =
            fun s' : ℝ ↦ g (x + w + s' • e) := by
          funext s'
          congr 1
          rw [sub_smul]
          abel
        rw [h4] at h3
        have h5 : HasDerivAt (fun y : ℝ ↦ y * g' k x) (g' k x) s := by
          simpa using (hasDerivAt_id s).mul_const (g' k x)
        exact (h3.sub h5).hasDerivWithinAt
      have h2 := (convex_uIcc (0 : ℝ) a).norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := fun s : ℝ ↦ g (x + w + s • e) - s * g' k x)
        (f' := fun s : ℝ ↦ g' k (x + w + s • e) - g' k x) (C := ε) (x := 0) (y := a)
        hder (fun s hs ↦ (hball _ (hpt s hs)).2 k) Set.left_mem_uIcc Set.right_mem_uIcc
      have h3 : g (x + u') - g (x + w) - a * g' k x =
          (g (x + w + a • e) - a * g' k x) - (g (x + w + (0 : ℝ) • e) - 0 * g' k x) := by
        rw [hu'eq, zero_smul, add_zero, zero_mul, sub_zero, add_assoc]
        ring
      rw [sub_zero, ← h3] at h2
      rw [Finset.sum_insert hk, Finset.sum_insert hk]
      calc ‖g (x + u') - g (x + u) - ((u' k - u k) * g' k x + ∑ j ∈ J, (u' j - u j) * g' j x)‖
          = ‖(g (x + u') - g (x + w) - a * g' k x) +
              (g (x + w) - g (x + u) - ∑ j ∈ J, (u' j - u j) * g' j x)‖ := by
            congr 1; ring
        _ ≤ ‖g (x + u') - g (x + w) - a * g' k x‖ +
              ‖g (x + w) - g (x + u) - ∑ j ∈ J, (u' j - u j) * g' j x‖ := norm_add_le _ _
        _ ≤ ε * ‖u' k - u k‖ + ∑ j ∈ J, ε * ‖u' j - u j‖ := add_le_add h2 h1
  -- conclusion
  filter_upwards [ball_mem_nhds (0 : Fin d → ℝ) hδ] with h hh
  have h1 := main Finset.univ 0 h (fun j ↦ by simpa using hδ) (hcoord h hh)
    (fun j hj ↦ absurd (Finset.mem_univ j) hj)
  have h2 : (∑ i, g' i x • (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ)) h =
      ∑ j, (h j - (0 : Fin d → ℝ) j) * g' j x := by
    simp [mul_comm]
  rw [h2]
  have h3 : ∑ j : Fin d, ε * ‖h j - (0 : Fin d → ℝ) j‖ ≤ c * ‖h‖ := by
    calc ∑ j : Fin d, ε * ‖h j - (0 : Fin d → ℝ) j‖ ≤ ∑ _j : Fin d, ε * ‖h‖ := by
          refine Finset.sum_le_sum fun j _ ↦ ?_
          have : ‖h j‖ ≤ ‖h‖ := norm_le_pi_norm h j
          simpa using mul_le_mul_of_nonneg_left this hεpos.le
      _ = d * (ε * ‖h‖) := by simp
      _ ≤ c * ‖h‖ := by
          have hd1 : (d : ℝ) * ε ≤ c := by
            rw [hεdef, mul_div_assoc', div_le_iff₀ (by positivity)]
            nlinarith [hcpos]
          calc (d : ℝ) * (ε * ‖h‖) = (d * ε) * ‖h‖ := by ring
            _ ≤ c * ‖h‖ := mul_le_mul_of_nonneg_right hd1 (norm_nonneg h)
  have h4 : x + (0 : Fin d → ℝ) = x := add_zero x
  rw [h4] at h1
  exact h1.trans h3

/-- Strong smoothness implies weak smoothness. -/
theorem weak_of_strong {E : Type*} [AddCommGroup E] [Module ℝ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℝ E] {d : ℕ}
    {Ω : Set (Fin d → ℝ)} (hΩ : IsOpen Ω) (D : List (Fin d) → (Fin d → ℝ) → E)
    (hDc : ∀ I, ContinuousOn (D I) Ω)
    (hDd : ∀ (I : List (Fin d)) (i : Fin d), ∀ x ∈ Ω,
      HasDerivAt (fun t : ℝ => D I (x + t • Pi.single i (1 : ℝ))) (D (i :: I) x) 0)
    (ℓ : StrongDual ℝ E) (n : ℕ) :
    ∀ I, ContDiffOn ℝ n (fun x => ℓ (D I x)) Ω := by
  induction n with
  | zero =>
    intro I
    rw [Nat.cast_zero, contDiffOn_zero]
    exact ℓ.continuous.comp_continuousOn (hDc I)
  | succ n ih =>
    intro I
    have hF : ∀ x ∈ Ω, HasFDerivAt (fun x => ℓ (D I x))
        (∑ i, ℓ (D (i :: I) x) • (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ)) x :=
      fun x hx ↦ hasFDerivAt_of_partial hΩ (fun x => ℓ (D I x)) (fun i x => ℓ (D (i :: I) x))
        (fun i ↦ ℓ.continuous.comp_continuousOn (hDc (i :: I)))
        (fun i y hy ↦ hasDerivAt_strongDual_comp ℓ (hDd I i y hy)) hx
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
    refine ⟨fun x hx ↦ (hF x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · intro h
      exact absurd h (by simp)
    · have h1 : ContDiffOn ℝ n (fun x => ∑ i,
          ℓ (D (i :: I) x) • (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ)) Ω :=
        ContDiffOn.sum fun i _ ↦ (ih (i :: I)).smul contDiffOn_const
      exact h1.congr fun x hx ↦ (hF x hx).fderiv

/-- The inductive step: a partial derivative of a weakly smooth function exists in `E`. -/
theorem exists_partial {E : Type*} [AddCommGroup E] [Module ℝ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℝ E] [PolynormableSpace ℝ E]
    [T2Space E] [QuasiCompleteSpace ℝ E] {d : ℕ}
    {Ω : Set (Fin d → ℝ)} (hΩ : IsOpen Ω) (g : (Fin d → ℝ) → E)
    (hg : ∀ (ℓ : StrongDual ℝ E), ContDiffOn ℝ 2 (fun x => ℓ (g x)) Ω)
    (i : Fin d) {x : Fin d → ℝ} (hx : x ∈ Ω) :
    ∃ v : E, HasDerivAt (fun t : ℝ => g (x + t • Pi.single i (1 : ℝ))) v 0 := by
  have hline : Continuous (fun t : ℝ => x + t • Pi.single i (1 : ℝ)) := by fun_prop
  refine exists_hasDerivAt_of_weak (U := (fun t : ℝ => x + t • Pi.single i (1 : ℝ)) ⁻¹' Ω)
    (hΩ.preimage hline) (by simpa using hx) _ fun ℓ ↦ ?_
  have hsm : ContDiff ℝ 2 (fun t : ℝ => x + t • Pi.single i (1 : ℝ)) := by fun_prop
  exact (hg ℓ).comp hsm.contDiffOn (fun t ht ↦ ht)

/-- The inductive step: the partial derivative of a weakly smooth function is weakly smooth. -/
theorem weak_partial {E : Type*} [AddCommGroup E] [Module ℝ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℝ E] {d : ℕ}
    {Ω : Set (Fin d → ℝ)} (hΩ : IsOpen Ω) (g g' : (Fin d → ℝ) → E)
    (hg : ∀ (ℓ : StrongDual ℝ E) (n : ℕ), ContDiffOn ℝ n (fun x => ℓ (g x)) Ω)
    (i : Fin d)
    (hg' : ∀ x ∈ Ω, HasDerivAt (fun t : ℝ => g (x + t • Pi.single i (1 : ℝ))) (g' x) 0)
    (ℓ : StrongDual ℝ E) (n : ℕ) : ContDiffOn ℝ n (fun x => ℓ (g' x)) Ω := by
  have h1 : ContDiffOn ℝ n
      (fun x => fderiv ℝ (fun y => ℓ (g y)) x (Pi.single i (1 : ℝ))) Ω := by
    have h2 : ContDiffOn ℝ n (fderiv ℝ (fun y => ℓ (g y))) Ω :=
      (hg ℓ (n + 1)).fderiv_of_isOpen hΩ (by rw [Nat.cast_succ])
    exact h2.clm_apply contDiffOn_const
  refine h1.congr fun x hx ↦ ?_
  have h3 : HasDerivAt (fun t : ℝ => ℓ (g (x + t • Pi.single i (1 : ℝ)))) (ℓ (g' x)) 0 :=
    hasDerivAt_strongDual_comp ℓ (hg' x hx)
  have hdiff : DifferentiableAt ℝ (fun y => ℓ (g y)) x :=
    ((hg ℓ 1).differentiableOn (by simp)).differentiableAt (hΩ.mem_nhds hx)
  have h4 : HasDerivAt (fun t : ℝ => x + t • Pi.single i (1 : ℝ)) (Pi.single i (1 : ℝ)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ))).const_add x
  have h5 : HasDerivAt (fun t : ℝ => ℓ (g (x + t • Pi.single i (1 : ℝ))))
      (fderiv ℝ (fun y => ℓ (g y)) x (Pi.single i (1 : ℝ))) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq (l := fun y => ℓ (g y)) 0 hdiff.hasFDerivAt h4 (by simp)
  exact h3.unique h5

/-- The iterated partial derivatives, chosen by `Classical.epsilon`. -/
noncomputable def partialD {E : Type*} [AddCommGroup E] [Module ℝ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℝ E] {d : ℕ}
    (f : (Fin d → ℝ) → E) : List (Fin d) → (Fin d → ℝ) → E
  | [] => f
  | i :: I => fun x => Classical.epsilon fun v : E =>
      HasDerivAt (fun t : ℝ => partialD f I (x + t • Pi.single i (1 : ℝ))) v 0

theorem partialD_spec {E : Type*} [AddCommGroup E] [Module ℝ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℝ E] [PolynormableSpace ℝ E]
    [T2Space E] [QuasiCompleteSpace ℝ E] {d : ℕ}
    {Ω : Set (Fin d → ℝ)} (hΩ : IsOpen Ω) (f : (Fin d → ℝ) → E)
    (hf : ∀ (ℓ : StrongDual ℝ E) (n : ℕ), ContDiffOn ℝ n (fun x => ℓ (f x)) Ω) :
    ∀ I : List (Fin d),
      (∀ (ℓ : StrongDual ℝ E) (n : ℕ), ContDiffOn ℝ n (fun x => ℓ (partialD f I x)) Ω) ∧
      ∀ (i : Fin d), ∀ x ∈ Ω,
        HasDerivAt (fun t : ℝ => partialD f I (x + t • Pi.single i (1 : ℝ)))
          (partialD f (i :: I) x) 0 := by
  have step : ∀ I : List (Fin d),
      (∀ (ℓ : StrongDual ℝ E) (n : ℕ), ContDiffOn ℝ n (fun x => ℓ (partialD f I x)) Ω) →
      ∀ (i : Fin d), ∀ x ∈ Ω,
        HasDerivAt (fun t : ℝ => partialD f I (x + t • Pi.single i (1 : ℝ)))
          (partialD f (i :: I) x) 0 := by
    intro I hI i x hx
    exact Classical.epsilon_spec
      (exists_partial hΩ (partialD f I) (fun ℓ ↦ by exact_mod_cast hI ℓ 2) i hx)
  intro I
  induction I with
  | nil => exact ⟨hf, step [] hf⟩
  | cons j I ih =>
    have hw : ∀ (ℓ : StrongDual ℝ E) (n : ℕ),
        ContDiffOn ℝ n (fun x => ℓ (partialD f (j :: I) x)) Ω :=
      fun ℓ n ↦ weak_partial hΩ (partialD f I) (partialD f (j :: I)) ih.1 j (ih.2 j) ℓ n
    exact ⟨hw, step (j :: I) hw⟩

end Sol_VectorValuedHolomorphy_forall_strongDual_contDiffOn_iff_exists_partial_derivatives

open Sol_VectorValuedHolomorphy_forall_strongDual_contDiffOn_iff_exists_partial_derivatives

theorem solution {E : Type*}
    [AddCommGroup E] [Module ℝ E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℝ E]
    [PolynormableSpace ℝ E] [T2Space E] [QuasiCompleteSpace ℝ E] {d : ℕ}
    {Ω : Set (Fin d → ℝ)} (hΩ : IsOpen Ω) (f : (Fin d → ℝ) → E) :
    (∀ (ℓ : StrongDual ℝ E) (n : ℕ), ContDiffOn ℝ n (fun x => ℓ (f x)) Ω) ↔
      ∃ D : List (Fin d) → (Fin d → ℝ) → E, D [] = f ∧ (∀ I, ContinuousOn (D I) Ω) ∧
        ∀ (I : List (Fin d)) (i : Fin d), ∀ x ∈ Ω,
          HasDerivAt (fun t : ℝ => D I (x + t • Pi.single i (1 : ℝ))) (D (i :: I) x) 0 := by
  constructor
  · intro hf
    have hspec := partialD_spec hΩ f hf
    refine ⟨partialD f, rfl, fun I ↦ ?_, fun I i x hx ↦ (hspec I).2 i x hx⟩
    exact continuousOn_of_weak hΩ (partialD f I) fun ℓ ↦ by exact_mod_cast (hspec I).1 ℓ 1
  · rintro ⟨D, hD0, hDc, hDd⟩ ℓ n
    have := weak_of_strong hΩ D hDc hDd ℓ n []
    rwa [hD0] at this
