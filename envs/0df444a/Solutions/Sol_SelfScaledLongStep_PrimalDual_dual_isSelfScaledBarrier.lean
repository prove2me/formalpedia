-- Prove2me | solution 1 for SelfScaledLongStep.PrimalDual.dual_isSelfScaledBarrier
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T18:54:59.344631+00:00
-- url     : https://prove2.me/submissions/f2d87130-a3c6-4eb9-8a0e-85bc1116bc62

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace DualSelfScaledAux

open Filter Topology

/-! ### Section 1: Cone and Dual Cone Properties -/

private lemma smul_mem_interior_cone {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior K) {τ : ℝ}
    (hτ : 0 < τ) : τ • x ∈ interior K := by
  let h := Homeomorph.smulOfNeZero (α := EuclideanSpace ℝ (Fin n)) τ hτ.ne'
  refine mem_interior.mpr ⟨h '' interior K, ?_, h.isOpenMap _ isOpen_interior, ⟨x, hx, rfl⟩⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hK.2.2.1 y (interior_subset hy) τ hτ.le

private lemma convex_dualCone {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) :
    Convex ℝ (ConvexOptimization.dualCone K) := by
  intro y₁ hy₁ y₂ hy₂ a b ha hb _ x hx
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  exact add_nonneg (mul_nonneg ha (hy₁ x hx)) (mul_nonneg hb (hy₂ x hx))

private lemma isClosed_dualCone {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) :
    IsClosed (ConvexOptimization.dualCone K) := by
  have hEq : ConvexOptimization.dualCone K = ⋂ x ∈ K, {y | 0 ≤ ⟪x, y⟫_ℝ} := by
    ext y
    simp [ConvexOptimization.dualCone]
  rw [hEq]
  refine isClosed_biInter fun x _ => ?_
  exact isClosed_le continuous_const (continuous_const.inner continuous_id)

private lemma smul_mem_dualCone {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    {s : EuclideanSpace ℝ (Fin n)} (hs : s ∈ ConvexOptimization.dualCone K)
    {t : ℝ} (ht : 0 ≤ t) : t • s ∈ ConvexOptimization.dualCone K := by
  intro x hx
  rw [inner_smul_right]
  exact mul_nonneg ht (hs x hx)

/-! ### Section 2: Smoothness, Symmetry, Invertibility, and Homogeneity of `F` -/

private lemma contDiffAt_of_logHom {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hF : IsLogHomBarrier K F ν)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior K) : ContDiffAt ℝ 3 F x :=
  hF.1.2.1.contDiffAt (isOpen_interior.mem_nhds hx)

private lemma differentiableAt_of_logHom {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hF : IsLogHomBarrier K F ν)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior K) : DifferentiableAt ℝ F x :=
  (contDiffAt_of_logHom hF hx).differentiableAt (by norm_num)

private lemma inner_gradient_eq_fderiv {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (x h : EuclideanSpace ℝ (Fin n)) : ⟪gradient F x, h⟫_ℝ = fderiv ℝ F x h := by
  unfold gradient
  exact InnerProductSpace.toDual_symm_apply

private lemma gradient_contDiffAt {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hF : IsLogHomBarrier K F ν)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior K) : ContDiffAt ℝ 2 (gradient F) x := by
  have hfd : ContDiffAt ℝ 2 (fderiv ℝ F) x :=
    (contDiffAt_of_logHom hF hx).fderiv_right (by norm_num)
  have hcomp : gradient F = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm ∘ fderiv ℝ F := by
    ext y
    rfl
  rw [hcomp]
  exact ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearMap.contDiff.contDiffAt).comp x hfd

private lemma gradient_differentiableAt {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hF : IsLogHomBarrier K F ν)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior K) : DifferentiableAt ℝ (gradient F) x :=
  (gradient_contDiffAt hF hx).differentiableAt (by norm_num)

private lemma inner_hess_eq_fderiv_fderiv {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hF : IsLogHomBarrier K F ν)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior K)
    (u v : EuclideanSpace ℝ (Fin n)) :
    ⟪hess F x u, v⟫_ℝ = fderiv ℝ (fderiv ℝ F) x u v := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ F) x :=
    ((contDiffAt_of_logHom hF hx).fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  let L := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearMap
  have hgrad : gradient F = fun y => L (fderiv ℝ F y) := rfl
  have hH : HasFDerivAt (gradient F) (L.comp (fderiv ℝ (fderiv ℝ F) x)) x := by
    rw [hgrad]
    exact L.hasFDerivAt.comp x hfd.hasFDerivAt
  have hhess : hess F x = L.comp (fderiv ℝ (fderiv ℝ F) x) := hH.fderiv
  rw [hhess, ContinuousLinearMap.comp_apply]
  exact InnerProductSpace.toDual_symm_apply

private lemma hess_symm {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hF : IsLogHomBarrier K F ν)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior K)
    (u v : EuclideanSpace ℝ (Fin n)) :
    ⟪hess F x u, v⟫_ℝ = ⟪u, hess F x v⟫_ℝ := by
  rw [inner_hess_eq_fderiv_fderiv hF hx u v, real_inner_comm,
    inner_hess_eq_fderiv_fderiv hF hx v u]
  have hsymm := (contDiffAt_of_logHom hF hx).isSymmSndFDerivAt (by simp; norm_num)
  exact hsymm u v

private lemma hess_equiv {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hF : IsLogHomBarrier K F ν)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior K) :
    ∃ e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      e.toContinuousLinearMap = hess F x := by
  have hinj : Function.Injective (hess F x).toLinearMap := by
    intro u v huv
    have hsub : hess F x (u - v) = 0 := by
      simp only [map_sub, sub_eq_zero]
      exact huv
    by_contra hne
    have hpos := hF.2.2.2.2 x hx (u - v) (sub_ne_zero.mpr hne)
    rw [hsub, inner_zero_left] at hpos
    exact lt_irrefl 0 hpos
  have hbij : Function.Bijective (hess F x).toLinearMap :=
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  let leq : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    LinearEquiv.ofBijective (hess F x).toLinearMap hbij
  refine ⟨leq.toContinuousLinearEquiv, ?_⟩
  ext u
  rfl

private lemma equiv_symm_selfAdjoint {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hsymm : ∀ u v, ⟪e u, v⟫_ℝ = ⟪u, e v⟫_ℝ) :
    ∀ u v, ⟪e.symm u, v⟫_ℝ = ⟪u, e.symm v⟫_ℝ := by
  intro u v
  calc
    ⟪e.symm u, v⟫_ℝ = ⟪e.symm u, e (e.symm v)⟫_ℝ := by rw [e.apply_symm_apply]
    _ = ⟪e (e.symm u), e.symm v⟫_ℝ := (hsymm (e.symm u) (e.symm v)).symm
    _ = ⟪u, e.symm v⟫_ℝ := by rw [e.apply_symm_apply]

private lemma gradient_smul_logHom {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior K)
    {τ : ℝ} (hτ : 0 < τ) :
    gradient F (τ • x) = τ⁻¹ • gradient F x := by
  have heq : (fun y => F (τ • y)) =ᶠ[𝓝 x] (fun y => F y - ν * Real.log τ) := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    exact hF.2.2.2.1 y hy τ hτ
  have h1 : HasFDerivAt (fun y => F (τ • y))
      ((fderiv ℝ F (τ • x)).comp (τ • ContinuousLinearMap.id ℝ _)) x := by
    have hsmul : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => τ • y)
        (τ • ContinuousLinearMap.id ℝ _) x :=
      (τ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).hasFDerivAt
    exact (differentiableAt_of_logHom hF (smul_mem_interior_cone hK hx hτ)).hasFDerivAt.comp x hsmul
  have h2 : HasFDerivAt (fun y => F y - ν * Real.log τ) (fderiv ℝ F x) x :=
    (differentiableAt_of_logHom hF hx).hasFDerivAt.sub_const (ν * Real.log τ)
  have hfd : (fderiv ℝ F (τ • x)).comp (τ • ContinuousLinearMap.id ℝ _) = fderiv ℝ F x := by
    rw [← h1.fderiv, heq.fderiv_eq, h2.fderiv]
  apply ext_inner_right ℝ
  intro h
  rw [inner_smul_left, RCLike.conj_to_real, inner_gradient_eq_fderiv, inner_gradient_eq_fderiv]
  have happ := congrArg (fun L => L h) hfd
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul] at happ
  rw [← happ, inv_mul_cancel_left₀ hτ.ne']

/-! ### Section 3: Surjectivity of `hess F v` onto `int K*` and `K*`, and Bipolarity -/

private lemma convex_first_order {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hF : IsLogHomBarrier K F ν)
    {y₀ y : EuclideanSpace ℝ (Fin n)} (hy₀ : y₀ ∈ interior K) (hy : y ∈ interior K) :
    F y₀ + ⟪gradient F y₀, y - y₀⟫_ℝ ≤ F y := by
  let g : ℝ → ℝ := fun t => F (y₀ + t • (y - y₀))
  have hg : HasDerivAt g ⟪gradient F y₀, y - y₀⟫_ℝ (0 : ℝ) := by
    have hline : HasDerivAt (fun t : ℝ => y₀ + t • (y - y₀)) (y - y₀) (0 : ℝ) := by
      have h1 : HasDerivAt (fun t : ℝ => t • (y - y₀)) (y - y₀) (0 : ℝ) := by
        simpa using (hasDerivAt_id (0 : ℝ)).smul_const (y - y₀)
      simpa using h1.const_add y₀
    have hF0 : HasFDerivAt F (fderiv ℝ F y₀) (y₀ + (0 : ℝ) • (y - y₀)) := by
      simpa using (differentiableAt_of_logHom hF hy₀).hasFDerivAt
    have hcomp : HasDerivAt g (fderiv ℝ F y₀ (y - y₀)) (0 : ℝ) :=
      hF0.comp_hasDerivAt (0 : ℝ) hline
    simpa [inner_gradient_eq_fderiv] using hcomp
  have htend : Tendsto (fun t : ℝ => t⁻¹ * (g t - g 0)) (𝓝[>] (0 : ℝ))
      (𝓝 ⟪gradient F y₀, y - y₀⟫_ℝ) := by
    have hslope := hg.tendsto_slope_zero.mono_left
      (nhdsWithin_mono (0 : ℝ) (show Set.Ioi (0 : ℝ) ⊆ ({0} : Set ℝ)ᶜ from fun t ht => ne_of_gt ht))
    simpa [smul_eq_mul, add_zero] using hslope
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ * (g t - g 0) ≤ F y - F y₀ := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
    have hpt : y₀ + t • (y - y₀) = (1 - t) • y₀ + t • y := by
      rw [sub_smul, one_smul, smul_sub]; abel
    have hconv : F ((1 - t) • y₀ + t • y) ≤ (1 - t) * F y₀ + t * F y := by
      simpa [smul_eq_mul] using hF.1.1.2 hy₀ hy (by linarith [ht.2]) ht.1.le (by ring)
    have hg_le : g t ≤ (1 - t) * F y₀ + t * F y := by
      simp only [g, hpt]
      exact hconv
    have hg0 : g 0 = F y₀ := by simp [g]
    rw [hg0, inv_mul_le_iff₀ ht.1]
    linarith
  have hle := le_of_tendsto htend hev
  linarith

private lemma conj_set_bddAbove_nhds {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {s : EuclideanSpace ℝ (Fin n)}
    (hs : s ∈ interior (ConvexOptimization.dualCone K)) :
    ∃ δ > 0, ∃ M : ℝ, ∀ s' ∈ Metric.ball s δ, ∀ y ∈ interior K, -⟪s', y⟫_ℝ - F y ≤ M := by
  obtain ⟨r, hr_pos, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hs)
  have hball_dual : Metric.ball s r ⊆ ConvexOptimization.dualCone K :=
    hball.trans interior_subset
  have hs_lower : ∀ y ∈ K, (r / 2) * ‖y‖ ≤ ⟪s, y⟫_ℝ := by
    intro y hy
    by_cases hy0 : y = 0
    · simp [hy0]
    · have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
      set w := s - (r / (2 * ‖y‖)) • y
      have hw_ball : w ∈ Metric.ball s r := by
        rw [Metric.mem_ball, dist_eq_norm]
        have hsub : w - s = -((r / (2 * ‖y‖)) • y) := by simp [w]
        rw [hsub, norm_neg, norm_smul, Real.norm_of_nonneg (by positivity)]
        have : r / (2 * ‖y‖) * ‖y‖ = r / 2 := by field_simp [hyn.ne']
        linarith
      have hw_dual : 0 ≤ ⟪y, w⟫_ℝ := hball_dual hw_ball y hy
      have hexp : ⟪y, w⟫_ℝ = ⟪s, y⟫_ℝ - (r / 2) * ‖y‖ := by
        simp only [w, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
          real_inner_comm y s]
        field_simp [hyn.ne']
      linarith
  have hs'_lower : ∀ s' ∈ Metric.ball s (r / 4), ∀ y ∈ K, (r / 4) * ‖y‖ ≤ ⟪s', y⟫_ℝ := by
    intro s' hs' y hy
    have hcs : |⟪s' - s, y⟫_ℝ| ≤ ‖s' - s‖ * ‖y‖ := abs_real_inner_le_norm _ _
    have hdist : ‖s' - s‖ < r / 4 := by simpa [Metric.mem_ball, dist_eq_norm] using hs'
    have h1 := hs_lower y hy
    have h2 : -(r / 4) * ‖y‖ ≤ ⟪s' - s, y⟫_ℝ := by
      have := (abs_le.mp hcs).1
      nlinarith [norm_nonneg y]
    have h3 : ⟪s', y⟫_ℝ = ⟪s, y⟫_ℝ + ⟪s' - s, y⟫_ℝ := by
      rw [inner_sub_left]; ring
    linarith
  obtain ⟨y₁, hy₁⟩ := hK.2.2.2.2
  set τ := 4 * (‖gradient F y₁‖ + 1) / r
  have hτ_pos : 0 < τ := by positivity
  set y₀ := τ • y₁
  have hy₀ : y₀ ∈ interior K := smul_mem_interior_cone hK hy₁ hτ_pos
  have hgrad_le : ‖gradient F y₀‖ ≤ r / 4 := by
    rw [gradient_smul_logHom hK hF hy₁ hτ_pos, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hτ_pos).le]
    have hτ_val : τ⁻¹ * ‖gradient F y₁‖ = (r / 4) * (‖gradient F y₁‖ / (‖gradient F y₁‖ + 1)) := by
      simp only [τ]
      field_simp [hr_pos.ne', (show 0 < ‖gradient F y₁‖ + 1 by positivity).ne']
    rw [hτ_val]
    have hfrac : ‖gradient F y₁‖ / (‖gradient F y₁‖ + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    nlinarith
  refine ⟨r / 4, by positivity, -F y₀ + ⟪gradient F y₀, y₀⟫_ℝ, ?_⟩
  intro s' hs' y hy
  have hconv := convex_first_order hF hy₀ hy
  have hlow := hs'_lower s' hs' y (interior_subset hy)
  have hcs : |⟪gradient F y₀, y⟫_ℝ| ≤ ‖gradient F y₀‖ * ‖y‖ := abs_real_inner_le_norm _ _
  have hinner_ge : -(r / 4) * ‖y‖ ≤ ⟪gradient F y₀, y⟫_ℝ := by
    have := (abs_le.mp hcs).1
    nlinarith [norm_nonneg y]
  rw [inner_sub_right] at hconv
  linarith

private lemma conj_bddAbove_nhds {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {s : EuclideanSpace ℝ (Fin n)}
    (hs : s ∈ interior (ConvexOptimization.dualCone K)) :
    ∃ δ > 0, ∃ M : ℝ, ∀ s' ∈ Metric.ball s δ, conj K F s' ≤ M := by
  obtain ⟨δ, hδ, M, hM⟩ := conj_set_bddAbove_nhds hK hF hs
  refine ⟨δ, hδ, M, fun s' hs' => ?_⟩
  obtain ⟨y₀, hy₀⟩ := hK.2.2.2.2
  have hne : ((fun x => -⟪s', x⟫_ℝ - F x) '' interior K).Nonempty := ⟨_, ⟨y₀, hy₀, rfl⟩⟩
  refine csSup_le hne ?_
  rintro _ ⟨y, hy, rfl⟩
  exact hM s' hs' y hy

private lemma conj_set_bddAbove {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {s : EuclideanSpace ℝ (Fin n)}
    (hs : s ∈ interior (ConvexOptimization.dualCone K)) :
    BddAbove ((fun x => -⟪s, x⟫_ℝ - F x) '' interior K) := by
  obtain ⟨δ, hδ, M, hM⟩ := conj_set_bddAbove_nhds hK hF hs
  refine ⟨M, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hM s (Metric.mem_ball_self hδ) y hy

private lemma hess_image_interior_eq {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsSelfScaledBarrier K F ν) {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ interior K) :
    (hess F v) '' interior K = interior (ConvexOptimization.dualCone K) := by
  obtain ⟨e, he⟩ := hess_equiv hF.1 hv
  let S := interior (ConvexOptimization.dualCone K)
  let U := (hess F v) '' interior K
  have hU_sub : U ⊆ S := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hF.2 v hv x hx).1
  have hU_eq_e : U = e '' interior K := by
    ext y; simp [U, ← he]
  have hU_open : IsOpen U := by
    rw [hU_eq_e]
    exact e.toHomeomorph.isOpenMap _ isOpen_interior
  have hU_ne : U.Nonempty := ⟨hess F v v, v, hv, rfl⟩
  have hS_preconn : IsPreconnected S := (convex_dualCone K).interior.isPreconnected
  have hU_rel_closed : S ∩ closure U ⊆ U := by
    intro s ⟨hsS, hsCl⟩
    set x₀ := e.symm s
    have hx₀_K : x₀ ∈ K := by
      have hcl : e.symm '' closure U = closure (interior K) := by
        have himg : e.symm '' closure U = closure (e.symm '' U) :=
          e.symm.toHomeomorph.image_closure U
        rw [himg, hU_eq_e, Set.image_image]
        simp
      have hx₀_cl : x₀ ∈ closure (interior K) := by
        rw [← hcl]
        exact ⟨s, hsCl, rfl⟩
      exact hK.1.closure_eq ▸ closure_mono interior_subset hx₀_cl
    by_contra hs_not_U
    have hx₀_not_int : x₀ ∉ interior K := by
      intro hx₀_int
      apply hs_not_U
      rw [hU_eq_e]
      exact ⟨x₀, hx₀_int, e.apply_symm_apply s⟩
    have hx₀_front : x₀ ∈ frontier K := ⟨hK.1.closure_eq.symm ▸ hx₀_K, hx₀_not_int⟩
    obtain ⟨δ, hδ, M, hM⟩ := conj_bddAbove_nhds hK hF.1 hsS
    have hbar : Tendsto F (𝓝[interior K] x₀) atTop := hF.1.2.1 x₀ hx₀_front
    have hev_F : ∀ᶠ x in 𝓝[interior K] x₀, M + 2 * F v + ν + 1 < F x :=
      hbar.eventually (eventually_gt_atTop (M + 2 * F v + ν + 1))
    rw [eventually_nhdsWithin_iff] at hev_F
    obtain ⟨V, hV_sub, hV_open, hx₀_V⟩ := mem_nhds_iff.mp hev_F
    let W := e '' V ∩ Metric.ball s δ
    have hW_open : IsOpen W := (e.toHomeomorph.isOpenMap _ hV_open).inter Metric.isOpen_ball
    have hs_W : s ∈ W := ⟨⟨x₀, hx₀_V, e.apply_symm_apply s⟩, Metric.mem_ball_self hδ⟩
    obtain ⟨s', hs'_W, hs'_U⟩ := mem_closure_iff.mp hsCl W hW_open hs_W
    rw [hU_eq_e] at hs'_U
    obtain ⟨x, hx_int, rfl⟩ := hs'_U
    have hx_V : x ∈ V := by
      obtain ⟨x', hx'_V, hx'eq⟩ := hs'_W.1
      have : x' = x := e.injective hx'eq
      rwa [← this]
    have hFx_gt : M + 2 * F v + ν + 1 < F x := hV_sub hx_V hx_int
    have hconj_le : conj K F (e x) ≤ M := hM (e x) hs'_W.2
    have hconj_eq : conj K F (e x) = F x - 2 * F v - ν := by
      have hev_eq : e x = hess F v x := by
        rw [← he]; rfl
      rw [hev_eq]
      exact (hF.2 v hv x hx_int).2
    linarith
  refine subset_antisymm hU_sub ?_
  intro s hs
  by_contra hs_not_U
  have hs_compl : s ∈ (closure U)ᶜ := fun hcl => hs_not_U (hU_rel_closed ⟨hs, hcl⟩)
  have hS_cov : S ⊆ U ∪ (closure U)ᶜ := by
    intro y hy
    by_cases hcl : y ∈ closure U
    · exact Or.inl (hU_rel_closed ⟨hy, hcl⟩)
    · exact Or.inr hcl
  have hSU : (S ∩ U).Nonempty := by
    obtain ⟨y, hy⟩ := hU_ne
    exact ⟨y, hU_sub hy, hy⟩
  have hSV : (S ∩ (closure U)ᶜ).Nonempty := ⟨s, hs, hs_compl⟩
  obtain ⟨y, _, hyU, hyCompl⟩ :=
    hS_preconn U (closure U)ᶜ hU_open isClosed_closure.isOpen_compl hS_cov hSU hSV
  exact hyCompl (subset_closure hyU)

private lemma hess_image_cone_eq {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsSelfScaledBarrier K F ν) {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ interior K) :
    (hess F v) '' K = ConvexOptimization.dualCone K := by
  obtain ⟨e, he⟩ := hess_equiv hF.1 hv
  have hint_eq : e '' interior K = interior (ConvexOptimization.dualCone K) := by
    have := hess_image_interior_eq hK hF hv
    simpa [← he] using this
  have hdual_int_ne : (interior (ConvexOptimization.dualCone K)).Nonempty :=
    ⟨hess F v v, (hF.2 v hv v hv).1⟩
  have hK_cl : closure (interior K) = K := by
    rw [hK.2.1.closure_interior_eq_closure_of_nonempty_interior hK.2.2.2.2, hK.1.closure_eq]
  have hdual_cl : closure (interior (ConvexOptimization.dualCone K)) =
      ConvexOptimization.dualCone K := by
    rw [(convex_dualCone K).closure_interior_eq_closure_of_nonempty_interior hdual_int_ne,
      (isClosed_dualCone K).closure_eq]
  have he_img : e '' K = ConvexOptimization.dualCone K := by
    calc
      e '' K = e '' closure (interior K) := by rw [hK_cl]
      _ = closure (e '' interior K) := e.toHomeomorph.image_closure (interior K)
      _ = closure (interior (ConvexOptimization.dualCone K)) := by rw [hint_eq]
      _ = ConvexOptimization.dualCone K := hdual_cl
  simpa [← he] using he_img

private lemma dualCone_dualCone_eq {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsSelfScaledBarrier K F ν) :
    ConvexOptimization.dualCone (ConvexOptimization.dualCone K) = K := by
  obtain ⟨v, hv⟩ := hK.2.2.2.2
  obtain ⟨e, he⟩ := hess_equiv hF.1 hv
  have hC : e '' K = ConvexOptimization.dualCone K := by
    have := hess_image_cone_eq hK hF hv
    simpa [← he] using this
  have hsymm_e : ∀ u w, ⟪e u, w⟫_ℝ = ⟪u, e w⟫_ℝ := fun u w => by
    have := hess_symm hF.1 hv u w
    simpa [← he] using this
  ext y
  change (∀ s ∈ ConvexOptimization.dualCone K, 0 ≤ ⟪s, y⟫_ℝ) ↔ y ∈ K
  rw [← hC]
  constructor
  · intro hy
    have hey_dual : e y ∈ ConvexOptimization.dualCone K := by
      intro x hx
      rw [← hsymm_e x y]
      exact hy (e x) ⟨x, hx, rfl⟩
    rw [← hC] at hey_dual
    exact e.injective.mem_set_image.mp hey_dual
  · rintro hy _ ⟨x, hx, rfl⟩
    rw [hsymm_e x y]
    have hey_dual : e y ∈ ConvexOptimization.dualCone K := by
      rw [← hC]
      exact ⟨y, hy, rfl⟩
    exact hey_dual x hx

/-! ### Section 4: Representation of `conj K F`, Its Derivatives, and Biconjugation -/

private lemma conj_eq_comp {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsSelfScaledBarrier K F ν) {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ interior K)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (he : e.toContinuousLinearMap = hess F v)
    {s : EuclideanSpace ℝ (Fin n)} (hs : s ∈ interior (ConvexOptimization.dualCone K)) :
    e.symm s ∈ interior K ∧ conj K F s = F (e.symm s) - 2 * F v - ν := by
  have hint_eq : e '' interior K = interior (ConvexOptimization.dualCone K) := by
    have := hess_image_interior_eq hK hF hv
    simpa [← he] using this
  have hx : e.symm s ∈ interior K := by
    rw [← hint_eq] at hs
    obtain ⟨x, hx, rfl⟩ := hs
    simpa using hx
  have hes : hess F v (e.symm s) = s := by
    rw [← he]
    exact e.apply_symm_apply s
  have h219 := (hF.2 v hv (e.symm s) hx).2
  rw [hes] at h219
  exact ⟨hx, h219⟩

private lemma conj_fderiv_grad_hess {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsSelfScaledBarrier K F ν) {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ interior K)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (he : e.toContinuousLinearMap = hess F v)
    {s : EuclideanSpace ℝ (Fin n)} (hs : s ∈ interior (ConvexOptimization.dualCone K)) :
    e.symm s ∈ interior K ∧
      fderiv ℝ (conj K F) s = (fderiv ℝ F (e.symm s)).comp e.symm.toContinuousLinearMap ∧
      gradient (conj K F) s = e.symm (gradient F (e.symm s)) ∧
      hess (conj K F) s =
        e.symm.toContinuousLinearMap ∘L hess F (e.symm s) ∘L e.symm.toContinuousLinearMap := by
  have hsymm_e : ∀ u w, ⟪e u, w⟫_ℝ = ⟪u, e w⟫_ℝ := fun u w => by
    have := hess_symm hF.1 hv u w
    simpa [← he] using this
  have hsymm_esymm : ∀ u w, ⟪e.symm u, w⟫_ℝ = ⟪u, e.symm w⟫_ℝ :=
    equiv_symm_selfAdjoint e hsymm_e
  have hfd_all : ∀ y ∈ interior (ConvexOptimization.dualCone K),
      fderiv ℝ (conj K F) y = (fderiv ℝ F (e.symm y)).comp e.symm.toContinuousLinearMap := by
    intro y hy
    have hxy : e.symm y ∈ interior K := (conj_eq_comp hK hF hv e he hy).1
    have heq : conj K F =ᶠ[𝓝 y] (fun z => F (e.symm z) - 2 * F v - ν) := by
      filter_upwards [isOpen_interior.mem_nhds hy] with z hz
      exact (conj_eq_comp hK hF hv e he hz).2
    have hcomp : HasFDerivAt (fun z => F (e.symm z) - 2 * F v - ν)
        ((fderiv ℝ F (e.symm y)).comp e.symm.toContinuousLinearMap) y := by
      have h1 := (differentiableAt_of_logHom hF.1 hxy).hasFDerivAt.comp y
        e.symm.toContinuousLinearMap.hasFDerivAt
      exact (h1.sub_const (2 * F v)).sub_const ν
    rw [heq.fderiv_eq, hcomp.fderiv]
  have hgrad_all : ∀ y ∈ interior (ConvexOptimization.dualCone K),
      gradient (conj K F) y = e.symm (gradient F (e.symm y)) := by
    intro y hy
    apply ext_inner_right ℝ
    intro h
    rw [inner_gradient_eq_fderiv, hfd_all y hy, ContinuousLinearMap.comp_apply,
      ← inner_gradient_eq_fderiv, hsymm_esymm]
    rfl
  have hx : e.symm s ∈ interior K := (conj_eq_comp hK hF hv e he hs).1
  have hhess_s : hess (conj K F) s =
      e.symm.toContinuousLinearMap ∘L hess F (e.symm s) ∘L e.symm.toContinuousLinearMap := by
    have heq : gradient (conj K F) =ᶠ[𝓝 s] (fun z => e.symm (gradient F (e.symm z))) := by
      filter_upwards [isOpen_interior.mem_nhds hs] with z hz
      exact hgrad_all z hz
    have h1 : HasFDerivAt (fun z => gradient F (e.symm z))
        ((hess F (e.symm s)).comp e.symm.toContinuousLinearMap) s :=
      (gradient_differentiableAt hF.1 hx).hasFDerivAt.comp s
        e.symm.toContinuousLinearMap.hasFDerivAt
    have h2 : HasFDerivAt (fun z => e.symm (gradient F (e.symm z)))
        (e.symm.toContinuousLinearMap.comp ((hess F (e.symm s)).comp e.symm.toContinuousLinearMap)) s :=
      e.symm.toContinuousLinearMap.hasFDerivAt.comp s h1
    change fderiv ℝ (gradient (conj K F)) s = _
    rw [heq.fderiv_eq, h2.fderiv]
  exact ⟨hx, hfd_all s hs, hgrad_all s hs, hhess_s⟩

private lemma sSup_image_add_const (S : Set ℝ) (hS_ne : S.Nonempty) (hS_bdd : BddAbove S) (c : ℝ) :
    sSup ((fun r => r + c) '' S) = sSup S + c := by
  have hne' : ((fun r => r + c) '' S).Nonempty := hS_ne.image _
  have hbdd' : BddAbove ((fun r => r + c) '' S) := by
    obtain ⟨M, hM⟩ := hS_bdd
    refine ⟨M + c, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    linarith [hM hr]
  apply le_antisymm
  · refine csSup_le hne' ?_
    rintro _ ⟨r, hr, rfl⟩
    linarith [le_csSup hS_bdd hr]
  · have hle : sSup S ≤ sSup ((fun r => r + c) '' S) - c := by
      refine csSup_le hS_ne fun r hr => ?_
      have := le_csSup hbdd' ⟨r, hr, rfl⟩
      linarith
    linarith

private lemma conj_conj_eq {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsSelfScaledBarrier K F ν) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior K) :
    conj (ConvexOptimization.dualCone K) (conj K F) x = F x := by
  obtain ⟨v, hv⟩ := hK.2.2.2.2
  obtain ⟨e, he⟩ := hess_equiv hF.1 hv
  have hint_eq : e '' interior K = interior (ConvexOptimization.dualCone K) := by
    have := hess_image_interior_eq hK hF hv
    simpa [← he] using this
  have hsymm_e : ∀ u w, ⟪e u, w⟫_ℝ = ⟪u, e w⟫_ℝ := fun u w => by
    have := hess_symm hF.1 hv u w
    simpa [← he] using this
  have hex_eq : e x = hess F v x := by rw [← he]; rfl
  have hex_int : e x ∈ interior (ConvexOptimization.dualCone K) := by
    rw [hex_eq]
    exact (hF.2 v hv x hx).1
  set S : Set ℝ := (fun y => -⟪e x, y⟫_ℝ - F y) '' interior K
  have hS_ne : S.Nonempty := ⟨_, ⟨v, hv, rfl⟩⟩
  have hS_bdd : BddAbove S := conj_set_bddAbove hK hF.1 hex_int
  have hImg : (fun t => -⟪x, t⟫_ℝ - conj K F t) '' interior (ConvexOptimization.dualCone K) =
      (fun r => r + (2 * F v + ν)) '' S := by
    rw [← hint_eq, Set.image_image]
    ext r
    simp only [Set.mem_image, S]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨-⟪e x, y⟫_ℝ - F y, ⟨y, hy, rfl⟩, ?_⟩
      have hey_eq : e y = hess F v y := by rw [← he]; rfl
      have hconj_ey : conj K F (e y) = F y - 2 * F v - ν := by
        rw [hey_eq]
        exact (hF.2 v hv y hy).2
      rw [hconj_ey, ← hsymm_e x y]
      ring
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨y, hy, ?_⟩
      have hey_eq : e y = hess F v y := by rw [← he]; rfl
      have hconj_ey : conj K F (e y) = F y - 2 * F v - ν := by
        rw [hey_eq]
        exact (hF.2 v hv y hy).2
      rw [hconj_ey, ← hsymm_e x y]
      ring
  change sSup ((fun t => -⟪x, t⟫_ℝ - conj K F t) '' interior (ConvexOptimization.dualCone K)) = F x
  rw [hImg, sSup_image_add_const S hS_ne hS_bdd (2 * F v + ν)]
  have hsup_eq : sSup S = conj K F (e x) := rfl
  rw [hsup_eq, hex_eq, (hF.2 v hv x hx).2]
  ring

/-! ### Section 5: Dual Cone Properness and Dual Self-Scaled Barrier Properties -/

private lemma dualCone_isProperCone {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsSelfScaledBarrier K F ν) :
    IsProperCone (ConvexOptimization.dualCone K) := by
  obtain ⟨v, hv⟩ := hK.2.2.2.2
  obtain ⟨e, he⟩ := hess_equiv hF.1 hv
  have hC : e '' K = ConvexOptimization.dualCone K := by
    have := hess_image_cone_eq hK hF hv
    simpa [← he] using this
  refine ⟨isClosed_dualCone K, convex_dualCone K, fun s hs t ht => smul_mem_dualCone K hs ht, ?_, ?_⟩
  · intro s hs hns
    rw [← hC] at hs hns
    obtain ⟨x, hx, rfl⟩ := hs
    have hnx_img : e (-x) ∈ e '' K := by simpa [map_neg] using hns
    have hnx : -x ∈ K := e.injective.mem_set_image.mp hnx_img
    have hx0 : x = 0 := hK.2.2.2.1 x hx hnx
    rw [hx0, map_zero]
  · exact ⟨hess F v v, (hF.2 v hv v hv).1⟩

private lemma iteratedDeriv_eq_of_eventuallyEq {f g : ℝ → ℝ} {t₀ : ℝ}
    (hfg : f =ᶠ[𝓝 t₀] g) (k : ℕ) :
    iteratedDeriv k f t₀ = iteratedDeriv k g t₀ := by
  induction k generalizing f g with
  | zero =>
    simpa [iteratedDeriv_zero] using hfg.eq_of_nhds
  | succ k ih =>
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    exact ih hfg.deriv

private lemma conj_isSelfConcordantOn {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsSelfScaledBarrier K F ν) :
    ConvexOptimization.IsSelfConcordantOn (interior (ConvexOptimization.dualCone K)) (conj K F) := by
  obtain ⟨v, hv⟩ := hK.2.2.2.2
  obtain ⟨e, he⟩ := hess_equiv hF.1 hv
  have hconv : ConvexOn ℝ (interior (ConvexOptimization.dualCone K)) (conj K F) := by
    refine ⟨(convex_dualCone K).interior, ?_⟩
    intro s₁ hs₁ s₂ hs₂ a b ha hb hab
    have hcomb : a • s₁ + b • s₂ ∈ interior (ConvexOptimization.dualCone K) :=
      (convex_dualCone K).interior hs₁ hs₂ ha hb hab
    obtain ⟨hx₁, hEq₁⟩ := conj_eq_comp hK hF hv e he hs₁
    obtain ⟨hx₂, hEq₂⟩ := conj_eq_comp hK hF hv e he hs₂
    obtain ⟨_, hEqc⟩ := conj_eq_comp hK hF hv e he hcomb
    rw [hEq₁, hEq₂, hEqc, map_add, map_smul, map_smul]
    have hFconv : F (a • e.symm s₁ + b • e.symm s₂) ≤ a * F (e.symm s₁) + b * F (e.symm s₂) := by
      simpa [smul_eq_mul] using hF.1.1.1.2 hx₁ hx₂ ha hb hab
    have hc : (a + b) * (2 * F v + ν) = 2 * F v + ν := by rw [hab, one_mul]
    simp only [smul_eq_mul]
    linarith
  have hcd : ContDiffOn ℝ 3 (conj K F) (interior (ConvexOptimization.dualCone K)) := by
    have hcomp : ContDiffOn ℝ 3 (fun s => F (e.symm s) - 2 * F v - ν)
        (interior (ConvexOptimization.dualCone K)) := by
      have h1 : ContDiffOn ℝ 3 (fun s => F (e.symm s))
          (interior (ConvexOptimization.dualCone K)) :=
        hF.1.1.2.1.comp e.symm.toContinuousLinearMap.contDiff.contDiffOn
          (fun s hs => (conj_eq_comp hK hF hv e he hs).1)
      exact (h1.sub contDiffOn_const).sub contDiffOn_const
    exact hcomp.congr fun s hs => (conj_eq_comp hK hF hv e he hs).2
  refine ⟨hconv, hcd, ?_⟩
  intro s hs h
  have hcont : Continuous (fun t : ℝ => s + t • h) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hnhds : {t : ℝ | s + t • h ∈ interior (ConvexOptimization.dualCone K)} ∈ 𝓝 (0 : ℝ) := by
    have hs0 : s + (0 : ℝ) • h ∈ interior (ConvexOptimization.dualCone K) := by simpa using hs
    exact hcont.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hs0)
  have hev : (fun t : ℝ => conj K F (s + t • h)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t : ℝ => F (e.symm s + t • e.symm h) - (2 * F v + ν)) := by
    filter_upwards [hnhds] with t ht
    have hEq := (conj_eq_comp hK hF hv e he ht).2
    rw [hEq, map_add, map_smul]
    ring
  have hderiv_sub : deriv (fun t : ℝ => F (e.symm s + t • e.symm h) - (2 * F v + ν)) =
      deriv (fun t : ℝ => F (e.symm s + t • e.symm h)) := by
    ext t
    exact deriv_sub_const (2 * F v + ν)
  have hd2 : iteratedDeriv 2 (fun t : ℝ => conj K F (s + t • h)) 0 =
      iteratedDeriv 2 (fun t : ℝ => F (e.symm s + t • e.symm h)) 0 := by
    rw [iteratedDeriv_eq_of_eventuallyEq hev 2, iteratedDeriv_succ', hderiv_sub, ← iteratedDeriv_succ']
  have hd3 : iteratedDeriv 3 (fun t : ℝ => conj K F (s + t • h)) 0 =
      iteratedDeriv 3 (fun t : ℝ => F (e.symm s + t • e.symm h)) 0 := by
    rw [iteratedDeriv_eq_of_eventuallyEq hev 3, iteratedDeriv_succ', hderiv_sub, ← iteratedDeriv_succ']
  rw [hd2, hd3]
  exact hF.1.1.2.2 (e.symm s) (conj_eq_comp hK hF hv e he hs).1 (e.symm h)

private lemma conj_isLogHomBarrier {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsSelfScaledBarrier K F ν) :
    IsLogHomBarrier (ConvexOptimization.dualCone K) (conj K F) ν := by
  obtain ⟨v, hv⟩ := hK.2.2.2.2
  obtain ⟨e, he⟩ := hess_equiv hF.1 hv
  have hC : e '' K = ConvexOptimization.dualCone K := by
    have := hess_image_cone_eq hK hF hv
    simpa [← he] using this
  have hint_eq : e '' interior K = interior (ConvexOptimization.dualCone K) := by
    have := hess_image_interior_eq hK hF hv
    simpa [← he] using this
  have hsymm_e : ∀ u w, ⟪e u, w⟫_ℝ = ⟪u, e w⟫_ℝ := fun u w => by
    have := hess_symm hF.1 hv u w
    simpa [← he] using this
  have hsymm_esymm : ∀ u w, ⟪e.symm u, w⟫_ℝ = ⟪u, e.symm w⟫_ℝ :=
    equiv_symm_selfAdjoint e hsymm_e
  have hKstar : IsProperCone (ConvexOptimization.dualCone K) := dualCone_isProperCone hK hF
  refine ⟨conj_isSelfConcordantOn hK hF, ?_, ?_, ?_, ?_⟩
  · -- Barrier property at frontier K*
    intro s₀ hs₀
    have hs₀_Kstar : s₀ ∈ ConvexOptimization.dualCone K :=
      (isClosed_dualCone K).closure_eq ▸ hs₀.1
    have hs₀_not_int : s₀ ∉ interior (ConvexOptimization.dualCone K) := hs₀.2
    have hx₀_K : e.symm s₀ ∈ K := by
      rw [← hC] at hs₀_Kstar
      obtain ⟨x, hx, hx_eq⟩ := hs₀_Kstar
      have : e.symm s₀ = x := by rw [← hx_eq]; simp
      rwa [this]
    have hx₀_not_int : e.symm s₀ ∉ interior K := by
      intro hx_int
      apply hs₀_not_int
      rw [← hint_eq]
      exact ⟨e.symm s₀, hx_int, e.apply_symm_apply s₀⟩
    have hx₀_front : e.symm s₀ ∈ frontier K := ⟨subset_closure hx₀_K, hx₀_not_int⟩
    have htend_symm : Tendsto e.symm (𝓝[interior (ConvexOptimization.dualCone K)] s₀)
        (𝓝[interior K] (e.symm s₀)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact e.symm.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall fun s hs => (conj_eq_comp hK hF hv e he hs).1
    have htend_F : Tendsto (fun s => F (e.symm s))
        (𝓝[interior (ConvexOptimization.dualCone K)] s₀) atTop :=
      (hF.1.2.1 (e.symm s₀) hx₀_front).comp htend_symm
    have htend_sub : Tendsto (fun s => F (e.symm s) - 2 * F v - ν)
        (𝓝[interior (ConvexOptimization.dualCone K)] s₀) atTop := by
      rw [tendsto_atTop] at htend_F ⊢
      intro b
      filter_upwards [htend_F (b + 2 * F v + ν)] with s hs
      linarith
    refine htend_sub.congr' ?_
    exact eventually_nhdsWithin_of_forall fun s hs => (conj_eq_comp hK hF hv e he hs).2.symm
  · -- Parameter ν inequality
    intro s hs h
    obtain ⟨hx, hfd, _, hhess⟩ := conj_fderiv_grad_hess hK hF hv e he hs
    rw [hfd, hhess]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [hsymm_esymm (hess F (e.symm s) (e.symm h)) h]
    exact hF.1.2.2.1 (e.symm s) hx (e.symm h)
  · -- Logarithmic homogeneity
    intro s hs τ hτ
    have hτs : τ • s ∈ interior (ConvexOptimization.dualCone K) :=
      smul_mem_interior_cone hKstar hs hτ
    obtain ⟨hx, hEqs⟩ := conj_eq_comp hK hF hv e he hs
    obtain ⟨_, hEqτs⟩ := conj_eq_comp hK hF hv e he hτs
    rw [hEqτs, hEqs, map_smul, hF.1.2.2.2.1 (e.symm s) hx τ hτ]
    ring
  · -- Positive definiteness of hess (conj K F) s
    intro s hs h hh
    obtain ⟨hx, _, _, hhess⟩ := conj_fderiv_grad_hess hK hF hv e he hs
    rw [hhess]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [hsymm_esymm (hess F (e.symm s) (e.symm h)) h]
    have heh : e.symm h ≠ 0 := fun h0 => hh (by simpa using congrArg e h0)
    exact hF.1.2.2.2.2 (e.symm s) hx (e.symm h) heh

private lemma conj_isSelfScaledBarrier {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsSelfScaledBarrier K F ν) :
    IsSelfScaledBarrier (ConvexOptimization.dualCone K) (conj K F) ν := by
  obtain ⟨v, hv⟩ := hK.2.2.2.2
  obtain ⟨e, he⟩ := hess_equiv hF.1 hv
  have hbid : ConvexOptimization.dualCone (ConvexOptimization.dualCone K) = K :=
    dualCone_dualCone_eq hK hF
  refine ⟨conj_isLogHomBarrier hK hF, ?_⟩
  intro u hu s hs
  obtain ⟨ha, hEq_u⟩ := conj_eq_comp hK hF hv e he hu
  obtain ⟨hb, hEq_s⟩ := conj_eq_comp hK hF hv e he hs
  obtain ⟨_, _, _, hhess_u⟩ := conj_fderiv_grad_hess hK hF hv e he hu
  have happly : hess (conj K F) u s = e.symm (hess F (e.symm u) (e.symm s)) := by
    rw [hhess_u]
    rfl
  have hy_int : hess F (e.symm u) (e.symm s) ∈ interior (ConvexOptimization.dualCone K) :=
    (hF.2 (e.symm u) ha (e.symm s) hb).1
  obtain ⟨hx_int, hEq_y⟩ := conj_eq_comp hK hF hv e he hy_int
  have hmem : hess (conj K F) u s ∈ interior (ConvexOptimization.dualCone (ConvexOptimization.dualCone K)) := by
    rw [hbid, happly]
    exact hx_int
  refine ⟨hmem, ?_⟩
  rw [happly, conj_conj_eq hK hF hx_int]
  have h219_ab : conj K F (hess F (e.symm u) (e.symm s)) = F (e.symm s) - 2 * F (e.symm u) - ν :=
    (hF.2 (e.symm u) ha (e.symm s) hb).2
  linarith

end DualSelfScaledAux

theorem solution {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν) :
    IsProperCone (ConvexOptimization.dualCone K) ∧
      IsSelfScaledBarrier (ConvexOptimization.dualCone K) (conj K F) ν := by
  let _ := hν
  exact ⟨DualSelfScaledAux.dualCone_isProperCone hK hF,
    DualSelfScaledAux.conj_isSelfScaledBarrier hK hF⟩
