-- Prove2me | solution 1 for SelfScaledIPM.FuncProx.proposition_3_5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T18:43:31.228998+00:00
-- url     : https://prove2.me/submissions/8ecc87fb-0f07-45e6-8606-129c31492b72

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_FuncProx_Setting
import Definitions.Def_SelfScaledIPM_FuncProx_Measures

open scoped InnerProductSpace

namespace Prop35Aux

open Filter Topology
open SelfScaledIPM.ShortStep

/-! ### Section 1: Cone and Dual Cone Properties -/

private lemma zero_mem_cone {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsProperCone K) :
    (0 : EuclideanSpace ℝ (Fin n)) ∈ K := by
  obtain ⟨x, hx⟩ := hK.2.2.2.2
  simpa using hK.2.2.1 x (interior_subset hx) 0 le_rfl

private lemma cone_add_mem {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsProperCone K)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ K) (hy : y ∈ K) : x + y ∈ K := by
  have hmid : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ K :=
    hK.2.1 hx hy (by norm_num) (by norm_num) (by norm_num)
  have h2 := hK.2.2.1 _ hmid 2 (by norm_num)
  simpa [smul_add, smul_smul] using h2

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

/-! ### Section 2: Smoothness, Symmetry, Homogeneity, and Invertibility of the Hessian -/

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
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (0 : EuclideanSpace ℝ (Fin n)) |> fun _ =>
        ((τ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).hasFDerivAt))
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

private lemma inner_gradient_self_logHom {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior K) :
    ⟪gradient F x, x⟫_ℝ = -ν := by
  have heq : (fun τ : ℝ => F (τ • x)) =ᶠ[𝓝 (1 : ℝ)] (fun τ : ℝ => F x - ν * Real.log τ) := by
    filter_upwards [Ioi_mem_nhds zero_lt_one] with τ hτ
    exact hF.2.2.2.1 x hx τ hτ
  have h1 : HasDerivAt (fun τ : ℝ => F (τ • x)) (fderiv ℝ F x x) (1 : ℝ) := by
    have hline : HasDerivAt (fun τ : ℝ => τ • x) x (1 : ℝ) := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
    have hF1 : HasFDerivAt F (fderiv ℝ F x) ((1 : ℝ) • x) := by
      simpa using (differentiableAt_of_logHom hF hx).hasFDerivAt
    exact hF1.comp_hasDerivAt (1 : ℝ) hline
  have h2 : HasDerivAt (fun τ : ℝ => F x - ν * Real.log τ) (-ν) (1 : ℝ) := by
    have hlog : HasDerivAt Real.log 1 (1 : ℝ) := by
      simpa using Real.hasDerivAt_log (one_ne_zero)
    have hmul := (hlog.const_mul ν).const_sub (F x)
    simpa using hmul
  have hderiv : fderiv ℝ F x x = -ν := by
    rw [← h1.deriv, heq.deriv_eq, h2.deriv]
  rw [inner_gradient_eq_fderiv]
  exact hderiv

private lemma hess_self_eq_neg_gradient {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior K) :
    hess F x x = -gradient F x := by
  have heq : (fun τ : ℝ => gradient F (τ • x)) =ᶠ[𝓝 (1 : ℝ)] (fun τ : ℝ => τ⁻¹ • gradient F x) := by
    filter_upwards [Ioi_mem_nhds zero_lt_one] with τ hτ
    exact gradient_smul_logHom hK hF hx hτ
  have h1 : HasDerivAt (fun τ : ℝ => gradient F (τ • x)) (hess F x x) (1 : ℝ) := by
    have hline : HasDerivAt (fun τ : ℝ => τ • x) x (1 : ℝ) := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
    have hG1 : HasFDerivAt (gradient F) (hess F x) ((1 : ℝ) • x) := by
      simpa [hess] using (gradient_differentiableAt hF hx).hasFDerivAt
    exact hG1.comp_hasDerivAt (1 : ℝ) hline
  have h2 : HasDerivAt (fun τ : ℝ => τ⁻¹ • gradient F x) (-gradient F x) (1 : ℝ) := by
    have hinv : HasDerivAt (fun τ : ℝ => τ⁻¹) (-1) (1 : ℝ) := by
      simpa using hasDerivAt_inv (one_ne_zero : (1 : ℝ) ≠ 0)
    simpa using hinv.smul_const (gradient F x)
  rw [← h1.deriv, heq.deriv_eq, h2.deriv]

private lemma inner_hess_self_self {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior K) :
    ⟪hess F x x, x⟫_ℝ = ν := by
  rw [hess_self_eq_neg_gradient hK hF hx, inner_neg_left, inner_gradient_self_logHom hF hx,
    neg_neg]

/-! ### Section 3: Line Derivatives and Dikin Ellipsoid (Case 1, Left Inequality) -/

private lemma line_contDiffAt {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hF : IsLogHomBarrier K F ν)
    {b a : EuclideanSpace ℝ (Fin n)} {t : ℝ} (ht : b - t • a ∈ interior K) :
    ContDiffAt ℝ 3 (fun s : ℝ => F (b - s • a)) t := by
  have hline : ContDiffAt ℝ 3 (fun s : ℝ => b - s • a) t :=
    contDiffAt_const.sub (contDiffAt_id.smul contDiffAt_const)
  exact (contDiffAt_of_logHom hF ht).comp t hline

private lemma line_deriv_eq {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hF : IsLogHomBarrier K F ν)
    {b a : EuclideanSpace ℝ (Fin n)} {t : ℝ} (ht : b - t • a ∈ interior K) :
    deriv (fun s : ℝ => F (b - s • a)) t = ⟪gradient F (b - t • a), -a⟫_ℝ := by
  have hline : HasDerivAt (fun s : ℝ => b - s • a) (-a) t := by
    have h1 : HasDerivAt (fun s : ℝ => s • a) a t := by
      simpa using (hasDerivAt_id t).smul_const a
    simpa using h1.const_sub b
  have hcomp : HasDerivAt (fun s : ℝ => F (b - s • a)) (fderiv ℝ F (b - t • a) (-a)) t :=
    (differentiableAt_of_logHom hF ht).hasFDerivAt.comp_hasDerivAt t hline
  rw [hcomp.deriv, inner_gradient_eq_fderiv]

private lemma line_iteratedDeriv_two_eq {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hF : IsLogHomBarrier K F ν)
    {b a : EuclideanSpace ℝ (Fin n)} {t : ℝ} (ht : b - t • a ∈ interior K) :
    iteratedDeriv 2 (fun s : ℝ => F (b - s • a)) t = ⟪hess F (b - t • a) a, a⟫_ℝ := by
  have hcont : Continuous (fun s : ℝ => b - s • a) :=
    continuous_const.sub (continuous_id.smul continuous_const)
  have hnhds : {s : ℝ | b - s • a ∈ interior K} ∈ 𝓝 t :=
    hcont.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds ht)
  have heq : deriv (fun s : ℝ => F (b - s • a)) =ᶠ[𝓝 t]
      (fun s : ℝ => ⟪gradient F (b - s • a), -a⟫_ℝ) := by
    filter_upwards [hnhds] with s hs
    exact line_deriv_eq hF hs
  have hline : HasDerivAt (fun s : ℝ => b - s • a) (-a) t := by
    have h1 : HasDerivAt (fun s : ℝ => s • a) a t := by
      simpa using (hasDerivAt_id t).smul_const a
    simpa using h1.const_sub b
  have hgrad : HasDerivAt (fun s : ℝ => gradient F (b - s • a)) (hess F (b - t • a) (-a)) t := by
    have hG : HasFDerivAt (gradient F) (hess F (b - t • a)) (b - t • a) :=
      (gradient_differentiableAt hF ht).hasFDerivAt
    exact hG.comp_hasDerivAt t hline
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) (-a)
  have hinner : HasDerivAt (fun s : ℝ => ⟪gradient F (b - s • a), -a⟫_ℝ)
      ⟪hess F (b - t • a) (-a), -a⟫_ℝ t := by
    have hL : HasDerivAt (fun s : ℝ => L (gradient F (b - s • a)))
        (L (hess F (b - t • a) (-a))) t :=
      L.hasFDerivAt.comp_hasDerivAt t hgrad
    have hfun : (fun s : ℝ => L (gradient F (b - s • a))) =
        (fun s : ℝ => ⟪gradient F (b - s • a), -a⟫_ℝ) := by
      ext s
      simp only [L, InnerProductSpace.toDual_apply_apply]
      exact real_inner_comm _ _
    rw [hfun] at hL
    simpa only [L, InnerProductSpace.toDual_apply_apply, real_inner_comm (-a)] using hL
  rw [iteratedDeriv_succ, iteratedDeriv_one, heq.deriv_eq, hinner.deriv, map_neg,
    inner_neg_left, inner_neg_right, neg_neg]

private lemma line_selfConcordant_bound {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hF : IsLogHomBarrier K F ν)
    {b a : EuclideanSpace ℝ (Fin n)} {t : ℝ} (ht : b - t • a ∈ interior K) :
    |iteratedDeriv 3 (fun s : ℝ => F (b - s • a)) t| ≤
      2 * (iteratedDeriv 2 (fun s : ℝ => F (b - s • a)) t) ^ ((3 : ℝ) / 2) := by
  let φ : ℝ → ℝ := fun s => F (b - s • a)
  have hshift : (fun s : ℝ => F ((b - t • a) + s • (-a))) = (fun s : ℝ => φ (t + s)) := by
    ext s
    simp only [φ]
    congr 1
    rw [add_smul, smul_neg]
    abel
  have hsc := hF.1.2.2 (b - t • a) ht (-a)
  rw [hshift] at hsc
  simpa [iteratedDeriv_comp_const_add, add_zero] using hsc

private lemma dikin_in_interior {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {b a : EuclideanSpace ℝ (Fin n)}
    (hb : b ∈ interior K) (ha : a ≠ 0) :
    0 < lnorm F b a ∧ ∀ t ∈ Set.Ico (0 : ℝ) (lnorm F b a)⁻¹, b - t • a ∈ interior K := by
  have hpos0 : 0 < ⟪hess F b a, a⟫_ℝ := hF.2.2.2.2 b hb a ha
  set r := lnorm F b a with hr_def
  have hr_pos : 0 < r := Real.sqrt_pos.mpr hpos0
  refine ⟨hr_pos, ?_⟩
  by_contra hnot
  push Not at hnot
  let S : Set ℝ := {t : ℝ | t ∈ Set.Ico 0 r⁻¹ ∧ b - t • a ∉ interior K}
  have hS_ne : S.Nonempty := by
    obtain ⟨t, ht, hnt⟩ := hnot
    exact ⟨t, ht, hnt⟩
  have hS_bdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  set T := sInf S
  have hT_lt : T < r⁻¹ := by
    obtain ⟨t₁, ht₁⟩ := hS_ne
    exact lt_of_le_of_lt (csInf_le hS_bdd ht₁) ht₁.1.2
  have hcont_line : Continuous (fun s : ℝ => b - s • a) :=
    continuous_const.sub (continuous_id.smul continuous_const)
  have hT_pos : 0 < T := by
    have h0 : (fun s : ℝ => b - s • a) 0 ∈ interior K := by simpa using hb
    have hnhds : {s : ℝ | b - s • a ∈ interior K} ∈ 𝓝 (0 : ℝ) :=
      hcont_line.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds h0)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
    have hle : ε ≤ T := by
      refine le_csInf hS_ne fun t ht => ?_
      by_contra hlt
      push Not at hlt
      have hdist : dist t 0 < ε := by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1.1]
        exact hlt
      exact ht.2 (hball hdist)
    exact lt_of_lt_of_le hε hle
  have hIco_mem : ∀ t ∈ Set.Ico (0 : ℝ) T, b - t • a ∈ interior K := by
    intro t ht
    by_contra hnt
    have htS : t ∈ S := ⟨⟨ht.1, lt_trans ht.2 hT_lt⟩, hnt⟩
    exact not_le_of_gt ht.2 (csInf_le hS_bdd htS)
  have hT_not_int : b - T • a ∉ interior K := by
    intro hmem
    have hnhds : {s : ℝ | b - s • a ∈ interior K} ∈ 𝓝 T :=
      hcont_line.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hmem)
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
    have hle : T + δ ≤ T := by
      refine le_csInf hS_ne fun t ht => ?_
      by_contra hlt
      push Not at hlt
      have htT : T ≤ t := csInf_le hS_bdd ht
      have hdist : dist t T < δ := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr htT)]
        linarith
      exact ht.2 (hball hdist)
    linarith
  have hT_front : b - T • a ∈ frontier K := by
    refine ⟨?_, hT_not_int⟩
    rw [hK.1.closure_eq]
    have htend : Tendsto (fun t : ℝ => b - t • a) (𝓝[<] T) (𝓝 (b - T • a)) :=
      hcont_line.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ t in 𝓝[<] T, b - t • a ∈ K := by
      filter_upwards [Ioo_mem_nhdsLT hT_pos] with t ht
      exact interior_subset (hIco_mem t ⟨ht.1.le, ht.2⟩)
    exact hK.1.mem_of_tendsto htend hev
  let φ : ℝ → ℝ := fun s => F (b - s • a)
  let g : ℝ → ℝ := iteratedDeriv 2 φ
  let h : ℝ → ℝ := fun s => (Real.sqrt (g s))⁻¹
  let U_line : Set ℝ := {s : ℝ | b - s • a ∈ interior K}
  have hU_open : IsOpen U_line := isOpen_interior.preimage hcont_line
  have hφ_cd : ContDiffOn ℝ 3 φ U_line :=
    hF.1.2.1.comp (contDiffOn_const.sub (contDiffOn_id.smul contDiffOn_const)) (fun _ hs => hs)
  have hφ1_cd : ContDiffOn ℝ 2 (deriv φ) U_line := hφ_cd.deriv_of_isOpen hU_open (by norm_num)
  have hφ2_cd : ContDiffOn ℝ 1 g U_line := by
    have h' : ContDiffOn ℝ 1 (deriv (deriv φ)) U_line := hφ1_cd.deriv_of_isOpen hU_open (by norm_num)
    have hgeq : g = deriv (deriv φ) := by ext s; simp [g, iteratedDeriv_succ]
    rwa [hgeq]
  have hg_pos : ∀ s ∈ Set.Ico (0 : ℝ) T, 0 < g s := by
    intro s hs
    have hmem := hIco_mem s hs
    dsimp only [g, φ]
    rw [line_iteratedDeriv_two_eq hF hmem]
    exact hF.2.2.2.2 _ hmem a ha
  have hg_hasDeriv : ∀ s ∈ Set.Ico (0 : ℝ) T, HasDerivAt g (iteratedDeriv 3 φ s) s := by
    intro s hs
    have hdiff : DifferentiableAt ℝ g s :=
      (hφ2_cd.differentiableOn one_ne_zero).differentiableAt (hU_open.mem_nhds (hIco_mem s hs))
    have hder : deriv g s = iteratedDeriv 3 φ s := by
      simp [g, iteratedDeriv_succ]
    simpa [hder] using hdiff.hasDerivAt
  have hh_hasDeriv : ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivAt h (-(iteratedDeriv 3 φ s / (2 * Real.sqrt (g s))) / (Real.sqrt (g s)) ^ 2) s := by
    intro s hs
    have hgpos := hg_pos s hs
    have hsq : HasDerivAt (fun u => Real.sqrt (g u))
        (iteratedDeriv 3 φ s / (2 * Real.sqrt (g s))) s := by
      have := (hg_hasDeriv s hs).sqrt hgpos.ne'
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
    have hsq_ne : Real.sqrt (g s) ≠ 0 := (Real.sqrt_pos.mpr hgpos).ne'
    exact hsq.inv hsq_ne
  have hh_deriv_ge : ∀ s ∈ Set.Ico (0 : ℝ) T, -1 ≤ deriv h s := by
    intro s hs
    have hgpos := hg_pos s hs
    have hsqrt_pos : 0 < Real.sqrt (g s) := Real.sqrt_pos.mpr hgpos
    have hder := (hh_hasDeriv s hs).deriv
    have hsc := line_selfConcordant_bound hF (hIco_mem s hs)
    have hrpow : (g s) ^ ((3 : ℝ) / 2) = Real.sqrt (g s) * (Real.sqrt (g s)) ^ 2 := by
      have h1 : ((3 : ℝ) / 2) = (1 : ℝ) + (1 : ℝ) / 2 := by norm_num
      rw [h1, Real.rpow_add hgpos, Real.rpow_one, ← Real.sqrt_eq_rpow, Real.sq_sqrt hgpos.le]
      ring
    have habs : |iteratedDeriv 3 φ s| ≤ 2 * Real.sqrt (g s) * (Real.sqrt (g s)) ^ 2 := by
      rw [mul_assoc, ← hrpow]
      exact hsc
    have hden_pos : 0 < 2 * Real.sqrt (g s) * (Real.sqrt (g s)) ^ 2 := by positivity
    rw [hder]
    have hrew : -(iteratedDeriv 3 φ s / (2 * Real.sqrt (g s))) / (Real.sqrt (g s)) ^ 2 =
        -(iteratedDeriv 3 φ s) / (2 * Real.sqrt (g s) * (Real.sqrt (g s)) ^ 2) := by
      ring
    rw [hrew, le_div_iff₀ hden_pos]
    have hle := (abs_le.mp habs).2
    linarith
  have h0_val : h 0 = r⁻¹ := by
    have hmem0 : b - (0 : ℝ) • a ∈ interior K := by simpa using hb
    have hg0 : g 0 = ⟪hess F b a, a⟫_ℝ := by
      simpa [g, φ] using line_iteratedDeriv_two_eq hF hmem0
    simp only [h, hg0, hr_def, lnorm]
  set c := r⁻¹ - T with hc_def
  have hc_pos : 0 < c := sub_pos.mpr hT_lt
  have hg_le : ∀ t ∈ Set.Ico (0 : ℝ) T, g t ≤ c⁻¹ ^ 2 := by
    intro t ht
    have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Ico (0 : ℝ) T := fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
    have hcont : ContinuousOn h (Set.Icc 0 t) :=
      fun s hs => (hh_hasDeriv s (hsub hs)).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ h (interior (Set.Icc 0 t)) :=
      fun s hs => (hh_hasDeriv s (hsub (interior_subset hs))).differentiableAt.differentiableWithinAt
    have hmvt := (convex_Icc (0 : ℝ) t).mul_sub_le_image_sub_of_le_deriv hcont hdiff
      (fun s hs => hh_deriv_ge s (hsub (interior_subset hs))) 0 (Set.left_mem_Icc.mpr ht.1)
      t (Set.right_mem_Icc.mpr ht.1) ht.1
    have hht : c ≤ h t := by
      rw [h0_val] at hmvt
      linarith [ht.2]
    have hsqrt_pos : 0 < Real.sqrt (g t) := Real.sqrt_pos.mpr (hg_pos t ht)
    have hsqrt_le : Real.sqrt (g t) ≤ c⁻¹ := by
      rw [le_inv_comm₀ hsqrt_pos hc_pos]
      exact hht
    have hsq := sq_le_sq' (by linarith [hsqrt_pos, inv_pos.mpr hc_pos]) hsqrt_le
    rwa [Real.sq_sqrt (hg_pos t ht).le] at hsq
  set C₁ := c⁻¹ ^ 2
  set M₁ := deriv φ 0 + C₁ * T
  have hderiv_le : ∀ t ∈ Set.Ico (0 : ℝ) T, deriv φ t ≤ M₁ := by
    intro t ht
    have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Ico (0 : ℝ) T := fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
    have hcd1 : ∀ s ∈ Set.Ico (0 : ℝ) T, HasDerivAt (deriv φ) (g s) s := by
      intro s hs
      have hdiff : DifferentiableAt ℝ (deriv φ) s :=
        (hφ1_cd.differentiableOn (by norm_num)).differentiableAt (hU_open.mem_nhds (hIco_mem s hs))
      have hder : deriv (deriv φ) s = g s := by simp [g, iteratedDeriv_succ]
      simpa [hder] using hdiff.hasDerivAt
    have hcont : ContinuousOn (deriv φ) (Set.Icc 0 t) :=
      fun s hs => (hcd1 s (hsub hs)).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ (deriv φ) (interior (Set.Icc 0 t)) :=
      fun s hs => (hcd1 s (hsub (interior_subset hs))).differentiableAt.differentiableWithinAt
    have hmvt := (convex_Icc (0 : ℝ) t).image_sub_le_mul_sub_of_deriv_le hcont hdiff
      (fun s hs => by
        rw [(hcd1 s (hsub (interior_subset hs))).deriv]
        exact hg_le s (hsub (interior_subset hs)))
      0 (Set.left_mem_Icc.mpr ht.1) t (Set.right_mem_Icc.mpr ht.1) ht.1
    have hC₁_nonneg : 0 ≤ C₁ := sq_nonneg _
    nlinarith [ht.2]
  set M₂ := φ 0 + max M₁ 0 * T
  have hφ_le : ∀ t ∈ Set.Ico (0 : ℝ) T, φ t ≤ M₂ := by
    intro t ht
    have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Ico (0 : ℝ) T := fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
    have hdiff_pt : ∀ s ∈ Set.Ico (0 : ℝ) T, DifferentiableAt ℝ φ s :=
      fun s hs => (line_contDiffAt hF (hIco_mem s hs)).differentiableAt (by norm_num)
    have hcont : ContinuousOn φ (Set.Icc 0 t) :=
      fun s hs => (hdiff_pt s (hsub hs)).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ φ (interior (Set.Icc 0 t)) :=
      fun s hs => (hdiff_pt s (hsub (interior_subset hs))).differentiableWithinAt
    have hmvt := (convex_Icc (0 : ℝ) t).image_sub_le_mul_sub_of_deriv_le hcont hdiff
      (C := max M₁ 0)
      (fun s hs => le_trans (hderiv_le s (hsub (interior_subset hs))) (le_max_left M₁ 0))
      0 (Set.left_mem_Icc.mpr ht.1) t (Set.right_mem_Icc.mpr ht.1) ht.1
    have hM_nonneg : 0 ≤ max M₁ 0 := le_max_right _ _
    nlinarith [ht.2]
  have hbar : Tendsto F (𝓝[interior K] (b - T • a)) atTop := hF.2.1 (b - T • a) hT_front
  have htend_line : Tendsto (fun t : ℝ => b - t • a) (𝓝[<] T) (𝓝[interior K] (b - T • a)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact hcont_line.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT hT_pos] with t ht
      exact hIco_mem t ⟨ht.1.le, ht.2⟩
  have hφ_atTop : Tendsto φ (𝓝[<] T) atTop := hbar.comp htend_line
  have hev_gt : ∀ᶠ t in 𝓝[<] T, M₂ < φ t := hφ_atTop.eventually (eventually_gt_atTop M₂)
  have hev_both : ∀ᶠ t in 𝓝[<] T, t ∈ Set.Ioo (0 : ℝ) T ∧ M₂ < φ t :=
    Filter.Eventually.and (Ioo_mem_nhdsLT hT_pos) hev_gt
  obtain ⟨t, ht_Ioo, ht_gt⟩ := hev_both.exists
  exact not_lt_of_ge (hφ_le t ⟨ht_Ioo.1.le, ht_Ioo.2⟩) ht_gt

private lemma sigma_le_lnorm {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {b : EuclideanSpace ℝ (Fin n)} (hb : b ∈ interior K)
    (a : EuclideanSpace ℝ (Fin n)) :
    sigma K b a ≤ lnorm F b a := by
  have hbdd : BddBelow {β : ℝ | 0 ≤ β ∧ β • b - a ∈ K} := ⟨0, fun β hβ => hβ.1⟩
  by_cases ha : a = 0
  · subst ha
    have h0 : (0 : ℝ) ∈ {β : ℝ | 0 ≤ β ∧ β • b - 0 ∈ K} := by
      refine ⟨le_rfl, ?_⟩
      simpa using zero_mem_cone hK
    exact le_trans (csInf_le hbdd h0) (Real.sqrt_nonneg _)
  · obtain ⟨hr_pos, hIco⟩ := dikin_in_interior hK hF hb ha
    set r := lnorm F b a
    have hcont : Continuous (fun t : ℝ => b - t • a) :=
      continuous_const.sub (continuous_id.smul continuous_const)
    have htend : Tendsto (fun t : ℝ => b - t • a) (𝓝[<] r⁻¹) (𝓝 (b - r⁻¹ • a)) :=
      hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ t in 𝓝[<] r⁻¹, b - t • a ∈ K := by
      filter_upwards [Ioo_mem_nhdsLT (inv_pos.mpr hr_pos)] with t ht
      exact interior_subset (hIco t ⟨ht.1.le, ht.2⟩)
    have hlim : b - r⁻¹ • a ∈ K := hK.1.mem_of_tendsto htend hev
    have hscaled : r • b - a ∈ K := by
      have := hK.2.2.1 _ hlim r hr_pos.le
      rwa [smul_sub, smul_smul, mul_inv_cancel₀ hr_pos.ne', one_smul] at this
    exact csInf_le hbdd ⟨hr_pos.le, hscaled⟩

private lemma absn_le_lnorm {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {b : EuclideanSpace ℝ (Fin n)} (hb : b ∈ interior K)
    (a : EuclideanSpace ℝ (Fin n)) :
    absn K b a ≤ lnorm F b a := by
  refine max_le (sigma_le_lnorm hK hF hb a) ?_
  have hneg : lnorm F b (-a) = lnorm F b a := by
    simp [lnorm, map_neg, inner_neg_left, inner_neg_right]
  rw [← hneg]
  exact sigma_le_lnorm hK hF hb (-a)

/-! ### Section 4: Case 1, Right Inequality -/

private lemma sigma_mem_and_nonneg {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {b : EuclideanSpace ℝ (Fin n)} (hb : b ∈ interior K)
    (a : EuclideanSpace ℝ (Fin n)) :
    0 ≤ sigma K b a ∧ sigma K b a • b - a ∈ K := by
  let S : Set ℝ := {β : ℝ | 0 ≤ β ∧ β • b - a ∈ K}
  have hS_ne : S.Nonempty := by
    have hcont : Continuous (fun t : ℝ => b - t • a) :=
      continuous_const.sub (continuous_id.smul continuous_const)
    have hnhds : {t : ℝ | b - t • a ∈ interior K} ∈ 𝓝 (0 : ℝ) :=
      hcont.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds (by simpa using hb))
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
    have hmem : b - (ε / 2) • a ∈ K := by
      apply interior_subset
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
      linarith
    refine ⟨(ε / 2)⁻¹, (inv_pos.mpr (half_pos hε)).le, ?_⟩
    have hscaled := hK.2.2.1 _ hmem (ε / 2)⁻¹ (inv_pos.mpr (half_pos hε)).le
    rwa [smul_sub, smul_smul, inv_mul_cancel₀ (half_pos hε).ne', one_smul] at hscaled
  have hS_bdd : BddBelow S := ⟨0, fun β hβ => hβ.1⟩
  have hS_closed : IsClosed S := by
    have h1 : IsClosed {β : ℝ | 0 ≤ β} := isClosed_Ici
    have h2 : IsClosed {β : ℝ | β • b - a ∈ K} :=
      hK.1.preimage ((continuous_id.smul continuous_const).sub continuous_const)
    exact h1.inter h2
  have hmem : sInf S ∈ closure S := csInf_mem_closure hS_ne hS_bdd
  rwa [hS_closed.closure_eq] at hmem

private lemma absn_cone_mem {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {b : EuclideanSpace ℝ (Fin n)} (hb : b ∈ interior K)
    (a : EuclideanSpace ℝ (Fin n)) :
    0 ≤ absn K b a ∧ absn K b a • b - a ∈ K ∧ absn K b a • b + a ∈ K := by
  obtain ⟨h1_nn, h1_mem⟩ := sigma_mem_and_nonneg hK hb a
  obtain ⟨h2_nn, h2_mem⟩ := sigma_mem_and_nonneg hK hb (-a)
  set β := absn K b a
  have hβ1 : sigma K b a ≤ β := le_max_left _ _
  have hβ2 : sigma K b (-a) ≤ β := le_max_right _ _
  have hsub : β • b - a ∈ K := by
    have hrew : β • b - a = (β - sigma K b a) • b + (sigma K b a • b - a) := by
      rw [sub_smul]; abel
    rw [hrew]
    exact cone_add_mem hK (hK.2.2.1 b (interior_subset hb) _ (sub_nonneg.mpr hβ1)) h1_mem
  have hadd : β • b + a ∈ K := by
    have hrew : β • b + a = (β - sigma K b (-a)) • b + (sigma K b (-a) • b - (-a)) := by
      rw [sub_smul, sub_neg_eq_add]; abel
    rw [hrew]
    exact cone_add_mem hK (hK.2.2.1 b (interior_subset hb) _ (sub_nonneg.mpr hβ2)) h2_mem
  exact ⟨le_trans h1_nn hβ1, hsub, hadd⟩

private lemma hess_maps_cone_to_dualCone {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsSelfScaledBarrier K F ν) {b : EuclideanSpace ℝ (Fin n)} (hb : b ∈ interior K)
    {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ K) :
    hess F b u ∈ ConvexOptimization.dualCone K := by
  intro v hv
  have htend : Tendsto (fun t : ℝ => ⟪v, hess F b ((1 - t) • u + t • b)⟫_ℝ)
      (𝓝[>] (0 : ℝ)) (𝓝 ⟪v, hess F b u⟫_ℝ) := by
    have hcont : Continuous (fun t : ℝ => ⟪v, hess F b ((1 - t) • u + t • b)⟫_ℝ) :=
      continuous_const.inner ((hess F b).continuous.comp
        (((continuous_const.sub continuous_id).smul continuous_const).add
          (continuous_id.smul continuous_const)))
    have hval : ⟪v, hess F b ((1 - (0 : ℝ)) • u + (0 : ℝ) • b)⟫_ℝ = ⟪v, hess F b u⟫_ℝ := by
      simp
    rw [← hval]
    exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ ⟪v, hess F b ((1 - t) • u + t • b)⟫_ℝ := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
    have hint : (1 - t) • u + t • b ∈ interior K :=
      hK.2.1.combo_self_interior_mem_interior hu hb (by linarith [ht.2]) ht.1 (by ring)
    exact interior_subset (hF.2 b hb _ hint).1 v hv
  exact ge_of_tendsto htend hev

private lemma lnorm_le_sqrt_nu_mul_absn {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hν : 1 ≤ ν)
    (hF : IsSelfScaledBarrier K F ν) {b : EuclideanSpace ℝ (Fin n)} (hb : b ∈ interior K)
    (a : EuclideanSpace ℝ (Fin n)) :
    lnorm F b a ≤ Real.sqrt ν * absn K b a := by
  obtain ⟨hβ_nn, hsub, hadd⟩ := absn_cone_mem hK hb a
  set β := absn K b a
  have hnn : 0 ≤ ⟪β • b - a, hess F b (β • b + a)⟫_ℝ :=
    hess_maps_cone_to_dualCone hK hF hb hadd (β • b - a) hsub
  have hexp : ⟪β • b - a, hess F b (β • b + a)⟫_ℝ =
      β ^ 2 * ⟪hess F b b, b⟫_ℝ - ⟪hess F b a, a⟫_ℝ := by
    rw [map_add, map_smul, inner_sub_left, inner_add_right, inner_add_right,
      inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right]
    simp only [RCLike.conj_to_real]
    have h1 : ⟪b, hess F b b⟫_ℝ = ⟪hess F b b, b⟫_ℝ := real_inner_comm _ _
    have h2 : ⟪b, hess F b a⟫_ℝ = ⟪a, hess F b b⟫_ℝ := by
      rw [← hess_symm hF.1 hb b a, real_inner_comm]
    have h3 : ⟪a, hess F b a⟫_ℝ = ⟪hess F b a, a⟫_ℝ := real_inner_comm _ _
    rw [h1, h2, h3]
    ring
  rw [hexp, inner_hess_self_self hK hF.1 hb] at hnn
  have hle : ⟪hess F b a, a⟫_ℝ ≤ ν * β ^ 2 := by linarith
  calc
    lnorm F b a = Real.sqrt ⟪hess F b a, a⟫_ℝ := rfl
    _ ≤ Real.sqrt (ν * β ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt ν * Real.sqrt (β ^ 2) := Real.sqrt_mul (by linarith) _
    _ = Real.sqrt ν * β := by rw [Real.sqrt_sq hβ_nn]

/-! ### Section 5: Surjectivity of `hess F v` onto `int K*` and `K*` -/

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

private lemma conj_bddAbove_nhds {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {s : EuclideanSpace ℝ (Fin n)}
    (hs : s ∈ interior (ConvexOptimization.dualCone K)) :
    ∃ δ > 0, ∃ M : ℝ, ∀ s' ∈ Metric.ball s δ, conj K F s' ≤ M := by
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
  intro s' hs'
  unfold conj
  have hne : ((fun x => -⟪s', x⟫_ℝ - F x) '' interior K).Nonempty := ⟨_, ⟨y₀, hy₀, rfl⟩⟩
  refine csSup_le hne ?_
  rintro _ ⟨y, hy, rfl⟩
  have hconv := convex_first_order hF hy₀ hy
  have hlow := hs'_lower s' hs' y (interior_subset hy)
  have hcs : |⟪gradient F y₀, y⟫_ℝ| ≤ ‖gradient F y₀‖ * ‖y‖ := abs_real_inner_le_norm _ _
  have hinner_ge : -(r / 4) * ‖y‖ ≤ ⟪gradient F y₀, y⟫_ℝ := by
    have := (abs_le.mp hcs).1
    nlinarith [norm_nonneg y]
  rw [inner_sub_right] at hconv
  linarith

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

/-! ### Section 6: Transfer Under Linear Equiv and Derivatives of `conj K F` -/

private lemma sigma_equiv_eq {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    {C₁ C₂ : Set (EuclideanSpace ℝ (Fin n))} (hC : e '' C₁ = C₂)
    (c u : EuclideanSpace ℝ (Fin n)) :
    sigma C₂ (e c) (e u) = sigma C₁ c u := by
  unfold sigma
  congr 1
  ext β
  simp only [Set.mem_ofPred_eq, ← hC, ← map_smul, ← map_sub]
  exact and_congr_right fun _ => e.injective.mem_set_image

private lemma absn_equiv_eq {n : ℕ}
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    {C₁ C₂ : Set (EuclideanSpace ℝ (Fin n))} (hC : e '' C₁ = C₂)
    (c u : EuclideanSpace ℝ (Fin n)) :
    absn C₂ (e c) (e u) = absn C₁ c u := by
  unfold absn
  rw [sigma_equiv_eq e hC c u, ← map_neg, sigma_equiv_eq e hC c (-u)]

private lemma case1 {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsProperCone K)
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hν : 1 ≤ ν)
    (hF : IsSelfScaledBarrier K F ν) {b : EuclideanSpace ℝ (Fin n)} (hb : b ∈ interior K)
    (a : EuclideanSpace ℝ (Fin n)) :
    absn K b a ≤ lnorm F b a ∧ lnorm F b a ≤ Real.sqrt ν * absn K b a :=
  ⟨absn_le_lnorm hK hF.1 hb a, lnorm_le_sqrt_nu_mul_absn hK hν hF hb a⟩

private lemma case2 {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsProperCone K)
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hν : 1 ≤ ν)
    (hF : IsSelfScaledBarrier K F ν) {b : EuclideanSpace ℝ (Fin n)} (hb : b ∈ interior K)
    (a : EuclideanSpace ℝ (Fin n)) :
    absn (ConvexOptimization.dualCone K) (-gradient F b) a ≤ dnorm F b a ∧
      dnorm F b a ≤ Real.sqrt ν * absn (ConvexOptimization.dualCone K) (-gradient F b) a := by
  obtain ⟨e, he⟩ := hess_equiv hF.1 hb
  have hC : e '' K = ConvexOptimization.dualCone K := by
    have := hess_image_cone_eq hK hF hb
    simpa [← he] using this
  set u := e.symm a
  have heb : e b = -gradient F b := by
    have : e b = hess F b b := by rw [← he]; rfl
    rw [this, hess_self_eq_neg_gradient hK hF.1 hb]
  have habsn : absn (ConvexOptimization.dualCone K) (-gradient F b) a = absn K b u := by
    rw [← heb, ← e.apply_symm_apply a]
    exact absn_equiv_eq e hC b u
  have hdnorm : dnorm F b a = lnorm F b u := by
    unfold dnorm lnorm
    congr 1
    have hinv : (hess F b).inverse = e.symm.toContinuousLinearMap := by
      rw [← he]
      exact ContinuousLinearMap.inverse_equiv e
    rw [hinv]
    change ⟪e.symm a, a⟫_ℝ = ⟪hess F b (e.symm a), e.symm a⟫_ℝ
    have heu : hess F b (e.symm a) = a := by
      rw [← he]
      exact e.apply_symm_apply a
    rw [heu, real_inner_comm]
  rw [habsn, hdnorm]
  exact case1 hK hν hF hb u

private lemma conj_grad_and_hess {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsSelfScaledBarrier K F ν) {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ interior K)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (he : e.toContinuousLinearMap = hess F v)
    {s : EuclideanSpace ℝ (Fin n)} (hs : s ∈ interior (ConvexOptimization.dualCone K)) :
    e.symm s ∈ interior K ∧
      gradient (conj K F) s = e.symm (gradient F (e.symm s)) ∧
      hess (conj K F) s =
        e.symm.toContinuousLinearMap ∘L hess F (e.symm s) ∘L e.symm.toContinuousLinearMap ∧
      (hess (conj K F) s).inverse =
        e.toContinuousLinearMap ∘L (hess F (e.symm s)).inverse ∘L e.toContinuousLinearMap := by
  have hint_eq : e '' interior K = interior (ConvexOptimization.dualCone K) := by
    have := hess_image_interior_eq hK hF hv
    simpa [← he] using this
  have hsymm_e : ∀ u w, ⟪e u, w⟫_ℝ = ⟪u, e w⟫_ℝ := fun u w => by
    have := hess_symm hF.1 hv u w
    simpa [← he] using this
  have hsymm_esymm : ∀ u w, ⟪e.symm u, w⟫_ℝ = ⟪u, e.symm w⟫_ℝ :=
    equiv_symm_selfAdjoint e hsymm_e
  have hmem_int : ∀ y ∈ interior (ConvexOptimization.dualCone K), e.symm y ∈ interior K := by
    intro y hy
    rw [← hint_eq] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    simpa using hx
  have hgrad_all : ∀ y ∈ interior (ConvexOptimization.dualCone K),
      gradient (conj K F) y = e.symm (gradient F (e.symm y)) := by
    intro y hy
    have hxy : e.symm y ∈ interior K := hmem_int y hy
    have heq : conj K F =ᶠ[𝓝 y] (fun z => F (e.symm z) - 2 * F v - ν) := by
      filter_upwards [isOpen_interior.mem_nhds hy] with z hz
      have hxz := hmem_int z hz
      have hez : hess F v (e.symm z) = z := by
        rw [← he]; exact e.apply_symm_apply z
      have h219 := (hF.2 v hv (e.symm z) hxz).2
      rwa [hez] at h219
    have hcomp : HasFDerivAt (fun z => F (e.symm z) - 2 * F v - ν)
        ((fderiv ℝ F (e.symm y)).comp e.symm.toContinuousLinearMap) y := by
      have h1 := (differentiableAt_of_logHom hF.1 hxy).hasFDerivAt.comp y
        e.symm.toContinuousLinearMap.hasFDerivAt
      exact (h1.sub_const (2 * F v)).sub_const ν
    have hfd : fderiv ℝ (conj K F) y =
        (fderiv ℝ F (e.symm y)).comp e.symm.toContinuousLinearMap := by
      rw [heq.fderiv_eq, hcomp.fderiv]
    apply ext_inner_right ℝ
    intro h
    rw [inner_gradient_eq_fderiv, hfd, ContinuousLinearMap.comp_apply,
      ← inner_gradient_eq_fderiv, hsymm_esymm]
    rfl
  have hx : e.symm s ∈ interior K := hmem_int s hs
  have hgrad_s : gradient (conj K F) s = e.symm (gradient F (e.symm s)) := hgrad_all s hs
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
  have hinv_s : (hess (conj K F) s).inverse =
      e.toContinuousLinearMap ∘L (hess F (e.symm s)).inverse ∘L e.toContinuousLinearMap := by
    obtain ⟨ex, hex⟩ := hess_equiv hF.1 hx
    have hex_inv : (hess F (e.symm s)).inverse = ex.symm.toContinuousLinearMap := by
      rw [← hex]
      exact ContinuousLinearMap.inverse_equiv ex
    rw [hhess_s, hex_inv, ← hex]
    apply ContinuousLinearMap.inverse_eq
    · ext u
      simp
    · ext u
      simp
  exact ⟨hx, hgrad_s, hhess_s, hinv_s⟩

private lemma case3 {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsProperCone K)
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hν : 1 ≤ ν)
    (hF : IsSelfScaledBarrier K F ν) {s : EuclideanSpace ℝ (Fin n)}
    (hs : s ∈ interior (ConvexOptimization.dualCone K))
    (a : EuclideanSpace ℝ (Fin n)) :
    absn (ConvexOptimization.dualCone K) s a ≤ lnorm (conj K F) s a ∧
      lnorm (conj K F) s a ≤ Real.sqrt ν * absn (ConvexOptimization.dualCone K) s a := by
  obtain ⟨v, hv⟩ := hK.2.2.2.2
  obtain ⟨e, he⟩ := hess_equiv hF.1 hv
  have hC : e '' K = ConvexOptimization.dualCone K := by
    have := hess_image_cone_eq hK hF hv
    simpa [← he] using this
  have hsymm_e : ∀ u w, ⟪e u, w⟫_ℝ = ⟪u, e w⟫_ℝ := fun u w => by
    have := hess_symm hF.1 hv u w
    simpa [← he] using this
  have hsymm_esymm := equiv_symm_selfAdjoint e hsymm_e
  obtain ⟨hx, _, hhess, _⟩ := conj_grad_and_hess hK hF hv e he hs
  set x := e.symm s
  set u := e.symm a
  have habsn : absn (ConvexOptimization.dualCone K) s a = absn K x u := by
    rw [← e.apply_symm_apply s, ← e.apply_symm_apply a]
    exact absn_equiv_eq e hC x u
  have hlnorm : lnorm (conj K F) s a = lnorm F x u := by
    unfold lnorm
    congr 1
    rw [hhess]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    exact hsymm_esymm (hess F x u) a
  rw [habsn, hlnorm]
  exact case1 hK hν hF hx u

private lemma case4 {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsProperCone K)
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hν : 1 ≤ ν)
    (hF : IsSelfScaledBarrier K F ν) {s : EuclideanSpace ℝ (Fin n)}
    (hs : s ∈ interior (ConvexOptimization.dualCone K))
    (a : EuclideanSpace ℝ (Fin n)) :
    absn K (-gradient (conj K F) s) a ≤ dnorm (conj K F) s a ∧
      dnorm (conj K F) s a ≤ Real.sqrt ν * absn K (-gradient (conj K F) s) a := by
  obtain ⟨v, hv⟩ := hK.2.2.2.2
  obtain ⟨e, he⟩ := hess_equiv hF.1 hv
  have hC : e '' K = ConvexOptimization.dualCone K := by
    have := hess_image_cone_eq hK hF hv
    simpa [← he] using this
  have hsymm_e : ∀ u w, ⟪e u, w⟫_ℝ = ⟪u, e w⟫_ℝ := fun u w => by
    have := hess_symm hF.1 hv u w
    simpa [← he] using this
  obtain ⟨hx, hgrad, _, hinv⟩ := conj_grad_and_hess hK hF hv e he hs
  set x := e.symm s
  set q := e a
  have hegrad : e (-gradient (conj K F) s) = -gradient F x := by
    rw [hgrad, map_neg, e.apply_symm_apply]
  have habsn : absn K (-gradient (conj K F) s) a =
      absn (ConvexOptimization.dualCone K) (-gradient F x) q := by
    rw [← hegrad]
    exact (absn_equiv_eq e hC (-gradient (conj K F) s) a).symm
  have hdnorm : dnorm (conj K F) s a = dnorm F x q := by
    unfold dnorm
    congr 1
    rw [hinv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    exact hsymm_e ((hess F x).inverse q) a
  rw [habsn, hdnorm]
  exact case2 hK hν hF hx q

end Prop35Aux

theorem solution
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : SelfScaledIPM.ShortStep.IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : SelfScaledIPM.ShortStep.IsSelfScaledBarrier K F ν) :
    (∀ b ∈ interior K, ∀ a : EuclideanSpace ℝ (Fin n),
      SelfScaledIPM.ShortStep.absn K b a ≤ SelfScaledIPM.ShortStep.lnorm F b a ∧ SelfScaledIPM.ShortStep.lnorm F b a ≤ Real.sqrt ν * SelfScaledIPM.ShortStep.absn K b a) ∧
    (∀ b ∈ interior K, ∀ a : EuclideanSpace ℝ (Fin n),
      SelfScaledIPM.ShortStep.absn (ConvexOptimization.dualCone K) (-gradient F b) a ≤ SelfScaledIPM.ShortStep.dnorm F b a ∧
        SelfScaledIPM.ShortStep.dnorm F b a ≤ Real.sqrt ν * SelfScaledIPM.ShortStep.absn (ConvexOptimization.dualCone K) (-gradient F b) a) ∧
    (∀ b ∈ interior (ConvexOptimization.dualCone K), ∀ a : EuclideanSpace ℝ (Fin n),
      SelfScaledIPM.ShortStep.absn (ConvexOptimization.dualCone K) b a ≤ SelfScaledIPM.ShortStep.lnorm (SelfScaledIPM.ShortStep.conj K F) b a ∧
        SelfScaledIPM.ShortStep.lnorm (SelfScaledIPM.ShortStep.conj K F) b a ≤ Real.sqrt ν * SelfScaledIPM.ShortStep.absn (ConvexOptimization.dualCone K) b a) ∧
    (∀ b ∈ interior (ConvexOptimization.dualCone K), ∀ a : EuclideanSpace ℝ (Fin n),
      SelfScaledIPM.ShortStep.absn K (-gradient (SelfScaledIPM.ShortStep.conj K F) b) a ≤ SelfScaledIPM.ShortStep.dnorm (SelfScaledIPM.ShortStep.conj K F) b a ∧
        SelfScaledIPM.ShortStep.dnorm (SelfScaledIPM.ShortStep.conj K F) b a ≤ Real.sqrt ν * SelfScaledIPM.ShortStep.absn K (-gradient (SelfScaledIPM.ShortStep.conj K F) b) a) :=
  ⟨fun _ hb a => Prop35Aux.case1 hK hν hF hb a,
   fun _ hb a => Prop35Aux.case2 hK hν hF hb a,
   fun _ hb a => Prop35Aux.case3 hK hν hF hb a,
   fun _ hb a => Prop35Aux.case4 hK hν hF hb a⟩
