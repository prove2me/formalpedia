-- Prove2me | solution 1 for SelfScaledLongStep.PathFollow.theorem_4_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:05:07.810794+00:00
-- url     : https://prove2.me/submissions/d8948ec4-6ed0-4599-b9fa-e90bb35fca71

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace Thm43Aux

open Filter Topology

/-! ### Section 1: Cone, Dual Cone, and Sigma-Measure Basics -/

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

private lemma add_mem_interior_cone {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {x d : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior K) (hd : d ∈ K) :
    x + d ∈ interior K := by
  let h := Homeomorph.addRight d
  refine mem_interior.mpr ⟨h '' interior K, ?_, h.isOpenMap _ isOpen_interior, ⟨x, hx, rfl⟩⟩
  rintro _ ⟨y, hy, rfl⟩
  exact cone_add_mem hK (interior_subset hy) hd

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

private lemma ne_zero_of_mem_interior_of_ne {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {x v : EuclideanSpace ℝ (Fin n)} (hxv : x ≠ v)
    {a : EuclideanSpace ℝ (Fin n)} (ha : a ∈ interior K) : a ≠ 0 := by
  intro ha0
  subst ha0
  obtain ⟨r, hr_pos, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds ha)
  have hu : x - v ≠ 0 := sub_ne_zero.mpr hxv
  have hun : 0 < ‖x - v‖ := norm_pos_iff.mpr hu
  set t := r / (2 * ‖x - v‖)
  have ht_pos : 0 < t := by positivity
  have hpos_mem : t • (x - v) ∈ K := by
    apply interior_subset
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ht_pos.le]
    have : t * ‖x - v‖ = r / 2 := by simp only [t]; field_simp [hun.ne']
    linarith
  have hneg_mem : -(t • (x - v)) ∈ K := by
    apply interior_subset
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_neg, norm_smul, Real.norm_of_nonneg ht_pos.le]
    have : t * ‖x - v‖ = r / 2 := by simp only [t]; field_simp [hun.ne']
    linarith
  have hzero := hK.2.2.2.1 _ hpos_mem hneg_mem
  rw [smul_eq_zero] at hzero
  exact hzero.elim ht_pos.ne' hu

private lemma dual_interior_coercive {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {s : EuclideanSpace ℝ (Fin n)} (hs : s ∈ interior (ConvexOptimization.dualCone K)) :
    ∃ c > 0, ∀ y ∈ K, c * ‖y‖ ≤ ⟪s, y⟫_ℝ := by
  obtain ⟨r, hr_pos, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hs)
  have hball_dual : Metric.ball s r ⊆ ConvexOptimization.dualCone K :=
    hball.trans interior_subset
  refine ⟨r / 2, half_pos hr_pos, fun y hy => ?_⟩
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

private lemma sigma_pos_of_interior {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {a b : EuclideanSpace ℝ (Fin n)} (ha : a ∈ interior K)
    (hb : b ∈ interior K) (hb0 : b ≠ 0) : 0 < sigma K a b := by
  obtain ⟨hnn, hmem⟩ := sigma_mem_and_nonneg hK ha b
  rcases eq_or_lt_of_le hnn with hzero | hpos
  · exfalso
    rw [← hzero, zero_smul, zero_sub] at hmem
    exact hb0 (hK.2.2.2.1 b (interior_subset hb) hmem)
  · exact hpos

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

private lemma hess_continuousAt {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hF : IsLogHomBarrier K F ν)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior K) : ContinuousAt (hess F) x := by
  have hcd : ContDiffAt ℝ 1 (fderiv ℝ (gradient F)) x :=
    (gradient_contDiffAt hF hx).fderiv_right (by norm_num)
  exact hcd.continuousAt

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

private lemma hess_nonneg {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hF : IsLogHomBarrier K F ν)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior K) (u : EuclideanSpace ℝ (Fin n)) :
    0 ≤ ⟪hess F x u, u⟫_ℝ := by
  by_cases hu : u = 0
  · simp [hu]
  · exact (hF.2.2.2.2 x hx u hu).le

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

private lemma hess_inv_symm {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hF : IsLogHomBarrier K F ν)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior K)
    (u v : EuclideanSpace ℝ (Fin n)) :
    ⟪(hess F x).inverse u, v⟫_ℝ = ⟪u, (hess F x).inverse v⟫_ℝ := by
  obtain ⟨e, he⟩ := hess_equiv hF hx
  have hinv : (hess F x).inverse = e.symm.toContinuousLinearMap := by
    rw [← he]; exact ContinuousLinearMap.inverse_equiv e
  rw [hinv]
  exact equiv_symm_selfAdjoint e (fun a b => by simpa [← he] using hess_symm hF hx a b) u v

private lemma hess_inv_pos {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hF : IsLogHomBarrier K F ν)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior K)
    {u : EuclideanSpace ℝ (Fin n)} (hu : u ≠ 0) :
    0 < ⟪(hess F x).inverse u, u⟫_ℝ := by
  obtain ⟨e, he⟩ := hess_equiv hF hx
  have hinv : (hess F x).inverse = e.symm.toContinuousLinearMap := by
    rw [← he]; exact ContinuousLinearMap.inverse_equiv e
  rw [hinv]
  change 0 < ⟪e.symm u, u⟫_ℝ
  have hne : e.symm u ≠ 0 := by
    intro h0
    apply hu
    calc u = e (e.symm u) := (e.apply_symm_apply u).symm
      _ = e 0 := by rw [h0]
      _ = 0 := map_zero e
  have hpos := hF.2.2.2.2 x hx (e.symm u) hne
  have heu : hess F x (e.symm u) = u := by rw [← he]; exact e.apply_symm_apply u
  rwa [heu, real_inner_comm] at hpos

private lemma hess_inv_nonneg {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hF : IsLogHomBarrier K F ν)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior K) (u : EuclideanSpace ℝ (Fin n)) :
    0 ≤ ⟪(hess F x).inverse u, u⟫_ℝ := by
  by_cases hu : u = 0
  · simp [hu]
  · exact (hess_inv_pos hF hx hu).le

private lemma hess_apply_inv {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hF : IsLogHomBarrier K F ν)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior K) (u : EuclideanSpace ℝ (Fin n)) :
    hess F x ((hess F x).inverse u) = u := by
  obtain ⟨e, he⟩ := hess_equiv hF hx
  have hinv : (hess F x).inverse = e.symm.toContinuousLinearMap := by
    rw [← he]; exact ContinuousLinearMap.inverse_equiv e
  rw [hinv, ← he]
  exact e.apply_symm_apply u

private lemma inv_apply_hess {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hF : IsLogHomBarrier K F ν)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior K) (u : EuclideanSpace ℝ (Fin n)) :
    (hess F x).inverse (hess F x u) = u := by
  obtain ⟨e, he⟩ := hess_equiv hF hx
  have hinv : (hess F x).inverse = e.symm.toContinuousLinearMap := by
    rw [← he]; exact ContinuousLinearMap.inverse_equiv e
  rw [hinv, ← he]
  exact e.symm_apply_apply u

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

private lemma hess_smul_logHom {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior K)
    {τ : ℝ} (hτ : 0 < τ) (u : EuclideanSpace ℝ (Fin n)) :
    hess F (τ • x) u = (τ ^ 2)⁻¹ • hess F x u := by
  have heq : (fun y => gradient F (τ • y)) =ᶠ[𝓝 x] (fun y => τ⁻¹ • gradient F y) := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    exact gradient_smul_logHom hK hF hy hτ
  have h1 : HasFDerivAt (fun y => gradient F (τ • y))
      ((hess F (τ • x)).comp (τ • ContinuousLinearMap.id ℝ _)) x := by
    have hsmul : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => τ • y)
        (τ • ContinuousLinearMap.id ℝ _) x :=
      (τ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).hasFDerivAt
    exact (gradient_differentiableAt hF (smul_mem_interior_cone hK hx hτ)).hasFDerivAt.comp x hsmul
  have h2 : HasFDerivAt (fun y => τ⁻¹ • gradient F y) (τ⁻¹ • hess F x) x :=
    (gradient_differentiableAt hF hx).hasFDerivAt.const_smul τ⁻¹
  have hfd : (hess F (τ • x)).comp (τ • ContinuousLinearMap.id ℝ _) = τ⁻¹ • hess F x := by
    rw [← h1.fderiv, heq.fderiv_eq, h2.fderiv]
  have happ := congrArg (fun L => L u) hfd
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul] at happ
  calc
    hess F (τ • x) u = τ⁻¹ • (τ • hess F (τ • x) u) := by
      rw [smul_smul, inv_mul_cancel₀ hτ.ne', one_smul]
    _ = τ⁻¹ • (τ⁻¹ • hess F x u) := by rw [happ]
    _ = (τ ^ 2)⁻¹ • hess F x u := by rw [smul_smul, sq, mul_inv]

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
      simpa using Real.hasDerivAt_log one_ne_zero
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

private lemma gradient_monotone {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hF : IsLogHomBarrier K F ν)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior K) (hy : y ∈ interior K) :
    0 ≤ ⟪gradient F x - gradient F y, x - y⟫_ℝ := by
  have h1 := convex_first_order hF hx hy
  have h2 := convex_first_order hF hy hx
  have h3 : ⟪gradient F x, y - x⟫_ℝ = -⟪gradient F x, x - y⟫_ℝ := by
    rw [← inner_neg_right, neg_sub]
  rw [inner_sub_left]
  linarith

/-! ### Section 3: Surjectivity of `hess F v` onto `int K*` and Derivatives of `conj K F` -/

private lemma conj_bddAbove_nhds {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {s : EuclideanSpace ℝ (Fin n)}
    (hs : s ∈ interior (ConvexOptimization.dualCone K)) :
    ∃ δ > 0, ∃ M : ℝ, ∀ s' ∈ Metric.ball s δ, conj K F s' ≤ M := by
  obtain ⟨c, hc_pos, hs_lower⟩ := dual_interior_coercive hs
  have hs'_lower : ∀ s' ∈ Metric.ball s (c / 2), ∀ y ∈ K, (c / 2) * ‖y‖ ≤ ⟪s', y⟫_ℝ := by
    intro s' hs' y hy
    have hcs : |⟪s' - s, y⟫_ℝ| ≤ ‖s' - s‖ * ‖y‖ := abs_real_inner_le_norm _ _
    have hdist : ‖s' - s‖ < c / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hs'
    have h1 := hs_lower y hy
    have h2 : -(c / 2) * ‖y‖ ≤ ⟪s' - s, y⟫_ℝ := by
      have := (abs_le.mp hcs).1
      nlinarith [norm_nonneg y]
    have h3 : ⟪s', y⟫_ℝ = ⟪s, y⟫_ℝ + ⟪s' - s, y⟫_ℝ := by
      rw [inner_sub_left]; ring
    linarith
  obtain ⟨y₁, hy₁⟩ := hK.2.2.2.2
  set τ := 2 * (‖gradient F y₁‖ + 1) / c
  have hτ_pos : 0 < τ := by positivity
  set y₀ := τ • y₁
  have hy₀ : y₀ ∈ interior K := smul_mem_interior_cone hK hy₁ hτ_pos
  have hgrad_le : ‖gradient F y₀‖ ≤ c / 2 := by
    rw [gradient_smul_logHom hK hF hy₁ hτ_pos, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hτ_pos).le]
    have hτ_val : τ⁻¹ * ‖gradient F y₁‖ = (c / 2) * (‖gradient F y₁‖ / (‖gradient F y₁‖ + 1)) := by
      simp only [τ]
      field_simp [hc_pos.ne', (show 0 < ‖gradient F y₁‖ + 1 by positivity).ne']
    rw [hτ_val]
    have hfrac : ‖gradient F y₁‖ / (‖gradient F y₁‖ + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    nlinarith
  refine ⟨c / 2, by positivity, -F y₀ + ⟪gradient F y₀, y₀⟫_ℝ, ?_⟩
  intro s' hs'
  unfold conj
  have hne : ((fun x => -⟪s', x⟫_ℝ - F x) '' interior K).Nonempty := ⟨_, ⟨y₀, hy₀, rfl⟩⟩
  refine csSup_le hne ?_
  rintro _ ⟨y, hy, rfl⟩
  have hconv := convex_first_order hF hy₀ hy
  have hlow := hs'_lower s' hs' y (interior_subset hy)
  have hcs : |⟪gradient F y₀, y⟫_ℝ| ≤ ‖gradient F y₀‖ * ‖y‖ := abs_real_inner_le_norm _ _
  have hinner_ge : -(c / 2) * ‖y‖ ≤ ⟪gradient F y₀, y⟫_ℝ := by
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
      have hev_eq : e x = hess F v x := by rw [← he]; rfl
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

private lemma conj_grad_hess_at_hess {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsSelfScaledBarrier K F ν) {w x : EuclideanSpace ℝ (Fin n)}
    (hw : w ∈ interior K) (hx : x ∈ interior K) :
    gradient (conj K F) (hess F w x) = (hess F w).inverse (gradient F x) ∧
      hess (conj K F) (hess F w x) =
        (hess F w).inverse ∘L hess F x ∘L (hess F w).inverse := by
  obtain ⟨e, he⟩ := hess_equiv hF.1 hw
  have hinv : (hess F w).inverse = e.symm.toContinuousLinearMap := by
    rw [← he]; exact ContinuousLinearMap.inverse_equiv e
  have hint_eq : e '' interior K = interior (ConvexOptimization.dualCone K) := by
    have := hess_image_interior_eq hK hF hw
    simpa [← he] using this
  have hsymm_e : ∀ u z, ⟪e u, z⟫_ℝ = ⟪u, e z⟫_ℝ := fun u z => by
    have := hess_symm hF.1 hw u z
    simpa [← he] using this
  have hsymm_esymm : ∀ u z, ⟪e.symm u, z⟫_ℝ = ⟪u, e.symm z⟫_ℝ :=
    equiv_symm_selfAdjoint e hsymm_e
  have hmem_int : ∀ y ∈ interior (ConvexOptimization.dualCone K), e.symm y ∈ interior K := by
    intro y hy
    rw [← hint_eq] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    simpa using hz
  have hgrad_all : ∀ y ∈ interior (ConvexOptimization.dualCone K),
      gradient (conj K F) y = e.symm (gradient F (e.symm y)) := by
    intro y hy
    have hxy : e.symm y ∈ interior K := hmem_int y hy
    have heq : conj K F =ᶠ[𝓝 y] (fun z => F (e.symm z) - 2 * F w - ν) := by
      filter_upwards [isOpen_interior.mem_nhds hy] with z hz
      have hxz := hmem_int z hz
      have hez : hess F w (e.symm z) = z := by
        rw [← he]; exact e.apply_symm_apply z
      have h219 := (hF.2 w hw (e.symm z) hxz).2
      rwa [hez] at h219
    have hcomp : HasFDerivAt (fun z => F (e.symm z) - 2 * F w - ν)
        ((fderiv ℝ F (e.symm y)).comp e.symm.toContinuousLinearMap) y := by
      have h1 := (differentiableAt_of_logHom hF.1 hxy).hasFDerivAt.comp y
        e.symm.toContinuousLinearMap.hasFDerivAt
      exact (h1.sub_const (2 * F w)).sub_const ν
    have hfd : fderiv ℝ (conj K F) y =
        (fderiv ℝ F (e.symm y)).comp e.symm.toContinuousLinearMap := by
      rw [heq.fderiv_eq, hcomp.fderiv]
    apply ext_inner_right ℝ
    intro h
    rw [inner_gradient_eq_fderiv, hfd, ContinuousLinearMap.comp_apply,
      ← inner_gradient_eq_fderiv, hsymm_esymm]
    rfl
  set s := hess F w x
  have hs : s ∈ interior (ConvexOptimization.dualCone K) := (hF.2 w hw x hx).1
  have hes : e.symm s = x := by
    change e.symm (hess F w x) = x
    rw [← he]
    exact e.symm_apply_apply x
  have hgrad_s : gradient (conj K F) s = (hess F w).inverse (gradient F x) := by
    rw [hgrad_all s hs, hes, hinv]
    rfl
  have hhess_s : hess (conj K F) s =
      (hess F w).inverse ∘L hess F x ∘L (hess F w).inverse := by
    have heq : gradient (conj K F) =ᶠ[𝓝 s] (fun z => e.symm (gradient F (e.symm z))) := by
      filter_upwards [isOpen_interior.mem_nhds hs] with z hz
      exact hgrad_all z hz
    have h1 : HasFDerivAt (fun z => gradient F (e.symm z))
        ((hess F (e.symm s)).comp e.symm.toContinuousLinearMap) s :=
      (gradient_differentiableAt hF.1 (hes ▸ hx)).hasFDerivAt.comp s
        e.symm.toContinuousLinearMap.hasFDerivAt
    have h2 : HasFDerivAt (fun z => e.symm (gradient F (e.symm z)))
        (e.symm.toContinuousLinearMap.comp ((hess F (e.symm s)).comp e.symm.toContinuousLinearMap)) s :=
      e.symm.toContinuousLinearMap.hasFDerivAt.comp s h1
    change fderiv ℝ (gradient (conj K F)) s = _
    rw [heq.fderiv_eq, h2.fderiv, hes, hinv]
  exact ⟨hgrad_s, hhess_s⟩

/-! ### Section 4: Positive Definite Square Root and Injectivity of `v ↦ hess F v x` -/

private lemma spd_exists_sqrt {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH_symm : H.toLinearMap.IsSymmetric)
    (hH_pos : ∀ u : EuclideanSpace ℝ (Fin n), u ≠ 0 → 0 < ⟪H u, u⟫_ℝ) :
    ∃ S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      (∀ u v, ⟪S u, v⟫_ℝ = ⟪u, S v⟫_ℝ) ∧ S.comp S = H ∧ Function.Bijective S := by
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  let b := hH_symm.eigenvectorBasis hfin
  let μ := hH_symm.eigenvalues hfin
  have hμ_pos : ∀ i : Fin n, 0 < μ i := by
    intro i
    have hbi_ne : b i ≠ 0 := by
      intro h0
      have hn1 : ‖b i‖ = 1 := b.orthonormal.1 i
      rw [h0, norm_zero] at hn1
      norm_num at hn1
    have hpos := hH_pos (b i) hbi_ne
    have heig : H (b i) = μ i • b i := hH_symm.apply_eigenvectorBasis hfin i
    rw [heig, inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq,
      b.orthonormal.1 i] at hpos
    simpa using hpos
  let S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ∑ i : Fin n, (Real.sqrt (μ i)) • ContinuousLinearMap.smulRight
      ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) (b i)) (b i)
  have hS_basis : ∀ j : Fin n, S (b j) = (Real.sqrt (μ j)) • b j := by
    intro j
    simp only [S, FunLike.coe_sum, Finset.sum_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, InnerProductSpace.toDual_apply_apply]
    rw [Finset.sum_eq_single j]
    · rw [real_inner_self_eq_norm_sq, b.orthonormal.1 j, one_pow, one_smul]
    · intro i _ hij
      rw [b.orthonormal.2 hij, zero_smul, smul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hS_symm : ∀ u v, ⟪S u, v⟫_ℝ = ⟪u, S v⟫_ℝ := by
    intro u v
    simp only [S, FunLike.coe_sum, Finset.sum_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, InnerProductSpace.toDual_apply_apply, sum_inner,
      inner_sum, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm u (b i)]
    ring
  have hS_sq : S.comp S = H := by
    apply ContinuousLinearMap.coe_injective
    exact b.toBasis.ext fun j => by
      change S (S (b j)) = H (b j)
      rw [hS_basis j, map_smul, hS_basis j, smul_smul, Real.mul_self_sqrt (hμ_pos j).le]
      exact (hH_symm.apply_eigenvectorBasis hfin j).symm
  have hS_inj : Function.Injective S := by
    intro u v huv
    have hsub : S (u - v) = 0 := by rw [map_sub, huv, sub_self]
    have hH0 : H (u - v) = 0 := by
      have := congrArg (fun L => L (u - v)) hS_sq
      simp only [ContinuousLinearMap.comp_apply] at this
      rw [← this, hsub, map_zero]
    by_contra hne
    have hpos := hH_pos (u - v) (sub_ne_zero.mpr hne)
    rw [hH0, inner_zero_left] at hpos
    exact lt_irrefl 0 hpos
  have hS_bij : Function.Bijective S :=
    ⟨hS_inj, LinearMap.injective_iff_surjective.mp (show Function.Injective S.toLinearMap from hS_inj)⟩
  exact ⟨S, hS_symm, hS_sq, hS_bij⟩

private lemma spd_sq_eq_imp_eq {n : ℕ}
    (A₁ A₂ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA₁_symm : A₁.toLinearMap.IsSymmetric)
    (hA₁_pos : ∀ u : EuclideanSpace ℝ (Fin n), u ≠ 0 → 0 < ⟪A₁ u, u⟫_ℝ)
    (hA₂_nonneg : ∀ u : EuclideanSpace ℝ (Fin n), 0 ≤ ⟪A₂ u, u⟫_ℝ)
    (hsq : A₁.comp A₁ = A₂.comp A₂) : A₁ = A₂ := by
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  let b := hA₁_symm.eigenvectorBasis hfin
  let μ := hA₁_symm.eigenvalues hfin
  have hμ_pos : ∀ i : Fin n, 0 < μ i := by
    intro i
    have hbi_ne : b i ≠ 0 := by
      intro h0
      have hn1 : ‖b i‖ = 1 := b.orthonormal.1 i
      rw [h0, norm_zero] at hn1
      norm_num at hn1
    have hpos := hA₁_pos (b i) hbi_ne
    have heig : A₁ (b i) = μ i • b i := hA₁_symm.apply_eigenvectorBasis hfin i
    rw [heig, inner_smul_left, RCLike.conj_to_real, real_inner_self_eq_norm_sq,
      b.orthonormal.1 i] at hpos
    simpa using hpos
  have heq_basis : ∀ i : Fin n, A₁ (b i) = A₂ (b i) := by
    intro i
    set w := A₂ (b i) - μ i • b i
    have hA₂w : A₂ w + μ i • w = 0 := by
      have hsqi : A₂ (A₂ (b i)) = A₁ (A₁ (b i)) := by
        have := congrArg (fun L => L (b i)) hsq
        simpa [ContinuousLinearMap.comp_apply] using this.symm
      have heig : A₁ (b i) = μ i • b i := hA₁_symm.apply_eigenvectorBasis hfin i
      have hA₁sq : A₁ (A₁ (b i)) = (μ i * μ i) • b i := by
        rw [heig, map_smul, heig, smul_smul]
      simp only [w, map_sub, map_smul, smul_sub, smul_smul, hsqi, hA₁sq]
      abel
    have hinner0 : ⟪A₂ w, w⟫_ℝ + μ i * ⟪w, w⟫_ℝ = 0 := by
      have h0 : ⟪A₂ w + μ i • w, w⟫_ℝ = 0 := by rw [hA₂w, inner_zero_left]
      rwa [inner_add_left, inner_smul_left, RCLike.conj_to_real] at h0
    have hww_nn : 0 ≤ ⟪w, w⟫_ℝ := real_inner_self_nonneg
    have hA₂_nn : 0 ≤ ⟪A₂ w, w⟫_ℝ := hA₂_nonneg w
    have hww0 : ⟪w, w⟫_ℝ = 0 := by nlinarith [hμ_pos i]
    have hw0 : w = 0 := inner_self_eq_zero.mp hww0
    have hA₂bi : A₂ (b i) = μ i • b i := sub_eq_zero.mp hw0
    rw [hA₂bi]
    exact hA₁_symm.apply_eigenvectorBasis hfin i
  apply ContinuousLinearMap.coe_injective
  exact b.toBasis.ext fun i => heq_basis i

private lemma hess_apply_injective {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsSelfScaledBarrier K F ν) {v₁ v₂ x : EuclideanSpace ℝ (Fin n)}
    (hv₁ : v₁ ∈ interior K) (hv₂ : v₂ ∈ interior K) (hx : x ∈ interior K)
    (heq : hess F v₁ x = hess F v₂ x) : v₁ = v₂ := by
  have hc₁ := (conj_grad_hess_at_hess hK hF hv₁ hx).2
  have hc₂ := (conj_grad_hess_at_hess hK hF hv₂ hx).2
  rw [heq] at hc₁
  have hcomp_eq :
      (hess F v₁).inverse ∘L hess F x ∘L (hess F v₁).inverse =
      (hess F v₂).inverse ∘L hess F x ∘L (hess F v₂).inverse :=
    hc₁.symm.trans hc₂
  obtain ⟨S, hS_symm, hS_sq, hS_bij⟩ :=
    spd_exists_sqrt (hess F x) (fun u w => hess_symm hF.1 hx u w) (hF.1.2.2.2.2 x hx)
  let M₁ := (hess F v₁).inverse
  let M₂ := (hess F v₂).inverse
  let A₁ := S ∘L M₁ ∘L S
  let A₂ := S ∘L M₂ ∘L S
  have hA₁_symm : A₁.toLinearMap.IsSymmetric := by
    intro u w
    change ⟪S (M₁ (S u)), w⟫_ℝ = ⟪u, S (M₁ (S w))⟫_ℝ
    rw [hS_symm (M₁ (S u)) w, hess_inv_symm hF.1 hv₁ (S u) (S w), ← hS_symm u (M₁ (S w))]
  have hA₁_pos : ∀ u, u ≠ 0 → 0 < ⟪A₁ u, u⟫_ℝ := by
    intro u hu
    change 0 < ⟪S (M₁ (S u)), u⟫_ℝ
    rw [hS_symm (M₁ (S u)) u]
    have hSu : S u ≠ 0 := by
      intro h0
      exact hu (hS_bij.1 (h0.trans (map_zero S).symm))
    exact hess_inv_pos hF.1 hv₁ hSu
  have hA₂_nn : ∀ u, 0 ≤ ⟪A₂ u, u⟫_ℝ := by
    intro u
    change 0 ≤ ⟪S (M₂ (S u)), u⟫_ℝ
    rw [hS_symm (M₂ (S u)) u]
    exact hess_inv_nonneg hF.1 hv₂ (S u)
  have hAsq : A₁.comp A₁ = A₂.comp A₂ := by
    refine ContinuousLinearMap.ext fun u => ?_
    simp only [A₁, A₂, ContinuousLinearMap.comp_apply]
    have hSS : ∀ z, S (S z) = hess F x z := fun z => by
      have := congrArg (fun L => L z) hS_sq
      simpa [ContinuousLinearMap.comp_apply] using this
    rw [hSS (M₁ (S u)), hSS (M₂ (S u))]
    have hm := congrArg (fun L => L (S u)) hcomp_eq
    simp only [ContinuousLinearMap.comp_apply] at hm
    exact congrArg S hm
  have hA_eq : A₁ = A₂ := spd_sq_eq_imp_eq A₁ A₂ hA₁_symm hA₁_pos hA₂_nn hAsq
  have hM_eq : M₁ = M₂ := by
    refine ContinuousLinearMap.ext fun u => ?_
    obtain ⟨w, rfl⟩ := hS_bij.2 u
    have := congrArg (fun L => L w) hA_eq
    simp only [A₁, A₂, ContinuousLinearMap.comp_apply] at this
    exact hS_bij.1 this
  have hhess_eq : hess F v₁ = hess F v₂ := by
    refine ContinuousLinearMap.ext fun u => ?_
    have h1 := hess_apply_inv hF.1 hv₁ (hess F v₂ u)
    rw [show (hess F v₁).inverse = (hess F v₂).inverse from hM_eq] at h1
    rw [inv_apply_hess hF.1 hv₂ u] at h1
    exact h1
  have hgrad_diff : gradient F v₁ - gradient F v₂ = -hess F v₁ (v₁ - v₂) := by
    have hg1 : gradient F v₁ = -hess F v₁ v₁ := by
      rw [hess_self_eq_neg_gradient hK hF.1 hv₁, neg_neg]
    have hg2 : gradient F v₂ = -hess F v₁ v₂ := by
      rw [hhess_eq, hess_self_eq_neg_gradient hK hF.1 hv₂, neg_neg]
    rw [hg1, hg2, map_sub]
    abel
  have hmono := gradient_monotone hF.1 hv₁ hv₂
  rw [hgrad_diff, inner_neg_left] at hmono
  by_contra hne
  have hpos := hF.1.2.2.2.2 v₁ hv₁ (v₁ - v₂) (sub_ne_zero.mpr hne)
  linarith

/-! ### Section 5: Scaling Point Existence, Lemma 3.1, and Monotonicity of the Hessian -/

private lemma exists_scaling_point_min {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsSelfScaledBarrier K F ν) {x s : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ interior K) (hs : s ∈ interior (ConvexOptimization.dualCone K)) :
    ∃ w ∈ interior K,
      (∀ y ∈ interior K, ⟪s, w⟫_ℝ - ⟪gradient F w, x⟫_ℝ ≤ ⟪s, y⟫_ℝ - ⟪gradient F y, x⟫_ℝ) ∧
      hess F w x = s := by
  let ψ : EuclideanSpace ℝ (Fin n) → ℝ := fun w => ⟪s, w⟫_ℝ - ⟪gradient F w, x⟫_ℝ
  obtain ⟨c, hc_pos, hs_coerc⟩ := dual_interior_coercive hs
  have hneg_grad_nn : ∀ w ∈ interior K, 0 ≤ -⟪gradient F w, x⟫_ℝ := by
    intro w hw
    have hmem : -gradient F w ∈ ConvexOptimization.dualCone K := by
      rw [← hess_self_eq_neg_gradient hK hF.1 hw]
      exact interior_subset (hF.2 w hw w hw).1
    have h0 := hmem x (interior_subset hx)
    rwa [real_inner_comm, inner_neg_left] at h0
  have hψ_coerc : ∀ w ∈ interior K, c * ‖w‖ ≤ ψ w := by
    intro w hw
    have h1 := hs_coerc w (interior_subset hw)
    have h2 := hneg_grad_nn w hw
    dsimp only [ψ]
    linarith
  have hψ_barrier : ∀ w ∈ interior K, F w - F x + ν ≤ ψ w := by
    intro w hw
    have hconv := convex_first_order hF.1 hw hx
    rw [inner_sub_right, inner_gradient_self_logHom hF.1 hw] at hconv
    have hsw : 0 ≤ ⟪s, w⟫_ℝ := by
      rw [real_inner_comm]
      exact interior_subset hs w (interior_subset hw)
    dsimp only [ψ]
    linarith
  have hψ_contAt : ∀ w ∈ interior K, ContinuousAt ψ w := by
    intro w hw
    exact (continuous_const.inner continuous_id).continuousAt.sub
      ((gradient_differentiableAt hF.1 hw).continuousAt.inner continuousAt_const)
  let S : Set (EuclideanSpace ℝ (Fin n)) := {w | w ∈ interior K ∧ ψ w ≤ ψ x}
  have hxS : x ∈ S := ⟨hx, le_rfl⟩
  have hS_ne : S.Nonempty := ⟨x, hxS⟩
  have hS_bdd : Bornology.IsBounded S := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨max (ψ x / c) 0, fun w hw => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := hψ_coerc w hw.1
    have h2 : ‖w‖ ≤ ψ x / c := by
      rw [le_div_iff₀ hc_pos]
      linarith [hw.2]
    exact le_trans h2 (le_max_left _ _)
  have hS_closed : IsClosed S := by
    rw [← closure_subset_iff_isClosed]
    intro w₀ hw₀
    have hw₀_K : w₀ ∈ K :=
      hK.1.closure_eq ▸ closure_mono (fun y hy => interior_subset hy.1) hw₀
    have hw₀_int : w₀ ∈ interior K := by
      by_contra hnot
      have hfront : w₀ ∈ frontier K := ⟨hK.1.closure_eq.symm ▸ hw₀_K, hnot⟩
      have hbar : Tendsto F (𝓝[interior K] w₀) atTop := hF.1.2.1 w₀ hfront
      have hev_F : ∀ᶠ y in 𝓝[interior K] w₀, ψ x + F x - ν + 1 < F y :=
        hbar.eventually (eventually_gt_atTop (ψ x + F x - ν + 1))
      have hne_nhds : (𝓝[S] w₀).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hw₀
      have hle_filter : 𝓝[S] w₀ ≤ 𝓝[interior K] w₀ := nhdsWithin_mono w₀ (fun y hy => hy.1)
      have hev_S : ∀ᶠ y in 𝓝[S] w₀, ψ x + F x - ν + 1 < F y := hev_F.filter_mono hle_filter
      have hev_both : ∀ᶠ y in 𝓝[S] w₀, y ∈ S ∧ ψ x + F x - ν + 1 < F y :=
        Filter.Eventually.and self_mem_nhdsWithin hev_S
      obtain ⟨y, hyS, hyF⟩ := hev_both.exists
      have hbar_y := hψ_barrier y hyS.1
      linarith [hyS.2]
    have hψ_le : ψ w₀ ≤ ψ x := by
      have htend : Tendsto ψ (𝓝[S] w₀) (𝓝 (ψ w₀)) :=
        (hψ_contAt w₀ hw₀_int).tendsto.mono_left nhdsWithin_le_nhds
      have : (𝓝[S] w₀).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hw₀
      exact le_of_tendsto htend (by filter_upwards [self_mem_nhdsWithin] with y hy; exact hy.2)
    exact ⟨hw₀_int, hψ_le⟩
  have hS_compact : IsCompact S := Metric.isCompact_of_isClosed_isBounded hS_closed hS_bdd
  have hψ_contOn : ContinuousOn ψ S := fun w hw => (hψ_contAt w hw.1).continuousWithinAt
  obtain ⟨w, hwS, hw_min⟩ := hS_compact.exists_isMinOn hS_ne hψ_contOn
  have hw_glob : ∀ y ∈ interior K, ψ w ≤ ψ y := by
    intro y hy
    by_cases hyS : ψ y ≤ ψ x
    · exact hw_min ⟨hy, hyS⟩
    · exact le_trans hwS.2 (le_of_not_ge hyS)
  have hw_locMin : IsLocalMin ψ w := by
    filter_upwards [isOpen_interior.mem_nhds hwS.1] with y hy
    exact hw_glob y hy
  have hfd0 : fderiv ℝ ψ w = 0 := hw_locMin.fderiv_eq_zero
  have hψ_fderiv : HasFDerivAt ψ
      ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) s -
        ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) x).comp (hess F w)) w := by
    have h1 : HasFDerivAt (fun y => ⟪s, y⟫_ℝ)
        ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) s) w := by
      have hfun1 : (fun y => ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) s) y) =
          (fun y => ⟪s, y⟫_ℝ) := by
        ext y
        exact InnerProductSpace.toDual_apply_apply
      rw [← hfun1]
      exact ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) s).hasFDerivAt
    have h2 : HasFDerivAt (fun y => ⟪gradient F y, x⟫_ℝ)
        (((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) x).comp (hess F w)) w := by
      have hG : HasFDerivAt (gradient F) (hess F w) w :=
        (gradient_differentiableAt hF.1 hwS.1).hasFDerivAt
      have hL : HasFDerivAt (fun y => ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) x) (gradient F y))
          (((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) x).comp (hess F w)) w :=
        ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) x).hasFDerivAt.comp w hG
      have hfun : (fun y => ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) x) (gradient F y)) =
          (fun y => ⟪gradient F y, x⟫_ℝ) := by
        ext y
        simp only [InnerProductSpace.toDual_apply_apply]
        exact real_inner_comm (gradient F y) x
      rwa [hfun] at hL
    exact h1.sub h2
  have hEq : hess F w x = s := by
    have hzero := hψ_fderiv.fderiv.symm.trans hfd0
    apply ext_inner_right ℝ
    intro h
    have happ := congrArg (fun L => L h) hzero
    simp only [sub_apply, ContinuousLinearMap.comp_apply,
      InnerProductSpace.toDual_apply_apply, zero_apply] at happ
    rw [← hess_symm hF.1 hwS.1 x h] at happ
    linarith
  exact ⟨w, hwS.1, hw_glob, hEq⟩

private lemma neg_inner_gradient_convexOn {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsSelfScaledBarrier K F ν) {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ interior K) :
    ConvexOn ℝ (interior K) (fun y => -⟪gradient F y, z⟫_ℝ) := by
  have hfirst : ∀ y₀ ∈ interior K, ∀ y ∈ interior K,
      -⟪gradient F y₀, z⟫_ℝ - ⟪hess F y₀ z, y - y₀⟫_ℝ ≤ -⟪gradient F y, z⟫_ℝ := by
    intro y₀ hy₀ y hy
    obtain ⟨w, hw, hw_min, hw_eq⟩ :=
      exists_scaling_point_min hK hF hz (hF.2 y₀ hy₀ z hz).1
    have hwy : w = y₀ := hess_apply_injective hK hF hw hy₀ hz hw_eq
    subst hwy
    have hle := hw_min y hy
    rw [inner_sub_right]
    linarith
  refine ⟨hK.2.1.interior, ?_⟩
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab
  have hy₀ : a • y₁ + b • y₂ ∈ interior K := hK.2.1.interior hy₁ hy₂ ha hb hab
  set y₀ := a • y₁ + b • y₂
  have h1 := hfirst y₀ hy₀ y₁ hy₁
  have h2 := hfirst y₀ hy₀ y₂ hy₂
  have hlin : a * ⟪hess F y₀ z, y₁ - y₀⟫_ℝ + b * ⟪hess F y₀ z, y₂ - y₀⟫_ℝ = 0 := by
    have hcomb : a • (y₁ - y₀) + b • (y₂ - y₀) = 0 := by
      rw [smul_sub, smul_sub]
      calc
        a • y₁ - a • y₀ + (b • y₂ - b • y₀)
            = (a • y₁ + b • y₂) - (a + b) • y₀ := by rw [add_smul]; abel
        _ = y₀ - (1 : ℝ) • y₀ := by rw [hab]
        _ = 0 := by simp
    rw [← inner_smul_right, ← inner_smul_right, ← inner_add_right, hcomb, inner_zero_right]
  have hcomb_le :
      a * (-⟪gradient F y₀, z⟫_ℝ - ⟪hess F y₀ z, y₁ - y₀⟫_ℝ) +
      b * (-⟪gradient F y₀, z⟫_ℝ - ⟪hess F y₀ z, y₂ - y₀⟫_ℝ) ≤
      a * (-⟪gradient F y₁, z⟫_ℝ) + b * (-⟪gradient F y₂, z⟫_ℝ) :=
    add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
  simp only [smul_eq_mul]
  have h_lhs :
      a * (-⟪gradient F y₀, z⟫_ℝ - ⟪hess F y₀ z, y₁ - y₀⟫_ℝ) +
      b * (-⟪gradient F y₀, z⟫_ℝ - ⟪hess F y₀ z, y₂ - y₀⟫_ℝ) = -⟪gradient F y₀, z⟫_ℝ := by
    calc
      a * (-⟪gradient F y₀, z⟫_ℝ - ⟪hess F y₀ z, y₁ - y₀⟫_ℝ) +
        b * (-⟪gradient F y₀, z⟫_ℝ - ⟪hess F y₀ z, y₂ - y₀⟫_ℝ)
          = (a + b) * (-⟪gradient F y₀, z⟫_ℝ) -
              (a * ⟪hess F y₀ z, y₁ - y₀⟫_ℝ + b * ⟪hess F y₀ z, y₂ - y₀⟫_ℝ) := by ring
      _ = -⟪gradient F y₀, z⟫_ℝ := by rw [hab, hlin]; ring
  linarith

private lemma line_add_hasDerivAt {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hF : IsLogHomBarrier K F ν)
    {p u : EuclideanSpace ℝ (Fin n)} {t : ℝ} (ht : p + t • u ∈ interior K) :
    HasDerivAt (fun s : ℝ => F (p + s • u)) ⟪gradient F (p + t • u), u⟫_ℝ t := by
  have hline : HasDerivAt (fun s : ℝ => p + s • u) u t := by
    simpa using ((hasDerivAt_id t).smul_const u).const_add p
  have hcomp : HasDerivAt (fun s : ℝ => F (p + s • u)) (fderiv ℝ F (p + t • u) u) t :=
    (differentiableAt_of_logHom hF ht).hasFDerivAt.comp_hasDerivAt t hline
  simpa [inner_gradient_eq_fderiv] using hcomp

private lemma line_grad_inner_hasDerivAt {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ} (hF : IsLogHomBarrier K F ν)
    {p u : EuclideanSpace ℝ (Fin n)} {t : ℝ} (ht : p + t • u ∈ interior K) :
    HasDerivAt (fun s : ℝ => ⟪gradient F (p + s • u), u⟫_ℝ) ⟪hess F (p + t • u) u, u⟫_ℝ t := by
  have hline : HasDerivAt (fun s : ℝ => p + s • u) u t := by
    simpa using ((hasDerivAt_id t).smul_const u).const_add p
  have hgrad : HasDerivAt (fun s : ℝ => gradient F (p + s • u)) (hess F (p + t • u) u) t := by
    have hG : HasFDerivAt (gradient F) (hess F (p + t • u)) (p + t • u) :=
      (gradient_differentiableAt hF ht).hasFDerivAt
    exact hG.comp_hasDerivAt t hline
  let L := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) u
  have hL : HasDerivAt (fun s : ℝ => L (gradient F (p + s • u)))
      (L (hess F (p + t • u) u)) t :=
    L.hasFDerivAt.comp_hasDerivAt t hgrad
  have hfun : (fun s : ℝ => L (gradient F (p + s • u))) =
      (fun s : ℝ => ⟪gradient F (p + s • u), u⟫_ℝ) := by
    ext s
    simp only [L, InnerProductSpace.toDual_apply_apply]
    exact real_inner_comm _ _
  rw [hfun] at hL
  simpa only [L, InnerProductSpace.toDual_apply_apply, real_inner_comm u] using hL

private lemma hess_antitone_interior {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsSelfScaledBarrier K F ν) {x d : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ interior K) (hd : d ∈ interior K) (u : EuclideanSpace ℝ (Fin n)) :
    ⟪hess F (x + d) u, u⟫_ℝ ≤ ⟪hess F x u, u⟫_ℝ := by
  have hcont_line : Continuous (fun s : ℝ => x + s • u) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hnhds : {s : ℝ | x + s • u ∈ interior K} ∈ 𝓝 (0 : ℝ) :=
    hcont_line.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds (by simpa using hx))
  obtain ⟨ε, hε_pos, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  have hmem_x : ∀ s ∈ Set.Ioo (-ε) ε, x + s • u ∈ interior K := by
    intro s hs
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact hs
  have hmem_xt : ∀ s ∈ Set.Ioo (-ε) ε, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      x + s • u + t • d ∈ interior K := by
    intro s hs t ht
    exact add_mem_interior_cone hK (hmem_x s hs) (hK.2.2.1 d (interior_subset hd) t ht.1)
  let φ : ℝ → ℝ := fun s => F (x + s • u) - F (x + d + s • u)
  have hφ_int : ∀ s ∈ Set.Ioo (-ε) ε,
      φ s = ∫ t in (0 : ℝ)..1, -⟪gradient F (x + s • u + t • d), d⟫_ℝ := by
    intro s hs
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun τ : ℝ => -F (x + s • u + τ • d))
          (-⟪gradient F (x + s • u + t • d), d⟫_ℝ) t := by
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      exact (line_add_hasDerivAt hF.1 (hmem_xt s hs t ht)).neg
    have hcont : ContinuousOn (fun t : ℝ => -⟪gradient F (x + s • u + t • d), d⟫_ℝ)
        (Set.uIcc (0 : ℝ) 1) := by
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      have h1 : ContinuousAt (fun τ : ℝ => x + s • u + τ • d) t :=
        (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
      have h2 : ContinuousAt (fun τ : ℝ => gradient F (x + s • u + τ • d)) t :=
        ContinuousAt.comp (g := gradient F) (f := fun τ : ℝ => x + s • u + τ • d)
          (gradient_differentiableAt hF.1 (hmem_xt s hs t ht)).continuousAt h1
      exact (h2.inner continuousAt_const).neg.continuousWithinAt
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
    have heq1 : x + s • u + (1 : ℝ) • d = x + d + s • u := by rw [one_smul]; abel
    have heq0 : x + s • u + (0 : ℝ) • d = x + s • u := by simp
    rw [hftc, heq1, heq0]
    dsimp only [φ]
    ring
  have hconv_g := neg_inner_gradient_convexOn hK hF hd
  have hφ_conv : ConvexOn ℝ (Set.Ioo (-ε) ε) φ := by
    refine ⟨convex_Ioo (-ε) ε, ?_⟩
    intro s₁ hs₁ s₂ hs₂ a b ha hb hab
    have hs : a * s₁ + b * s₂ ∈ Set.Ioo (-ε) ε :=
      convex_Ioo (-ε) ε hs₁ hs₂ ha hb hab
    simp only [smul_eq_mul]
    rw [hφ_int _ hs, hφ_int _ hs₁, hφ_int _ hs₂]
    have hint : ∀ s' ∈ Set.Ioo (-ε) ε,
        IntervalIntegrable (fun t : ℝ => -⟪gradient F (x + s' • u + t • d), d⟫_ℝ)
          MeasureTheory.volume 0 1 := by
      intro s' hs'
      refine ContinuousOn.intervalIntegrable fun t ht => ?_
      rw [Set.uIcc_of_le zero_le_one] at ht
      have h1 : ContinuousAt (fun τ : ℝ => x + s' • u + τ • d) t :=
        (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
      have h2 : ContinuousAt (fun τ : ℝ => gradient F (x + s' • u + τ • d)) t :=
        ContinuousAt.comp (g := gradient F) (f := fun τ : ℝ => x + s' • u + τ • d)
          (gradient_differentiableAt hF.1 (hmem_xt s' hs' t ht)).continuousAt h1
      exact (h2.inner continuousAt_const).neg.continuousWithinAt
    have hmono := intervalIntegral.integral_mono_on zero_le_one (hint _ hs)
      (((hint _ hs₁).const_mul a).add ((hint _ hs₂).const_mul b)) (fun t ht => by
        have hy₁ := hmem_xt s₁ hs₁ t ht
        have hy₂ := hmem_xt s₂ hs₂ t ht
        have hcomb : a • (x + s₁ • u + t • d) + b • (x + s₂ • u + t • d) =
            x + (a * s₁ + b * s₂) • u + t • d := by
          rw [smul_add, smul_add, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
          calc
            a • x + (a * s₁) • u + (a * t) • d + (b • x + (b * s₂) • u + (b * t) • d)
                = (a + b) • x + (a * s₁ + b * s₂) • u + ((a + b) * t) • d := by
                  rw [add_smul, add_smul, add_mul, add_smul]; abel
            _ = x + (a * s₁ + b * s₂) • u + t • d := by rw [hab, one_smul, one_mul]
        have hpt := hconv_g.2 hy₁ hy₂ ha hb hab
        rw [hcomb] at hpt
        simpa [smul_eq_mul] using hpt)
    rw [intervalIntegral.integral_add ((hint _ hs₁).const_mul a) ((hint _ hs₂).const_mul b),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
    exact hmono
  have hφ_hasDeriv : ∀ s ∈ Set.Ioo (-ε) ε,
      HasDerivAt φ (⟪gradient F (x + s • u), u⟫_ℝ - ⟪gradient F (x + d + s • u), u⟫_ℝ) s := by
    intro s hs
    have h1 := line_add_hasDerivAt hF.1 (hmem_x s hs)
    have h2_mem : x + d + s • u ∈ interior K := by
      have := hmem_xt s hs 1 (Set.right_mem_Icc.mpr zero_le_one)
      rwa [one_smul, add_right_comm] at this
    have h2 := line_add_hasDerivAt hF.1 h2_mem
    exact h1.sub h2
  have hmono_deriv : MonotoneOn (deriv φ) (Set.Ioo (-ε) ε) :=
    hφ_conv.monotoneOn_deriv (fun s hs => (hφ_hasDeriv s hs).differentiableAt)
  have hderiv_eq : deriv φ =ᶠ[𝓝 (0 : ℝ)]
      (fun s => ⟪gradient F (x + s • u), u⟫_ℝ - ⟪gradient F (x + d + s • u), u⟫_ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Set.Ioo (-ε) ε by constructor <;> linarith)] with s hs
    exact (hφ_hasDeriv s hs).deriv
  have hxd : x + d ∈ interior K := add_mem_interior_cone hK hx (interior_subset hd)
  have hd2 : HasDerivAt (deriv φ) (⟪hess F x u, u⟫_ℝ - ⟪hess F (x + d) u, u⟫_ℝ) (0 : ℝ) := by
    have h1 : HasDerivAt (fun s : ℝ => ⟪gradient F (x + s • u), u⟫_ℝ) ⟪hess F x u, u⟫_ℝ (0 : ℝ) := by
      simpa using line_grad_inner_hasDerivAt hF.1 (p := x) (u := u) (t := (0 : ℝ)) (by simpa using hx)
    have h2 : HasDerivAt (fun s : ℝ => ⟪gradient F (x + d + s • u), u⟫_ℝ) ⟪hess F (x + d) u, u⟫_ℝ (0 : ℝ) := by
      simpa using line_grad_inner_hasDerivAt hF.1 (p := x + d) (u := u) (t := (0 : ℝ)) (by simpa using hxd)
    exact (h1.sub h2).congr_of_eventuallyEq hderiv_eq
  have hslope : Tendsto (fun t : ℝ => t⁻¹ * (deriv φ t - deriv φ 0)) (𝓝[>] (0 : ℝ))
      (𝓝 (⟪hess F x u, u⟫_ℝ - ⟪hess F (x + d) u, u⟫_ℝ)) := by
    have hs := hd2.tendsto_slope_zero.mono_left
      (nhdsWithin_mono (0 : ℝ) (show Set.Ioi (0 : ℝ) ⊆ ({0} : Set ℝ)ᶜ from fun t ht => ne_of_gt ht))
    simpa [smul_eq_mul, add_zero] using hs
  have hev_nn : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ t⁻¹ * (deriv φ t - deriv φ 0) := by
    filter_upwards [Ioo_mem_nhdsGT hε_pos] with t ht
    have h0_mem : (0 : ℝ) ∈ Set.Ioo (-ε) ε := by constructor <;> linarith
    have ht_mem : t ∈ Set.Ioo (-ε) ε := ⟨by linarith [ht.1], ht.2⟩
    have hle := hmono_deriv h0_mem ht_mem ht.1.le
    exact mul_nonneg (inv_nonneg.mpr ht.1.le) (sub_nonneg.mpr hle)
  have hnn := ge_of_tendsto hslope hev_nn
  linarith

private lemma hess_antitone_cone {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsSelfScaledBarrier K F ν) {x d : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ interior K) (hd : d ∈ K) (u : EuclideanSpace ℝ (Fin n)) :
    ⟪hess F (x + d) u, u⟫_ℝ ≤ ⟪hess F x u, u⟫_ℝ := by
  have hxd : x + d ∈ interior K := add_mem_interior_cone hK hx hd
  have htend_pt : Tendsto (fun t : ℝ => x + (d + t • x)) (𝓝[>] (0 : ℝ)) (𝓝 (x + d)) := by
    have hcont : Continuous (fun t : ℝ => x + (d + t • x)) :=
      continuous_const.add (continuous_const.add (continuous_id.smul continuous_const))
    have hval : x + (d + (0 : ℝ) • x) = x + d := by simp
    rw [← hval]
    exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have htend_val : Tendsto (fun t : ℝ => ⟪hess F (x + (d + t • x)) u, u⟫_ℝ)
      (𝓝[>] (0 : ℝ)) (𝓝 ⟪hess F (x + d) u, u⟫_ℝ) := by
    have h1 : Tendsto (fun t : ℝ => hess F (x + (d + t • x))) (𝓝[>] (0 : ℝ)) (𝓝 (hess F (x + d))) :=
      (hess_continuousAt hF.1 hxd).tendsto.comp htend_pt
    have h2 : Continuous (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => ⟪L u, u⟫_ℝ) :=
      ((ContinuousLinearMap.apply ℝ _ u).continuous).inner continuous_const
    exact h2.continuousAt.tendsto.comp h1
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ⟪hess F (x + (d + t • x)) u, u⟫_ℝ ≤ ⟪hess F x u, u⟫_ℝ := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have hdt : d + t • x ∈ interior K := by
      rw [add_comm]
      exact add_mem_interior_cone hK (smul_mem_interior_cone hK hx ht) hd
    exact hess_antitone_interior hK hF hx hdt u
  exact le_of_tendsto htend_val hev

private lemma hess_le_sigma_sq_hess {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsSelfScaledBarrier K F ν) {a b : EuclideanSpace ℝ (Fin n)}
    (ha : a ∈ interior K) (hb : b ∈ interior K) (hb0 : b ≠ 0) (u : EuclideanSpace ℝ (Fin n)) :
    ⟪hess F a u, u⟫_ℝ ≤ (sigma K a b) ^ 2 * ⟪hess F b u, u⟫_ℝ := by
  set β := sigma K a b
  have hβ_pos : 0 < β := sigma_pos_of_interior hK ha hb hb0
  have hmem : β • a - b ∈ K := (sigma_mem_and_nonneg hK ha b).2
  have hrew : β • a = b + (β • a - b) := by abel
  have hanti : ⟪hess F (β • a) u, u⟫_ℝ ≤ ⟪hess F b u, u⟫_ℝ := by
    rw [hrew]
    exact hess_antitone_cone hK hF hb hmem u
  rw [hess_smul_logHom hK hF.1 ha hβ_pos u, inner_smul_left, RCLike.conj_to_real] at hanti
  have hβ2_pos : 0 < β ^ 2 := sq_pos_of_pos hβ_pos
  calc
    ⟪hess F a u, u⟫_ℝ = β ^ 2 * ((β ^ 2)⁻¹ * ⟪hess F a u, u⟫_ℝ) := by
      field_simp [hβ2_pos.ne']
    _ ≤ β ^ 2 * ⟪hess F b u, u⟫_ℝ := mul_le_mul_of_nonneg_left hanti hβ2_pos.le

/-! ### Section 6: Operator Inequalities, Sigma Bounds, Polarization, and Theorem 4.3 -/

private lemma cauchy_schwarz_of_symm_nonneg {n : ℕ}
    (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hM_symm : ∀ a b, ⟪M a, b⟫_ℝ = ⟪a, M b⟫_ℝ)
    (hM_nn : ∀ a, 0 ≤ ⟪M a, a⟫_ℝ)
    (a b : EuclideanSpace ℝ (Fin n)) :
    ⟪M a, b⟫_ℝ ^ 2 ≤ ⟪M a, a⟫_ℝ * ⟪M b, b⟫_ℝ := by
  have hquad : ∀ t : ℝ, 0 ≤ ⟪M a, a⟫_ℝ + 2 * t * ⟪M a, b⟫_ℝ + t ^ 2 * ⟪M b, b⟫_ℝ := by
    intro t
    have hnn := hM_nn (a + t • b)
    have hexp : ⟪M (a + t • b), a + t • b⟫_ℝ =
        ⟪M a, a⟫_ℝ + 2 * t * ⟪M a, b⟫_ℝ + t ^ 2 * ⟪M b, b⟫_ℝ := by
      rw [map_add, map_smul, inner_add_left, inner_add_right, inner_add_right,
        inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right]
      simp only [RCLike.conj_to_real]
      have hba : ⟪M b, a⟫_ℝ = ⟪M a, b⟫_ℝ := by rw [hM_symm b a, real_inner_comm]
      rw [hba]
      ring
    linarith
  by_cases hbb : ⟪M b, b⟫_ℝ = 0
  · have hlin : ∀ t : ℝ, 0 ≤ ⟪M a, a⟫_ℝ + 2 * t * ⟪M a, b⟫_ℝ := fun t => by
      have := hquad t; rw [hbb, mul_zero, add_zero] at this; exact this
    have hab0 : ⟪M a, b⟫_ℝ = 0 := by
      by_contra hne
      have h1 := hlin (-(⟪M a, a⟫_ℝ + 1) / (2 * ⟪M a, b⟫_ℝ))
      have h2 : 2 * (-(⟪M a, a⟫_ℝ + 1) / (2 * ⟪M a, b⟫_ℝ)) * ⟪M a, b⟫_ℝ = -(⟪M a, a⟫_ℝ + 1) := by
        field_simp [hne]
      linarith
    rw [hab0, hbb]
    norm_num
  · have hbb_pos : 0 < ⟪M b, b⟫_ℝ := lt_of_le_of_ne (hM_nn b) (Ne.symm hbb)
    have hmin := hquad (-⟪M a, b⟫_ℝ / ⟪M b, b⟫_ℝ)
    have hrew : ⟪M a, a⟫_ℝ + 2 * (-⟪M a, b⟫_ℝ / ⟪M b, b⟫_ℝ) * ⟪M a, b⟫_ℝ +
        (-⟪M a, b⟫_ℝ / ⟪M b, b⟫_ℝ) ^ 2 * ⟪M b, b⟫_ℝ =
        (⟪M a, a⟫_ℝ * ⟪M b, b⟫_ℝ - ⟪M a, b⟫_ℝ ^ 2) / ⟪M b, b⟫_ℝ := by
      field_simp [hbb_pos.ne']
      ring
    rw [hrew, div_nonneg_iff] at hmin
    rcases hmin with ⟨h1, _⟩ | ⟨_, h2⟩
    · linarith
    · linarith

private lemma loewner_inv_le {n : ℕ}
    {K : Set (EuclideanSpace ℝ (Fin n))} {F : EuclideanSpace ℝ (Fin n) → ℝ} {ν : ℝ}
    (hF : IsLogHomBarrier K F ν) {a b : EuclideanSpace ℝ (Fin n)}
    (ha : a ∈ interior K) (hb : b ∈ interior K) {c : ℝ}
    (hle : ∀ u, ⟪hess F a u, u⟫_ℝ ≤ c * ⟪hess F b u, u⟫_ℝ)
    (z : EuclideanSpace ℝ (Fin n)) :
    ⟪(hess F b).inverse z, z⟫_ℝ ≤ c * ⟪(hess F a).inverse z, z⟫_ℝ := by
  set y := (hess F b).inverse z
  have hby : hess F b y = z := hess_apply_inv hF hb z
  by_cases hy0 : y = 0
  · have hz0 : z = 0 := by rw [← hby, hy0, map_zero]
    simp [hz0]
  · have hcs := cauchy_schwarz_of_symm_nonneg (hess F a) (hess_symm hF ha) (hess_nonneg hF ha)
      ((hess F a).inverse z) y
    have h1 : ⟪hess F a ((hess F a).inverse z), y⟫_ℝ = ⟪hess F b y, y⟫_ℝ := by
      rw [hess_apply_inv hF ha z, hby]
    have h2 : ⟪hess F a ((hess F a).inverse z), (hess F a).inverse z⟫_ℝ =
        ⟪(hess F a).inverse z, z⟫_ℝ := by
      rw [hess_apply_inv hF ha z, real_inner_comm]
    rw [h1, h2] at hcs
    have h3 : ⟪hess F b y, y⟫_ℝ ^ 2 ≤
        ⟪(hess F a).inverse z, z⟫_ℝ * (c * ⟪hess F b y, y⟫_ℝ) :=
      le_trans hcs (mul_le_mul_of_nonneg_left (hle y) (hess_inv_nonneg hF ha z))
    have hpos : 0 < ⟪hess F b y, y⟫_ℝ := hF.2.2.2.2 b hb y hy0
    have hfinal : ⟪hess F b y, y⟫_ℝ ≤ c * ⟪(hess F a).inverse z, z⟫_ℝ := by
      nlinarith
    have hrew : ⟪(hess F b).inverse z, z⟫_ℝ = ⟪hess F b y, y⟫_ℝ := by
      change ⟪y, z⟫_ℝ = ⟪hess F b y, y⟫_ℝ
      rw [hby, real_inner_comm]
    rwa [hrew]

private lemma polarization_bound {n : ℕ}
    (H T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH_symm : ∀ a b, ⟪H a, b⟫_ℝ = ⟪a, H b⟫_ℝ)
    (hH_pos : ∀ a, a ≠ 0 → 0 < ⟪H a, a⟫_ℝ)
    (hT_symm : ∀ a b, ⟪H (T a), b⟫_ℝ = ⟪H a, T b⟫_ℝ)
    {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ u, |⟪H (T u), u⟫_ℝ| ≤ c * ⟪H u, u⟫_ℝ)
    (p : EuclideanSpace ℝ (Fin n)) :
    Real.sqrt ⟪H (T p), T p⟫_ℝ ≤ c * Real.sqrt ⟪H p, p⟫_ℝ := by
  have hH_nn : ∀ a, 0 ≤ ⟪H a, a⟫_ℝ := fun a => by
    by_cases ha : a = 0
    · simp [ha]
    · exact (hH_pos a ha).le
  set r := Real.sqrt ⟪H p, p⟫_ℝ
  set s := Real.sqrt ⟪H (T p), T p⟫_ℝ
  by_cases hs0 : s = 0
  · rw [hs0]; exact mul_nonneg hc (Real.sqrt_nonneg _)
  · have hs_pos : 0 < s := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hs0)
    have hp_ne : p ≠ 0 := by
      intro hp0
      have : s = 0 := by simp [s, hp0]
      exact hs0 this
    have hr_pos : 0 < r := Real.sqrt_pos.mpr (hH_pos p hp_ne)
    set y := (r / s) • T p
    have hr_sq : r ^ 2 = ⟪H p, p⟫_ℝ := Real.sq_sqrt (hH_nn p)
    have hs_sq : s ^ 2 = ⟪H (T p), T p⟫_ℝ := Real.sq_sqrt (hH_nn (T p))
    have hy_norm : ⟪H y, y⟫_ℝ = r ^ 2 := by
      simp only [y, map_smul, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
      rw [← hs_sq]
      field_simp [hs_pos.ne']
    have hTpy : ⟪H (T p), y⟫_ℝ = r * s := by
      simp only [y, inner_smul_right]
      rw [← hs_sq]
      field_simp [hs_pos.ne']
    have hpol : 4 * ⟪H (T p), y⟫_ℝ =
        ⟪H (T (p + y)), p + y⟫_ℝ - ⟪H (T (p - y)), p - y⟫_ℝ := by
      have hsym : ⟪H (T y), p⟫_ℝ = ⟪H (T p), y⟫_ℝ := by
        rw [hT_symm y p, hH_symm y (T p), real_inner_comm]
      simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
        hsym]
      ring
    have hpar : ⟪H (p + y), p + y⟫_ℝ + ⟪H (p - y), p - y⟫_ℝ =
        2 * (⟪H p, p⟫_ℝ + ⟪H y, y⟫_ℝ) := by
      have hsym : ⟪H y, p⟫_ℝ = ⟪H p, y⟫_ℝ := by rw [hH_symm y p, real_inner_comm]
      simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
        hsym]
      ring
    have hb1 : ⟪H (T (p + y)), p + y⟫_ℝ ≤ c * ⟪H (p + y), p + y⟫_ℝ :=
      (abs_le.mp (hbound (p + y))).2
    have hb2 : -⟪H (T (p - y)), p - y⟫_ℝ ≤ c * ⟪H (p - y), p - y⟫_ℝ := by
      have := (abs_le.mp (hbound (p - y))).1; linarith
    have hineq : 4 * (r * s) ≤ 4 * c * r ^ 2 := by
      calc
        4 * (r * s) = 4 * ⟪H (T p), y⟫_ℝ := by rw [hTpy]
        _ = ⟪H (T (p + y)), p + y⟫_ℝ - ⟪H (T (p - y)), p - y⟫_ℝ := hpol
        _ ≤ c * ⟪H (p + y), p + y⟫_ℝ + c * ⟪H (p - y), p - y⟫_ℝ := by linarith
        _ = c * (⟪H (p + y), p + y⟫_ℝ + ⟪H (p - y), p - y⟫_ℝ) := by ring
        _ = 2 * c * (⟪H p, p⟫_ℝ + ⟪H y, y⟫_ℝ) := by rw [hpar]; ring
        _ = 4 * c * r ^ 2 := by rw [← hr_sq, hy_norm]; ring
    nlinarith

private lemma sigma_v_le_one_add_absn {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {x v : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior K) :
    sigma K x v ≤ 1 + absn K x (v - x) := by
  obtain ⟨hnn, hmem⟩ := sigma_mem_and_nonneg hK hx (v - x)
  have h1_mem : (1 + sigma K x (v - x)) • x - v ∈ K := by
    have hrew : (1 + sigma K x (v - x)) • x - v = sigma K x (v - x) • x - (v - x) := by
      rw [add_smul, one_smul]; abel
    rw [hrew]
    exact hmem
  have hbdd : BddBelow {β : ℝ | 0 ≤ β ∧ β • x - v ∈ K} := ⟨0, fun β hβ => hβ.1⟩
  have hle : sigma K x v ≤ 1 + sigma K x (v - x) :=
    csInf_le hbdd ⟨by linarith, h1_mem⟩
  exact le_trans hle (add_le_add le_rfl (le_max_left _ _))

private lemma one_sub_inv_sigma_le_absn {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsProperCone K) {x v : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ interior K) (hv : v ∈ interior K) (hx0 : x ≠ 0) :
    1 - (sigma K v x)⁻¹ ≤ absn K x (v - x) := by
  set δ := sigma K x (-(v - x))
  have hδ_le : δ ≤ absn K x (v - x) := le_max_right _ _
  have hσ_pos : 0 < sigma K v x := sigma_pos_of_interior hK hv hx hx0
  by_cases hδ1 : δ < 1
  · obtain ⟨_, hmem⟩ := sigma_mem_and_nonneg hK hx (-(v - x))
    have h1δ_pos : 0 < 1 - δ := sub_pos.mpr hδ1
    have hrew : v - (1 - δ) • x = δ • x - -(v - x) := by
      rw [sub_smul, one_smul, sub_neg_eq_add]; abel
    have hv_mem : v - (1 - δ) • x ∈ K := by rwa [hrew]
    have hscaled : (1 - δ)⁻¹ • v - x ∈ K := by
      have hsc := hK.2.2.1 _ hv_mem (1 - δ)⁻¹ (inv_pos.mpr h1δ_pos).le
      rwa [smul_sub, smul_smul, inv_mul_cancel₀ h1δ_pos.ne', one_smul] at hsc
    have hbdd : BddBelow {β : ℝ | 0 ≤ β ∧ β • v - x ∈ K} := ⟨0, fun β hβ => hβ.1⟩
    have hσ_le : sigma K v x ≤ (1 - δ)⁻¹ :=
      csInf_le hbdd ⟨(inv_pos.mpr h1δ_pos).le, hscaled⟩
    have hinv_ge : 1 - δ ≤ (sigma K v x)⁻¹ := by
      have := inv_anti₀ hσ_pos hσ_le
      rwa [inv_inv] at this
    linarith
  · push Not at hδ1
    have hinv_pos : 0 < (sigma K v x)⁻¹ := inv_pos.mpr hσ_pos
    linarith

private lemma theorem_4_3_aux {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hF : IsSelfScaledBarrier K F ν)
    (x v : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) (hv : v ∈ interior K) :
    dnorm F v (gradient F v - gradient F x - hess F x (v - x)) ≤
      absn K x (v - x) * lnorm F x (v - x) := by
  by_cases hxv : x = v
  · subst hxv
    simp [dnorm, lnorm]
  · have hx0 : x ≠ 0 := ne_zero_of_mem_interior_of_ne hK hxv hx
    have hv0 : v ≠ 0 := ne_zero_of_mem_interior_of_ne hK hxv hv
    have hs_mem : -gradient F v ∈ interior (ConvexOptimization.dualCone K) := by
      rw [← hess_self_eq_neg_gradient hK hF.1 hv]
      exact (hF.2 v hv v hv).1
    obtain ⟨w, hw, _, hw_eq⟩ := exists_scaling_point_min hK hF hx hs_mem
    have hwx_eq_vv : hess F w x = hess F v v := by
      rw [hw_eq, hess_self_eq_neg_gradient hK hF.1 hv]
    have ⟨hc_grad_wx, hc_hess_wx⟩ := conj_grad_hess_at_hess hK hF hw hx
    have ⟨hc_grad_vv, hc_hess_vv⟩ := conj_grad_hess_at_hess hK hF hv hv
    rw [hwx_eq_vv] at hc_grad_wx hc_hess_wx
    -- Identity 1: gradient F x = -hess F w v
    have hgrad_x : gradient F x = -hess F w v := by
      have h1 : (hess F w).inverse (gradient F x) = (hess F v).inverse (gradient F v) :=
        hc_grad_wx.symm.trans hc_grad_vv
      have h2 : (hess F v).inverse (gradient F v) = -v := by
        have hgv : gradient F v = -hess F v v := by
          rw [hess_self_eq_neg_gradient hK hF.1 hv, neg_neg]
        rw [hgv, map_neg, inv_apply_hess hF.1 hv v]
      rw [h2] at h1
      have h3 := congrArg (hess F w) h1
      rw [hess_apply_inv hF.1 hw, map_neg] at h3
      exact h3
    -- Identity 2: (hess F v).inverse = (hess F w).inverse ∘L hess F x ∘L (hess F w).inverse
    have hinv_v : (hess F v).inverse =
        (hess F w).inverse ∘L hess F x ∘L (hess F w).inverse := by
      have h1 : (hess F v).inverse ∘L hess F v ∘L (hess F v).inverse =
          (hess F w).inverse ∘L hess F x ∘L (hess F w).inverse :=
        hc_hess_vv.symm.trans hc_hess_wx
      rw [← h1]
      ext u
      simp only [ContinuousLinearMap.comp_apply, hess_apply_inv hF.1 hv]
    -- Rewrite remainder q = (hess F w - hess F x)(v - x)
    set p := v - x
    set q := gradient F v - gradient F x - hess F x p
    have hq_eq : q = hess F w p - hess F x p := by
      have hgv : gradient F v = -hess F w x := by rw [hw_eq, neg_neg]
      simp only [q, p, hgv, hgrad_x, map_sub]
      abel
    -- Define A = (hess F w).inverse ∘L hess F x and T = id - A
    let H := hess F x
    let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
      (hess F w).inverse ∘L H
    let T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
      ContinuousLinearMap.id ℝ _ - A
    have hTp : T p = (hess F w).inverse q := by
      simp only [T, A, H, hq_eq, sub_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.comp_apply, map_sub, inv_apply_hess hF.1 hw]
    have hdnorm_eq : dnorm F v q = Real.sqrt ⟪H (T p), T p⟫_ℝ := by
      unfold dnorm
      congr 1
      rw [hTp, hinv_v]
      simp only [ContinuousLinearMap.comp_apply, H]
      rw [hess_inv_symm hF.1 hw (hess F x ((hess F w).inverse q)) q]
    have hA_symm : ∀ a b, ⟪H (A a), b⟫_ℝ = ⟪H a, A b⟫_ℝ := by
      intro a b
      simp only [A, H, ContinuousLinearMap.comp_apply]
      rw [hess_symm hF.1 hx ((hess F w).inverse (hess F x a)) b,
        hess_inv_symm hF.1 hw (hess F x a) (hess F x b),
        real_inner_comm]
    have hT_symm : ∀ a b, ⟪H (T a), b⟫_ℝ = ⟪H a, T b⟫_ℝ := by
      intro a b
      simp only [T, sub_apply, ContinuousLinearMap.id_apply, map_sub,
        inner_sub_left, inner_sub_right, hA_symm a b]
    have hAu_sq : ∀ u, ⟪H (A u), A u⟫_ℝ = ⟪(hess F v).inverse (H u), H u⟫_ℝ := by
      intro u
      simp only [A, H, ContinuousLinearMap.comp_apply, hinv_v]
      rw [hess_inv_symm hF.1 hw (hess F x ((hess F w).inverse (hess F x u))) (hess F x u)]
    -- Upper bound: ⟪H (A u), u⟫ ≤ σ_x(v) * ⟪H u, u⟫
    have hσxv_pos : 0 < sigma K x v := sigma_pos_of_interior hK hx hv hv0
    have hA_upper : ∀ u, ⟪H (A u), u⟫_ℝ ≤ sigma K x v * ⟪H u, u⟫_ℝ := by
      intro u
      have hloew := loewner_inv_le hF.1 hx hv
        (hess_le_sigma_sq_hess hK hF hx hv hv0) (H u)
      have hAu_le : ⟪H (A u), A u⟫_ℝ ≤ (sigma K x v) ^ 2 * ⟪H u, u⟫_ℝ := by
        rw [hAu_sq u]
        have hrew : ⟪(hess F x).inverse (H u), H u⟫_ℝ = ⟪H u, u⟫_ℝ := by
          simp only [H, inv_apply_hess hF.1 hx u, real_inner_comm]
        rwa [hrew] at hloew
      have hcs := cauchy_schwarz_of_symm_nonneg H (hess_symm hF.1 hx) (hess_nonneg hF.1 hx) (A u) u
      have hsq : ⟪H (A u), u⟫_ℝ ^ 2 ≤ (sigma K x v * ⟪H u, u⟫_ℝ) ^ 2 := by
        calc
          ⟪H (A u), u⟫_ℝ ^ 2 ≤ ⟪H (A u), A u⟫_ℝ * ⟪H u, u⟫_ℝ := hcs
          _ ≤ ((sigma K x v) ^ 2 * ⟪H u, u⟫_ℝ) * ⟪H u, u⟫_ℝ :=
            mul_le_mul_of_nonneg_right hAu_le (hess_nonneg hF.1 hx u)
          _ = (sigma K x v * ⟪H u, u⟫_ℝ) ^ 2 := by ring
      have hrhs_nn : 0 ≤ sigma K x v * ⟪H u, u⟫_ℝ :=
        mul_nonneg hσxv_pos.le (hess_nonneg hF.1 hx u)
      nlinarith [sq_nonneg (sigma K x v * ⟪H u, u⟫_ℝ - ⟪H (A u), u⟫_ℝ)]
    -- Lower bound: (σ_v(x))⁻¹ * ⟪H u, u⟫ ≤ ⟪H (A u), u⟫
    have hσvx_pos : 0 < sigma K v x := sigma_pos_of_interior hK hv hx hx0
    have hw_le_σvx : ∀ z, ⟪hess F w z, z⟫_ℝ ≤ sigma K v x * ⟪H z, z⟫_ℝ := by
      intro z
      have hloew := loewner_inv_le hF.1 hv hx
        (hess_le_sigma_sq_hess hK hF hv hx hx0) (hess F w z)
      have hinv_v_w : ⟪(hess F v).inverse (hess F w z), hess F w z⟫_ℝ =
          ⟪H z, z⟫_ℝ := by
        rw [hinv_v]
        simp only [ContinuousLinearMap.comp_apply, inv_apply_hess hF.1 hw z, H]
        rw [hess_inv_symm hF.1 hw (hess F x z) (hess F w z), inv_apply_hess hF.1 hw z]
      rw [hinv_v_w] at hloew
      have hcs := cauchy_schwarz_of_symm_nonneg H (hess_symm hF.1 hx) (hess_nonneg hF.1 hx)
        ((hess F x).inverse (hess F w z)) z
      have h1 : ⟪H ((hess F x).inverse (hess F w z)), z⟫_ℝ = ⟪hess F w z, z⟫_ℝ := by
        simp only [H, hess_apply_inv hF.1 hx]
      have h2 : ⟪H ((hess F x).inverse (hess F w z)), (hess F x).inverse (hess F w z)⟫_ℝ =
          ⟪(hess F x).inverse (hess F w z), hess F w z⟫_ℝ := by
        simp only [H, hess_apply_inv hF.1 hx, real_inner_comm]
      rw [h1, h2] at hcs
      have hsq : ⟪hess F w z, z⟫_ℝ ^ 2 ≤ (sigma K v x * ⟪H z, z⟫_ℝ) ^ 2 := by
        calc
          ⟪hess F w z, z⟫_ℝ ^ 2 ≤ ⟪(hess F x).inverse (hess F w z), hess F w z⟫_ℝ * ⟪H z, z⟫_ℝ := hcs
          _ ≤ ((sigma K v x) ^ 2 * ⟪H z, z⟫_ℝ) * ⟪H z, z⟫_ℝ :=
            mul_le_mul_of_nonneg_right hloew (hess_nonneg hF.1 hx z)
          _ = (sigma K v x * ⟪H z, z⟫_ℝ) ^ 2 := by ring
      have hrhs_nn : 0 ≤ sigma K v x * ⟪H z, z⟫_ℝ :=
        mul_nonneg hσvx_pos.le (hess_nonneg hF.1 hx z)
      nlinarith [sq_nonneg (sigma K v x * ⟪H z, z⟫_ℝ - ⟪hess F w z, z⟫_ℝ)]
    have hA_lower : ∀ u, (sigma K v x)⁻¹ * ⟪H u, u⟫_ℝ ≤ ⟪H (A u), u⟫_ℝ := by
      intro u
      have hloew := loewner_inv_le hF.1 hw hx hw_le_σvx (H u)
      have hrew1 : ⟪(hess F x).inverse (H u), H u⟫_ℝ = ⟪H u, u⟫_ℝ := by
        simp only [H, inv_apply_hess hF.1 hx u, real_inner_comm]
      have hrew2 : ⟪(hess F w).inverse (H u), H u⟫_ℝ = ⟪H (A u), u⟫_ℝ := by
        simp only [A, H, ContinuousLinearMap.comp_apply]
        rw [hess_symm hF.1 hx ((hess F w).inverse (hess F x u)) u]
      rw [hrew1, hrew2] at hloew
      calc
        (sigma K v x)⁻¹ * ⟪H u, u⟫_ℝ ≤ (sigma K v x)⁻¹ * (sigma K v x * ⟪H (A u), u⟫_ℝ) :=
          mul_le_mul_of_nonneg_left hloew (inv_pos.mpr hσvx_pos).le
        _ = ⟪H (A u), u⟫_ℝ := by field_simp [hσvx_pos.ne']
    -- Combine into |⟪H (T u), u⟫| ≤ |v - x|_x * ⟪H u, u⟫
    set c := absn K x p
    have hc_nn : 0 ≤ c := le_trans (sigma_mem_and_nonneg hK hx p).1 (le_max_left _ _)
    have hσ_ub : sigma K x v - 1 ≤ c := by
      have := sigma_v_le_one_add_absn hK hx (v := v)
      linarith
    have hσ_lb : 1 - (sigma K v x)⁻¹ ≤ c := one_sub_inv_sigma_le_absn hK hx hv hx0
    have hT_bound : ∀ u, |⟪H (T u), u⟫_ℝ| ≤ c * ⟪H u, u⟫_ℝ := by
      intro u
      have hTu : ⟪H (T u), u⟫_ℝ = ⟪H u, u⟫_ℝ - ⟪H (A u), u⟫_ℝ := by
        simp only [T, sub_apply, ContinuousLinearMap.id_apply, map_sub,
          inner_sub_left]
      have hnn := hess_nonneg hF.1 hx u
      rw [hTu, abs_le]
      constructor
      · have h1 := hA_upper u
        have h2 : (sigma K x v - 1) * ⟪H u, u⟫_ℝ ≤ c * ⟪H u, u⟫_ℝ :=
          mul_le_mul_of_nonneg_right hσ_ub hnn
        linarith
      · have h1 := hA_lower u
        have h2 : (1 - (sigma K v x)⁻¹) * ⟪H u, u⟫_ℝ ≤ c * ⟪H u, u⟫_ℝ :=
          mul_le_mul_of_nonneg_right hσ_lb hnn
        linarith
    rw [hdnorm_eq]
    exact polarization_bound H T (hess_symm hF.1 hx) (hF.1.2.2.2.2 x hx) hT_symm hc_nn hT_bound p

end Thm43Aux

theorem solution {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (x v : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) (hv : v ∈ interior K) :
    dnorm F v (gradient F v - gradient F x - hess F x (v - x)) ≤
      absn K x (v - x) * lnorm F x (v - x) := by
  let _ := hν
  exact Thm43Aux.theorem_4_3_aux K hK F ν hF x v hx hv
