-- Prove2me | solution 1 for SelfScaledLongStep.Karmarkar.eq_7_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T01:08:50.944898+00:00
-- url     : https://prove2.me/submissions/33849244-b533-44a6-896d-34ca922c55c2

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Definitions.Def_SelfScaledLongStep_Karmarkar_Defs

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace Aux_SelfScaledLongStep_Karmarkar_eq_7_8

/-- The inverse Riesz map as a genuine `ℝ`-linear continuous map. -/
noncomputable def rieszInv (n : ℕ) :
    StrongDual ℝ (EuclideanSpace ℝ (Fin n)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun L => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm L
      map_add' := fun L M => by simp
      map_smul' := fun c L => by simp }

lemma rieszInv_apply (n : ℕ) (L : StrongDual ℝ (EuclideanSpace ℝ (Fin n))) :
    rieszInv n L = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm L := rfl

end Aux_SelfScaledLongStep_Karmarkar_eq_7_8

open Aux_SelfScaledLongStep_Karmarkar_eq_7_8 in
open SelfScaledLongStep.Karmarkar in
theorem solution
    {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (hB : Function.Surjective B)
    (c d : EuclideanSpace ℝ (Fin n)) (hd : d ∈ ConvexOptimization.dualCone K)
    (hD : ∃ (y : EuclideanSpace ℝ (Fin m)) (ζ : ℝ) (s : EuclideanSpace ℝ (Fin n)),
      s ∈ interior (ConvexOptimization.dualCone K) ∧
        ContinuousLinearMap.adjoint B y + ζ • d + s = c)
    (hnc : ∃ x₁ x₂ : EuclideanSpace ℝ (Fin n),
      KarFeasible K B d x₁ ∧ KarFeasible K B d x₂ ∧ ⟪c, x₁⟫_ℝ ≠ ⟪c, x₂⟫_ℝ)
    (xh : EuclideanSpace ℝ (Fin n)) (hxh : KarStrict K B d xh)
    (yc : EuclideanSpace ℝ (Fin m)) (pc : EuclideanSpace ℝ (Fin n))
    (hpc : SelfScaledLongStep.PrimalDual.IsProjection F B xh (cHat F ν c xh) yc pc)
    (yd : EuclideanSpace ℝ (Fin m)) (pd : EuclideanSpace ℝ (Fin n))
    (hpd : SelfScaledLongStep.PrimalDual.IsProjection F B xh (dHat F ν d xh) yd pd)
    (ζ : ℝ) :
    (lnorm F xh (karDir pc pd ζ)) ^ 2 = ⟪c - ζ • d, karDir pc pd ζ⟫_ℝ := by
  have hU : IsOpen (interior K) := isOpen_interior
  have hx : xh ∈ interior K := hxh.1
  have hν0 : ν ≠ 0 := by linarith
  have hC3on : ContDiffOn ℝ 3 F (interior K) := hF.1.1.2.1
  have hC3 : ∀ y ∈ interior K, ContDiffAt ℝ 3 F y :=
    fun y hy => hC3on.contDiffAt (hU.mem_nhds hy)
  have hdiffF : ∀ y ∈ interior K, DifferentiableAt ℝ F y :=
    fun y hy => (hC3 y hy).differentiableAt (by norm_num)
  have hD1 : DifferentiableAt ℝ (fderiv ℝ F) xh :=
    ((hC3 xh hx).fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  set D2 := fderiv ℝ (fderiv ℝ F) xh with hD2
  have hsymm : ∀ u v, D2 u v = D2 v u :=
    (hC3 xh hx).isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num)
  -- Hessian in terms of D2
  have hgrad : gradient F = (rieszInv n) ∘ fderiv ℝ F := by
    funext y; rfl
  have hH : ∀ u v, ⟪hess F xh u, v⟫_ℝ = D2 u v := by
    intro u v
    have hfd := ((rieszInv n).hasFDerivAt.comp xh hD1.hasFDerivAt).fderiv
    unfold hess
    rw [hgrad, hfd]
    show ⟪(InnerProductSpace.toDual ℝ _).symm (D2 u), v⟫_ℝ = D2 u v
    exact InnerProductSpace.toDual_symm_apply
  have hgin : ∀ y v, ⟪gradient F y, v⟫_ℝ = fderiv ℝ F y v :=
    fun y v => InnerProductSpace.toDual_symm_apply
  -- Euler identity
  have heuler : ∀ y ∈ interior K, fderiv ℝ F y y = -ν := by
    intro y hy
    have hline : HasDerivAt (fun τ : ℝ => τ • y) y 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const y
    have h1 : HasDerivAt (fun τ : ℝ => F (τ • y)) (fderiv ℝ F y y) 1 :=
      (hdiffF y hy).hasFDerivAt.comp_hasDerivAt_of_eq 1 hline (by simp)
    have h2 : HasDerivAt (fun τ : ℝ => F y - ν * Real.log τ) (-ν) 1 := by
      have := ((Real.hasDerivAt_log one_ne_zero).const_mul ν).const_sub (F y)
      simpa using this
    have heq : (fun τ : ℝ => F (τ • y)) =ᶠ[nhds 1] fun τ => F y - ν * Real.log τ := by
      filter_upwards [lt_mem_nhds (zero_lt_one : (0 : ℝ) < 1)] with τ hτ
      exact hF.1.2.2.2.1 y hy τ hτ
    exact h1.unique (h2.congr_of_eventuallyEq heq)
  -- Hessian applied to xh
  have hHx : ∀ v, D2 v xh + fderiv ℝ F xh v = 0 := by
    have hG : HasFDerivAt (fun y => fderiv ℝ F y y)
        ((fderiv ℝ F xh).comp (ContinuousLinearMap.id ℝ _) + D2.flip xh) xh :=
      hD1.hasFDerivAt.clm_apply (hasFDerivAt_id xh)
    have hG0 : HasFDerivAt (fun y => fderiv ℝ F y y) (0 : _ →L[ℝ] ℝ) xh := by
      apply (hasFDerivAt_const (-ν) xh).congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds hx] with y hy
      exact heuler y hy
    have huniq := hG.unique hG0
    intro v
    have := congrArg (fun L => L v) huniq
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.zero_apply] at this
    linarith
  -- key: gradient pairing vanishes against vectors whose Hessian image is ⟂ xh
  have hgradp : ∀ p, ⟪gradient F xh, p⟫_ℝ = -⟪hess F xh p, xh⟫_ℝ := by
    intro p
    rw [hgin, hH]
    linarith [hHx p]
  have hgx : ⟪gradient F xh, xh⟫_ℝ = -ν := by rw [hgin]; exact heuler xh hx
  have hcx : ⟪cHat F ν c xh, xh⟫_ℝ = 0 := by
    unfold cHat
    rw [inner_add_left, real_inner_smul_left, hgx]
    field_simp
    ring
  have hdx : ⟪dHat F ν d xh, xh⟫_ℝ = 0 := by
    unfold dHat
    rw [inner_add_left, real_inner_smul_left, hgx]
    field_simp
    ring
  set p := karDir pc pd ζ with hp
  have hBp : B p = 0 := by
    rw [hp]; unfold karDir; rw [map_sub, map_smul, hpc.1, hpd.1, smul_zero, sub_zero]
  have hHp : hess F xh p = (cHat F ν c xh - ContinuousLinearMap.adjoint B yc) -
      ζ • (dHat F ν d xh - ContinuousLinearMap.adjoint B yd) := by
    rw [hp]; unfold karDir
    rw [map_sub, map_smul, ← hpc.2, ← hpd.2]
    abel_nf
  have hBx : B xh = 0 := hxh.2.1
  have hHpx : ⟪hess F xh p, xh⟫_ℝ = 0 := by
    rw [hHp, inner_sub_left, real_inner_smul_left, inner_sub_left, inner_sub_left,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, hBx,
      inner_zero_right, inner_zero_right, hcx, hdx]
    ring
  have hgp : ⟪gradient F xh, p⟫_ℝ = 0 := by rw [hgradp, hHpx, neg_zero]
  have hHpp : ⟪hess F xh p, p⟫_ℝ = ⟪c - ζ • d, p⟫_ℝ := by
    rw [hHp, inner_sub_left, real_inner_smul_left, inner_sub_left, inner_sub_left,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, hBp,
      inner_zero_right, inner_zero_right]
    unfold cHat dHat
    rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, hgp,
      inner_sub_left, real_inner_smul_left]
    ring
  have hnn : 0 ≤ ⟪hess F xh p, p⟫_ℝ := by
    by_cases hp0 : p = 0
    · rw [hp0, map_zero, inner_zero_left]
    · exact (hF.1.2.2.2.2 xh hx p hp0).le
  unfold lnorm
  rw [Real.sq_sqrt hnn, hHpp]
