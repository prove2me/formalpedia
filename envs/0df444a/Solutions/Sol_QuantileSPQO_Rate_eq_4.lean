-- Prove2me | solution 1 for QuantileSPQO.Rate.eq_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T20:15:07.249238+00:00
-- url     : https://prove2.me/submissions/113fc303-d6a6-4e9b-aa3e-e268e50e0e0e

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_QuantileSPQO_Rate_Setting

open Filter Topology
open QuantileSPQO.Rate
open scoped RealInnerProductSpace

theorem solution {d : ℕ} (M : Model d) (Θ : Set (E d)) (hM : IsQuantileModel M Θ) (θ : E d)
    (hq : DifferentiableAt ℝ M.qf θ) (hF : DifferentiableAt ℝ (cdfU M) (M.qf θ, θ))
    (hf : M.dens (M.qf θ) θ ≠ 0) :
    gradient M.qf θ = -(M.dens (M.qf θ) θ)⁻¹ • gradθ M (M.qf θ) θ := by
  set y0 := M.qf θ with hy0
  set L := fderiv ℝ (cdfU M) (y0, θ) with hL
  have hFd : HasFDerivAt (cdfU M) L (y0, θ) := hF.hasFDerivAt
  set Dq := fderiv ℝ M.qf θ with hDq
  have hqd : HasFDerivAt M.qf Dq θ := hq.hasFDerivAt
  -- total derivative along θ' ↦ (q θ', θ') vanishes
  have hpath : HasFDerivAt (fun θ' => (M.qf θ', θ')) (Dq.prod (ContinuousLinearMap.id ℝ (E d))) θ :=
    hqd.prodMk (hasFDerivAt_id θ)
  have hcomp : HasFDerivAt (fun θ' => cdfU M (M.qf θ', θ'))
      (L.comp (Dq.prod (ContinuousLinearMap.id ℝ (E d)))) θ :=
    HasFDerivAt.comp (g := cdfU M) (f := fun θ' => (M.qf θ', θ')) θ hFd hpath
  have hconst : (fun θ' => cdfU M (M.qf θ', θ')) = fun _ => M.φ := by
    funext θ'; exact hM.quantile θ'
  rw [hconst] at hcomp
  have hzero : L.comp (Dq.prod (ContinuousLinearMap.id ℝ (E d))) = 0 :=
    hcomp.unique (hasFDerivAt_const _ _)
  -- partial derivative in y
  have hy : HasFDerivAt (fun y => cdfU M (y, θ)) (L.comp (ContinuousLinearMap.inl ℝ ℝ (E d))) y0 :=
    HasFDerivAt.comp (g := cdfU M) (f := fun y => (y, θ)) y0 hFd
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) y0 θ)
  have hy' : HasDerivAt (fun y => cdfU M (y, θ)) (M.dens y0 θ) y0 := hM.hasDens y0 θ
  have hdens : L (1, 0) = M.dens y0 θ := by
    have := hy'.hasFDerivAt.unique hy
    have h2 := congrArg (fun T : ℝ →L[ℝ] ℝ => T 1) this
    simp at h2
    exact h2.symm
  -- partial derivative in θ
  have hθ : HasFDerivAt (fun θ' => cdf M y0 θ') (L.comp (ContinuousLinearMap.inr ℝ ℝ (E d))) θ :=
    HasFDerivAt.comp (g := cdfU M) (f := fun θ' => (y0, θ')) θ hFd
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) y0 θ)
  have hgradθ : gradθ M y0 θ =
      (InnerProductSpace.toDual ℝ (E d)).symm (L.comp (ContinuousLinearMap.inr ℝ ℝ (E d))) := by
    simp only [gradθ, gradient, hθ.fderiv]
  apply ext_inner_right ℝ
  intro v
  have hv := congrArg (fun T : E d →L[ℝ] ℝ => T v) hzero
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] at hv
  have hsplit : L (Dq v, v) = Dq v * L (1, 0) + L (0, v) := by
    have : ((Dq v, v) : ℝ × E d) = Dq v • ((1 : ℝ), (0 : E d)) + ((0 : ℝ), v) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  rw [hsplit, hdens] at hv
  rw [hgradθ, real_inner_smul_left, gradient, InnerProductSpace.toDual_symm_apply,
    InnerProductSpace.toDual_symm_apply]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  field_simp
  linarith
