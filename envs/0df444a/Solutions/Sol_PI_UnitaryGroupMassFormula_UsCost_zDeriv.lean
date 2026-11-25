-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.zDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:51:11.988072+00:00
-- url     : https://prove2.me/submissions/743a6f92-a218-49dc-914c-f7d3904fd312

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_DerivB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZDeriv
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dx_hasDerivAt
import Theorems.Thm_Formalism_FourierDecayAlt_P_directions_in_parabolic
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DA_cm_conjT
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DA_cm_inv
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DA_cm_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DA_contDiffAt_block_matrix_three
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DA_contDiffAt_block_matrix_two
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DA_hasDerivAt_block_matrix_three
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DA_hd_invT
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DA_hd_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DB_U_inv_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DB_ga_mem
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DB_line_rep
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DB_phi_rep
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DB_sum_dirZ
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DB_symmetricScalarBlockMatrix_one_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PI.UnitaryGroupMassFormula.UsCost.DA PI.UnitaryGroupMassFormula.UsCost.DB
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution : ZDeriv := by
  intro hMem hRad hSZ k p s ρ σ d hd E _ _ H hH ξ Z γ hZ hγ W
  have hZu : IsUnit (Matrix.of Z).det := isUnit_iff_ne_zero.mpr hZ
  have hg := ga_mem hMem hRad hd ξ hZ hγ

  have hΦ : ContDiffAt ℝ 1 (fun Z' : G.Mat s => gaXi k ρ σ d ξ Z' γ) Z := by
    rw [show (fun Z' : G.Mat s => gaXi k ρ σ d ξ Z' γ) = _ from funext (phi_rep hSZ ξ hZ γ)]
    have hA : ContDiffAt ℝ 1 (fun Z' : G.Mat s => (Matrix.of Z)⁻¹ * Matrix.of Z') Z :=
      cm_mul contDiffAt_const contDiffAt_id
    have hP := cm_mul (cm_mul (contDiffAt_const (c := (blk2 (1 : Matrix (Fin p) (Fin p) ℂ) (Matrix.of ξ.2.1.2) 0
      (1 : Matrix (Fin s) (Fin s) ℂ))⁻¹))
      (contDiffAt_block_matrix_two (contDiffAt_const (c := (1 : Matrix (Fin p) (Fin p) ℂ))) (contDiffAt_const (c := (0 : Matrix (Fin p) (Fin s) ℂ)))
        (contDiffAt_const (c := (0 : Matrix (Fin s) (Fin p) ℂ))) hA))
      (contDiffAt_const (c := blk2 (1 : Matrix (Fin p) (Fin p) ℂ) (Matrix.of ξ.2.1.2) 0 (1 : Matrix (Fin s) (Fin s) ℂ)))
    have hP1 : (blk2 (1 : Matrix (Fin p) (Fin p) ℂ) (Matrix.of ξ.2.1.2) 0 (1 : Matrix (Fin s) (Fin s) ℂ))⁻¹ *
        blk2 1 0 0 ((Matrix.of Z)⁻¹ * Matrix.of Z) * blk2 1 (Matrix.of ξ.2.1.2) 0 1 = 1 := by
      rw [Matrix.nonsing_inv_mul _ hZu, symmetricScalarBlockMatrix_one_zero, Matrix.mul_one, U_inv_mul]
    have hdet : ((((blk2 (1 : Matrix (Fin p) (Fin p) ℂ) (Matrix.of ξ.2.1.2) 0 (1 : Matrix (Fin s) (Fin s) ℂ))⁻¹ *
        blk2 1 0 0 ((Matrix.of Z)⁻¹ * Matrix.of Z) * blk2 1 (Matrix.of ξ.2.1.2) 0 1))ᴴ).det ≠ 0 := by
      rw [hP1]; simp
    have hmu := contDiffAt_block_matrix_three (k := k) (ρ := ρ) hP (contDiffAt_const (c := 0)) (contDiffAt_const (c := 0))
      (contDiffAt_const (c := 0))
      (contDiffAt_const (c := (1 : B.Mat k ρ))) (contDiffAt_const (c := 0)) (contDiffAt_const (c := 0))
      (contDiffAt_const (c := 0))
      (cm_mul (cm_mul (contDiffAt_const (c := G.wMat (p + s))) (cm_inv (cm_conjT hP) hdet))
        (contDiffAt_const (c := G.wMat (p + s))))
    exact cm_mul contDiffAt_const (cm_mul (cm_mul contDiffAt_const hmu) contDiffAt_const)
  have hΦd : DifferentiableAt ℝ (fun Z' : G.Mat s => gaXi k ρ σ d ξ Z' γ) Z := hΦ.differentiableAt one_ne_zero

  have hline : HasDerivAt (fun t : ℝ => gaXi k ρ σ d ξ (Z + t • W) γ)
      (gaXi k ρ σ d ξ Z γ * lamZ k ρ ξ ((Matrix.of Z)⁻¹ * Matrix.of W)) 0 := by
    rw [show (fun t : ℝ => gaXi k ρ σ d ξ (Z + t • W) γ) = _ from funext (line_rep hSZ ξ hZ γ W)]
    set Bm := (blk2 (1 : Matrix (Fin p) (Fin p) ℂ) (Matrix.of ξ.2.1.2) 0 (1 : Matrix (Fin s) (Fin s) ℂ))⁻¹ *
        blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 ((Matrix.of Z)⁻¹ * Matrix.of W) * blk2 1 (Matrix.of ξ.2.1.2) 0 1
      with hBm
    have h11 : HasDerivAt (fun t : ℝ => (1 : Matrix (Fin (p + s)) (Fin (p + s)) ℂ) + t • Bm) Bm 0 :=
      (((hasDerivAt_id' (0 : ℝ)).smul_const Bm).const_add _).congr_deriv (one_smul _ _)
    have h33 : HasDerivAt (fun t : ℝ => G.wMat (p + s) * ((1 + t • Bm)ᴴ)⁻¹ * G.wMat (p + s))
        (-(G.wMat (p + s) * Bmᴴ * G.wMat (p + s))) 0 :=
      (hd_mul (hd_mul (hasDerivAt_const (0 : ℝ) (G.wMat (p + s))) (hd_invT Bm))
        (hasDerivAt_const (0 : ℝ) (G.wMat (p + s)))).congr_deriv (by simp)
    have hmu : HasDerivAt (fun t : ℝ => muP k (p + s) ρ (1 + t • Bm)) (dmuP k (p + s) ρ Bm) 0 :=
      hasDerivAt_block_matrix_three (k := k) (ρ := ρ) h11 (hasDerivAt_const _ _) (hasDerivAt_const _ _) (hasDerivAt_const _ _)
        (hasDerivAt_const _ (1 : B.Mat k ρ)) (hasDerivAt_const _ _) (hasDerivAt_const _ _) (hasDerivAt_const _ _) h33
    exact (hd_mul (hasDerivAt_const (0 : ℝ) (gaXi k ρ σ d ξ Z γ))
      (hd_mul (hd_mul (hasDerivAt_const (0 : ℝ) (Rn k (p + s) ρ ξ.1.2)⁻¹) hmu)
        (hasDerivAt_const (0 : ℝ) (Rn k (p + s) ρ ξ.1.2)))).congr_deriv (by simp [lamZ, Bm, Matrix.mul_assoc])
  have hfd : fderiv ℝ (fun Z' : G.Mat s => gaXi k ρ σ d ξ Z' γ) Z W =
      gaXi k ρ σ d ξ Z γ * lamZ k ρ ξ ((Matrix.of Z)⁻¹ * Matrix.of W) := by
    have hlin : HasDerivAt (fun t : ℝ => Z + t • W) W 0 :=
      (((hasDerivAt_id' (0 : ℝ)).smul_const W).const_add Z).congr_deriv (one_smul _ _)
    exact (hΦd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hlin (by simp)).unique hline

  obtain ⟨U0, H', hU0, hgU0, hcd, hagree⟩ := hH _ hg
  have hH'd : DifferentiableAt ℝ H' (gaXi k ρ σ d ξ Z γ) :=
    (hcd.differentiableOn (by simp)).differentiableAt (hU0.mem_nhds hgU0)
  have hdc : Continuous fun Z' : G.Mat s => G.detM Z' :=
    Continuous.matrix_det (A := fun Z' : G.Mat s => (Matrix.of Z' : Matrix (Fin s) (Fin s) ℂ)) continuous_id
  have hev : (fun Z' : G.Mat s => H (gaXi k ρ σ d ξ Z' γ)) =ᶠ[𝓝 Z] fun Z' => H' (gaXi k ρ σ d ξ Z' γ) := by
    have h1 : ∀ᶠ Z' in 𝓝 Z, gaXi k ρ σ d ξ Z' γ ∈ U0 := hΦd.continuousAt.preimage_mem_nhds (hU0.mem_nhds hgU0)
    have h2 : ∀ᶠ Z' in 𝓝 Z, G.detM Z' ≠ 0 := hdc.continuousAt.eventually_ne hZ
    filter_upwards [h1, h2] with Z' h1 h2
    exact hagree _ h1 (ga_mem hMem hRad hd ξ h2 hγ)
  have hcomp : fderiv ℝ (fun Z' : G.Mat s => H' (gaXi k ρ σ d ξ Z' γ)) Z =
      (fderiv ℝ H' (gaXi k ρ σ d ξ Z γ)).comp (fderiv ℝ (fun Z' : G.Mat s => gaXi k ρ σ d ξ Z' γ) Z) :=
    (hH'd.hasFDerivAt.comp Z hΦd.hasFDerivAt).fderiv
  have hR : ∀ i, RdV (dirZ k ρ ξ i) H (gaXi k ρ σ d ξ Z γ) =
      fderiv ℝ H' (gaXi k ρ σ d ξ Z γ) (gaXi k ρ σ d ξ Z γ * dirZ k ρ ξ i) := by
    intro i
    have hX : B.inLie k (p + s + ρ) (dirZ k ρ ξ i) := ((P.directions_in_parabolic k (p + s) ρ ξ.1.2).2 _).1
    exact (P.BetaSesquilinearity.Dx_hasDerivAt (x := (false, dirZ k ρ ξ i)) hX hU0 hgU0 hg hH'd hagree).deriv
  rw [hev.fderiv_eq, hcomp, ContinuousLinearMap.comp_apply, hfd, ← sum_dirZ, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hR i, Matrix.mul_smul, map_smul]
end PI.UnitaryGroupMassFormula.UsCost
