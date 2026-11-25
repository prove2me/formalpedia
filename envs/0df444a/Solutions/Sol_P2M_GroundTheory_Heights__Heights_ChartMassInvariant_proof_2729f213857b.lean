-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMassInvariant_proof_2729f213857b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:08:36.915114+00:00
-- url     : https://prove2.me/submissions/952d909e-575d-4f10-a95b-c23df7fae6c2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartMassInvariant
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMongeAmpereAffineInvariance_chartMass_conj_47d12006171a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder
noncomputable section
open ChartMongeAmpereAffineInvariance
namespace GroundTheory.Heights₂.Heights
namespace ChartMassInvariant
theorem _root_.solution : ChartMassInvariant.Statement := by
  intro e M hM
  let S : Matrix (Fin (e + 1))ᵒᵈ (Fin (e + 1))ᵒᵈ ℂ := M
  have hS : S.PosDef := hM
  let P₀ : Matrix (Fin (e + 1))ᵒᵈ (Fin (e + 1))ᵒᵈ ℂ := LDL.lowerInv hS
  let P : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ := P₀
  have hPdet : P.det ≠ 0 := (isUnit_det_of_invertible P₀).ne_zero
  set T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ := Pᴴ with hTdef
  have hT : ∀ j : Fin e, T 0 j.succ = 0 := fun j => by
    have h := LDL.lowerInv_triangular hS (i := OrderDual.toDual j.succ) (j := OrderDual.toDual 0)
      (OrderDual.toDual_lt_toDual.mpr (Fin.succ_pos j))
    rw [hTdef, conjTranspose_apply, show P j.succ 0 = 0 from h, star_zero]
  have hTdet : T.det ≠ 0 := by
    rw [hTdef, det_conjTranspose]
    exact star_ne_zero.mpr hPdet
  let d₀ : (Fin (e + 1))ᵒᵈ → ℂ := LDL.diagEntries hS
  set d : Fin (e + 1) → ℂ := d₀ with hddef
  have hD : Tᴴ * M * T = diagonal d := by
    rw [hTdef, conjTranspose_conjTranspose]
    exact (LDL.diag_eq_lowerInv_conj hS).symm
  have hDpos : (diagonal d).PosDef := by
    rw [← hD]
    exact hM.conjTranspose_mul_mul_same
      (mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det T).mpr (isUnit_iff_ne_zero.mpr hTdet)))
  have hdpos : ∀ i, 0 < d i := fun i => by simpa using hDpos.diag_pos (i := i)
  set T' : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ := diagonal fun i => ((Real.sqrt (d i).re)⁻¹ : ℝ) with hT'def
  have hT' : ∀ j : Fin e, T' 0 j.succ = 0 := fun j => diagonal_apply_ne _ (Fin.succ_ne_zero j).symm
  have hT'det : T'.det ≠ 0 := by
    rw [hT'def, det_diagonal, Finset.prod_ne_zero_iff]
    intro i _
    exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_pos.mpr (Complex.pos_iff.mp (hdpos i)).1).ne')
  have h1 : T'ᴴ * diagonal d * T' = 1 := by
    rw [hT'def, diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    obtain ⟨hr, him⟩ := Complex.pos_iff.mp (hdpos i)
    set r := (d i).re with hrdef
    have hdi : d i = (r : ℂ) := Complex.ext (by simp [hrdef]) (by simp [← him])
    have key : (Real.sqrt r)⁻¹ * r * (Real.sqrt r)⁻¹ = 1 := by
      have hs : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
      rw [mul_comm, ← mul_assoc, ← mul_inv, Real.mul_self_sqrt hr.le, inv_mul_cancel₀ hr.ne']
    rw [hdi, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    exact_mod_cast key
  calc chartMass M = chartMass (Tᴴ * M * T) := (chartMass_conj M T hM hT hTdet).symm
    _ = chartMass (diagonal d) := by rw [hD]
    _ = chartMass (T'ᴴ * diagonal d * T') := (chartMass_conj _ T' hDpos hT' hT'det).symm
    _ = chartMass 1 := by rw [h1]
end ChartMassInvariant
end GroundTheory.Heights₂.Heights
