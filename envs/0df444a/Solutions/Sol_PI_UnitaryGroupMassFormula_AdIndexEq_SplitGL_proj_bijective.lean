-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL.proj_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:27.219949+00:00
-- url     : https://prove2.me/submissions/39fae5fb-75ba-49ab-a237-0b31f5590bef

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Commensurated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitGL
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_SplitGL_mat_ext_p
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_SplitGL_unitary_iff
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_SplitGL_hermitian_map_snd
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL
open Matrix
variable {R k : Type} [CommRing R] [Field k] {n : Type} [Fintype n] [DecidableEq n]
variable (σ : R →+* R) (π : R ≃+* k × k) (hπ : ∀ r, π (σ r) = (π r).swap)
include hπ
namespace PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL
theorem _root_.solution (J : Matrix n n R) (hJ : Formalism.UG.cT σ J = J) (hdet : IsUnit J.det) :
    Function.Bijective (proj σ π J) := by
  have hJ1 : IsUnit (J.map (p1 π)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hdet.map _
  have hunit : ∀ x : Formalism.UG.UJ σ J,
      (((x : GL n R) : Matrix n n R).map (p2 π))ᵀ * J.map (p1 π) * ((x : GL n R) : Matrix n n R).map (p1 π) =
        J.map (p1 π) :=
    fun x => ((unitary_iff σ π hπ J ((x : GL n R) : Matrix n n R)).1 x.2).1
  have hinv1 : ∀ x : GL n R,
      (x : Matrix n n R).map (p1 π) * ((x⁻¹ : GL n R) : Matrix n n R).map (p1 π) = 1 := by
    intro x
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  constructor
  · intro g h hgh
    have h1 : ((g : GL n R) : Matrix n n R).map (p1 π) = ((h : GL n R) : Matrix n n R).map (p1 π) :=
      congrArg (fun u : GL n k => (u : Matrix n n k)) hgh
    have h2 : ((g : GL n R) : Matrix n n R).map (p2 π) = ((h : GL n R) : Matrix n n R).map (p2 π) := by
      have hg := hunit g
      have hh := hunit h
      rw [h1] at hg
      have e : (((g : GL n R) : Matrix n n R).map (p2 π))ᵀ * J.map (p1 π) =
          (((h : GL n R) : Matrix n n R).map (p2 π))ᵀ * J.map (p1 π) := by
        have := congrArg (fun X => X * (((h : GL n R)⁻¹ : GL n R) : Matrix n n R).map (p1 π)) (hg.trans hh.symm)
        simp only [Matrix.mul_assoc, hinv1, Matrix.mul_one] at this
        simpa only [Matrix.mul_assoc] using this
      have e' := congrArg (fun X => X * (J.map (p1 π))⁻¹) e
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ1, Matrix.mul_one] at e'
      have := congrArg Matrix.transpose e'
      simpa only [Matrix.transpose_transpose] using this
    exact Subtype.ext (Units.ext (mat_ext_p π h1 h2))
  · intro A
    let J1 : Matrix n n k := J.map (p1 π)
    let A1 : Matrix n n k := (A : Matrix n n k)
    let B : Matrix n n k := (J1 * ((A⁻¹ : GL n k) : Matrix n n k) * J1⁻¹)ᵀ
    let M : Matrix n n R := Matrix.of fun i j => π.symm (A1 i j, B i j)
    have hM1 : M.map (p1 π) = A1 := by
      ext i j
      simp [M, p1]
    have hM2 : M.map (p2 π) = B := by
      ext i j
      simp [M, p2]
    have hJ1' : IsUnit J1.det := hJ1
    have key : Bᵀ * J1 * A1 = J1 := by
      simp only [B, Matrix.transpose_transpose, Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul_cancel_left _ _ hJ1', Units.inv_mul, Matrix.mul_one]
    have hU : Formalism.UG.cT σ M * J * M = J := by
      rw [unitary_iff σ π hπ J M, hM1, hM2, hermitian_map_snd σ π hπ J hJ]
      refine ⟨key, ?_⟩
      have := congrArg Matrix.transpose key
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc] at this
      exact this
    have hdetM : IsUnit M.det := by
      have h := congrArg Matrix.det hU
      rw [Matrix.det_mul, Matrix.det_mul] at h
      have h' : IsUnit ((Formalism.UG.cT σ M).det * J.det * M.det) := by rw [h]; exact hdet
      exact isUnit_of_mul_isUnit_right h'
    refine ⟨⟨((Matrix.isUnit_iff_isUnit_det M).2 hdetM).unit, hU⟩, ?_⟩
    exact Units.ext hM1
end PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL
