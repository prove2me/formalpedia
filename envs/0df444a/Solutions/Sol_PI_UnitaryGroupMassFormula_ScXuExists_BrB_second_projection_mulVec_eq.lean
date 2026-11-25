-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.BrB.second_projection_mulVec_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:12:49.900066+00:00
-- url     : https://prove2.me/submissions/72b4f860-3975-4e31-9051-af2a392b8aa8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitGL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondProjectionSplitEquiv
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrB_proj_coe
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScXuExists_BrB_isUnit_det_first_projection
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_SplitGL_unitary_iff
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists PI.UnitaryGroupMassFormula.ScXuExists.BrB
open Matrix PI.UnitaryGroupMassFormula.AdIndexEq
namespace PI.UnitaryGroupMassFormula.ScXuExists.BrB
theorem _root_.solution {R k : Type} [CommRing R] [Field k] {n : Type} [Fintype n] [DecidableEq n]
    (σ : R →+* R) (π : R ≃+* k × k) (hπ : ∀ r, π (σ r) = (π r).swap) (J : Matrix n n R)
    (hdet : IsUnit J.det) (y : Formalism.UG.UJ σ J) (β β' : n → k)
    (h : β' ᵥ* J.map (SplitGL.p1 π) =
      (β ᵥ* J.map (SplitGL.p1 π)) ᵥ* (((SplitGL.proj σ π J y)⁻¹ : GL n k) : Matrix n n k)) :
    ((y : GL n R) : Matrix n n R).map (SplitGL.p2 π) *ᵥ β = β' := by
  set P := J.map (SplitGL.p1 π) with hP
  set M2 := ((y : GL n R) : Matrix n n R).map (SplitGL.p2 π) with hM2
  set T := SplitGL.proj σ π J y with hT
  have hu : M2ᵀ * P * (T : Matrix n n k) = P := by
    rw [hT, proj_coe]
    exact ((SplitGL.unitary_iff σ π hπ J _).1 y.2).1
  have hTT : (T : Matrix n n k) * ((T⁻¹ : GL n k) : Matrix n n k) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have key : M2ᵀ * P = P * ((T⁻¹ : GL n k) : Matrix n n k) := by
    calc M2ᵀ * P = M2ᵀ * P * ((T : Matrix n n k) * ((T⁻¹ : GL n k) : Matrix n n k)) := by
          rw [hTT, Matrix.mul_one]
      _ = P * ((T⁻¹ : GL n k) : Matrix n n k) := by rw [← Matrix.mul_assoc, hu]
  have h2 : (M2 *ᵥ β) ᵥ* P = β' ᵥ* P := by
    calc (M2 *ᵥ β) ᵥ* P = (β ᵥ* M2ᵀ) ᵥ* P := by rw [Matrix.vecMul_transpose]
      _ = β ᵥ* (M2ᵀ * P) := by rw [Matrix.vecMul_vecMul]
      _ = β ᵥ* (P * ((T⁻¹ : GL n k) : Matrix n n k)) := by rw [key]
      _ = (β ᵥ* P) ᵥ* ((T⁻¹ : GL n k) : Matrix n n k) := by rw [Matrix.vecMul_vecMul]
      _ = β' ᵥ* P := h.symm
  have hPu : IsUnit P.det := isUnit_det_first_projection π J hdet
  have h3 := congrArg (fun w => w ᵥ* P⁻¹) h2
  simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hPu, Matrix.vecMul_one] at h3
  exact h3
end PI.UnitaryGroupMassFormula.ScXuExists.BrB
