-- Prove2me | solution 1 for P2M_GroundTheory_Automorphic_Parabolic_isUnit_det_submatrix_of_mem_blockUpper__fc1b51b4478e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:34:21.706364+00:00
-- url     : https://prove2.me/submissions/b2d918fc-6ec8-41ca-b748-5be90dd607cb

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mul_submatrix_of_mem_blockUpper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa Topology Set DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
variable (β γ : Fin n → ℕ)
variable {β γ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {q : GL (Fin n) F} (hq : q ∈ blockUpper F n γ)
    (b : ℕ) :
    IsUnit ((q : Matrix (Fin n) (Fin n) F).submatrix (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n))
      (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n))).det := by
  classical
  apply Matrix.isUnit_det_of_left_inverse (B := ((q⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).submatrix
    (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n)) (fun j : {j : Fin n // γ j ≤ b} => (j : Fin n)))
  rw [← mul_submatrix_of_mem_blockUpper hq, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  exact Matrix.submatrix_one _ Subtype.val_injective
end GroundTheory.Automorphic.Parabolic
