-- Prove2me | solution 1 for PI.DvRows.GramDeterminantPositive.hmatrix_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:54:05.503441+00:00
-- url     : https://prove2.me/submissions/a28a4137-0e82-43d4-9c9b-e4614e19fc57

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_Pieces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_MulVecInjectiveOfKer
import Theorems.Thm_PI_DvRows_GramDeterminantPositive_rho_apply
import Theorems.Thm_PI_DvRows_GramDeterminantPositive_h_expand
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
open PI PI.DvRows
open PI.DvRows.GramDeterminantPositive
open Matrix
open scoped ComplexOrder
open NumberField Formalism.BasicNotions PI.Dv
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace PI.DvRows.GramDeterminantPositive
theorem _root_.solution (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) (φ : K →+* ℂ) {m m' : ℕ}
    (f : Fin m → A.V) (g : Fin m' → A.V) :
    (Matrix.of fun i j => φ (h (f i) (g j))) = (cmat A (rho φ) f)ᴴ * hmat A h φ * cmat A φ g := by
  ext i j
  simp only [of_apply, h_expand A h (f i) (g j), map_sum, map_mul, Matrix.mul_apply,
    conjTranspose_apply, cmat, hmat, rho_apply, star_star, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
end PI.DvRows.GramDeterminantPositive
