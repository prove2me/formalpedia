-- Prove2me | solution 1 for PIW.AdelClassFin.svM_conj_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:18:43.710478+00:00
-- url     : https://prove2.me/submissions/8e880cc1-e445-4fed-856d-4964213f9efa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartShortOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SuccessiveVectorMajorantE
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
open PIW PIW.AdelClassFin
open Formalism.UG NumberField Matrix
open scoped ComplexOrder
namespace PIW.AdelClassFin
theorem _root_.solution {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (d z : Fin n → ℂ) :
    star z ⬝ᵥ ((U * diagonal d * star U) *ᵥ z) =
      ∑ i, star ((star U *ᵥ z) i) * (d i * (star U *ᵥ z) i) := by
  rw [Matrix.star_eq_conjTranspose, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]
  have h : star z ᵥ* U = star (Uᴴ *ᵥ z) := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  rw [h]
  simp only [dotProduct, Pi.star_apply, Matrix.mulVec_diagonal]
end PIW.AdelClassFin
