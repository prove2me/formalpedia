-- Prove2me | solution 1 for PIW.AdelClassFin.svBig_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:18:41.687915+00:00
-- url     : https://prove2.me/submissions/0fd8ac4e-f916-46c7-b0c8-b2feef7c7497

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_PartShortOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SuccessiveVectorReal
import Theorems.Thm_PIW_AdelClassFin_svR_entry
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
variable {E : Type} [Field E] [NumberField E] [StarRing E]
namespace PIW.AdelClassFin
theorem _root_.solution [DecidableEq (E →+* ℂ)] {m N : ℕ} (e : Fin N → Fin m → E)
    (A : (E →+* ℂ) → Matrix (Fin m) (Fin m) ℂ) :
    (svBig e)ᴴ * blockDiagonal A * svBig e = ∑ φ, (svP e φ)ᴴ * A φ * svP e φ := by
  ext i j
  rw [svR_entry, Matrix.sum_apply]
  simp_rw [svR_entry]
  simp only [svBig, svP, Matrix.of_apply, Matrix.blockDiagonal_apply, Fintype.sum_prod_type,
    mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
end PIW.AdelClassFin
