-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.nsmul_tmul_F
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:12:39.742101+00:00
-- url     : https://prove2.me/submissions/08468245-d0d7-44e6-9aea-f1d6823bb72c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_RationalPointsDense
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {M : ℕ}
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution (N : ℕ) (a : Af F) (e : E) : N • (a ⊗ₜ[F] e) = a ⊗ₜ[F] ((N : F) • e) := by
  first
  | (rw [Nat.cast_smul_eq_nsmul, TensorProduct.tmul_smul])
  | (induction N with
      | zero => simp
      | succ n ih => simp [succ_nsmul, ih, add_smul, TensorProduct.tmul_add])
end PI.UnitaryGroupMassFormula.UJClassFin
