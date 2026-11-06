-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.finrank_binaryCSSLogicalBasisQuotient_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:27:45.131+00:00
-- url     : https://prove2.me/submissions/ef22b30f-971e-4a23-9f62-13d7b1242111

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_LinearCode_dual_dimension_eq_length_sub_dimension


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
open scoped BigOperators
universe u w
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι]
variable [DecidableEq ι]
omit [DecidableEq ι]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier) :
    Module.finrank (ZMod 2) (binaryCSSLogicalBasisQuotient xCode zCode) =
      Length (ZMod 2) ι - Dimension xCode - Dimension zCode := by
  have hquot :=
    Submodule.finrank_quotient_add_finrank (binaryCSSXCodeInZDual xCode zCode)
  rw [finrank_binaryCSSXCodeInZDual_eq xCode zCode hdual,
    ← Dimension_eq_finrank_carrier zCode.dual,
    LinearCode.dual_dimension_eq_length_sub_dimension] at hquot
  rw [Nat.sub_right_comm]
  rw [← hquot]
  exact (Nat.add_sub_cancel_right _ _).symm
end QEC.Coding.PauliSymplectic
