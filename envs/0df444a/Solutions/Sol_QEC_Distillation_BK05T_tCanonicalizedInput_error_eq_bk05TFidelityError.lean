-- Prove2me | solution 1 for QEC.Distillation.BK05T.tCanonicalizedInput_error_eq_bk05TFidelityError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:48:01.708529+00:00
-- url     : https://prove2.me/submissions/789611ad-aec6-42af-b050-ba7f3c2f4315

import Definitions.Def_QEC_Distillation_FiveQubitT_Postselection
import Definitions.Def_QEC_Distillation_FiveQubitT_Recurrence
import Theorems.Thm_QEC_Distillation_BK05T_tCanonicalizedInput_error_eq_one_sub_tFidelity_sq


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open OneQubitMagic
namespace QEC.Distillation.BK05T
theorem _root_.solution
    (rho : DensityOperator QubitSpace) :
    tInputError (tCanonicalizedInput rho) = bk05TFidelityError rho := by
  exact tCanonicalizedInput_error_eq_one_sub_tFidelity_sq rho
end QEC.Distillation.BK05T
