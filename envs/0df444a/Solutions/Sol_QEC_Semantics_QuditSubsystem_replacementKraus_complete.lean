-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.replacementKraus_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:36:14.240364+00:00
-- url     : https://prove2.me/submissions/28cf5a41-1545-489e-a4b5-43e5f123391a

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_complete

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    (S.replacementKraus rho).Complete :=
  (S.replacementFactorizedKraus rho).unitaryTransport_complete
    S.registerFactorization.symm S.registerFactorization.symm
    (S.replacementFactorizedKraus_complete rho)
end QEC.Semantics.QuditSubsystem
