-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:49:20.236675+00:00
-- url     : https://prove2.me/submissions/982b2c88-0e8f-46b9-9dae-f2f6b528cdcd

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation

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
    (rho : DensityOperator S.selectedSystem)
    (p : Fin (S.densityEnsembleSize rho) × Fin (Module.finrank Complex S.selectedSystem)) :
    (S.replacementFactorizedKraus rho).operator p =
      (S.prepareFactorizedBranch (S.densityEnsembleVectors rho p.1)).comp
        (LinearMap.adjoint (S.prepareFactorizedBranch
          ((stdOrthonormalBasis Complex S.selectedSystem) p.2))) :=
  rfl
end QEC.Semantics.QuditSubsystem
