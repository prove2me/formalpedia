-- Prove2me | solution 1 for QEC.QLDPC.FiniteQuditCheck.globalOperator_eq_extendLocalToRegister
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:52:25.185256+00:00
-- url     : https://prove2.me/submissions/74c21c97-8318-4340-bde6-2481b9658c6e

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Coding_QLDPC_FiniteQuditCheckPresentation

set_option autoImplicit false
noncomputable section
open QEC
open QEC.QLDPC
universe u v
open QEC.QLDPC.FiniteQuditCheck
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {alphabetSize : Nat}
namespace QEC.QLDPC.FiniteQuditCheck
theorem _root_.solution
    (check : FiniteQuditCheck ι alphabetSize) :
    check.globalOperator =
      check.region.extendLocalToRegister check.localOperator :=
  rfl
end QEC.QLDPC.FiniteQuditCheck
