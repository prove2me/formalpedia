-- Prove2me | solution 1 for QEC.Coding.why24ComputationalLabelEquiv_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:15:50.519485+00:00
-- url     : https://prove2.me/submissions/5b33cdb7-d312-4cdd-b514-892521890548

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
namespace QEC.Coding
theorem _root_.solution (β : F1024) :
    PauliSymplectic.bitstringWordEquiv (Fin 10) (why24ComputationalLabelEquiv β) =
      f1024SelectedCoordinates β := by
  exact (PauliSymplectic.bitstringWordEquiv (Fin 10)).apply_symm_apply _
end QEC.Coding
