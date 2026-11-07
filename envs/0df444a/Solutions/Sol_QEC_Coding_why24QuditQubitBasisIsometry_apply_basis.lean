-- Prove2me | solution 1 for QEC.Coding.why24QuditQubitBasisIsometry_apply_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:26:21.458464+00:00
-- url     : https://prove2.me/submissions/55b3a18a-c3d8-4e53-8185-fc2ae58195cc

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
namespace QEC.Coding
theorem _root_.solution (β : F1024) :
    why24QuditQubitBasisIsometry (why24QuditComputationalBasis β) =
      why24QubitComputationalBasis (why24ComputationalLabelEquiv β) := by
  exact EuclideanSpace.piLpCongrLeft_single why24ComputationalLabelEquiv β 1
end QEC.Coding
