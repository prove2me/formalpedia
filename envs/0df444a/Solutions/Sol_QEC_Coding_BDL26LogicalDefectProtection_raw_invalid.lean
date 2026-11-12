-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectProtection.raw_invalid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:28:38.930932+00:00
-- url     : https://prove2.me/submissions/568c5b47-ecd4-46a8-a3c7-69c4910f950d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Theorems.Thm_QEC_Coding_CSSGibbs_projector_eq_zero_of_not_realizable


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalDefectProtection
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26TransposedStoppedDecoder
open StabilizerCode.DecoderDressedLogical
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26LogicalDefectProtection._p2m_local_instance_6c2d909602_23
attribute [local instance] QEC.Coding.BDL26LogicalDefectProtection._p2m_local_instance_6c2d909602_24
namespace QEC.Coding.BDL26LogicalDefectProtection
theorem _root_.solution (w : Word (ZMod 2) (Sum (ZLabel S (n+2)) (XLabel S (n+2))))
    (hw : w ∉ CSSGibbs.realizableSyndromes (zSyndrome S (n+2)) (xSyndrome S (n+2)))
    (E : Binary (Physical S (n+2))) (O : BDL26PairedDecoderChannel.Op S n) :
    (toHermitianQubitOperator E * O - O * toHermitianQubitOperator E) * projector S (n+2) w = 0 := by
  have hz : projector S (n+2) w = 0 :=
    CSSGibbs.projector_eq_zero_of_not_realizable _ _ _ _ hw
  rw [hz, mul_zero]
end QEC.Coding.BDL26LogicalDefectProtection
