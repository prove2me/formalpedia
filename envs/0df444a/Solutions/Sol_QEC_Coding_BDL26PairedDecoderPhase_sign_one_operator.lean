-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderPhase.sign_one_operator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:26:59.802493+00:00
-- url     : https://prove2.me/submissions/b9e7c606-a9bc-462b-8552-2f455329c9ae

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binarySign_mul


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedDecoderPhase
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26TransposedStoppedDecoder
open StabilizerCode.DecoderDressedLogical
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26PairedDecoderPhase._p2m_local_instance_6635fd3be7_27
attribute [local instance] QEC.Coding.BDL26PairedDecoderPhase._p2m_local_instance_6635fd3be7_28
namespace QEC.Coding.BDL26PairedDecoderPhase
theorem _root_.solution (E : Binary (Physical S (n + 2))) :
    toHermitianQubitOperator (binaryMul (binarySign 1) E) = -toHermitianQubitOperator E := by
  rw [toHermitianQubitOperator_binarySign_mul]
  norm_num [binaryPhaseScalar]
end QEC.Coding.BDL26PairedDecoderPhase
