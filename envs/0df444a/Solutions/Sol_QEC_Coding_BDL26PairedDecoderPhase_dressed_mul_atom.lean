-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderPhase.dressed_mul_atom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T15:32:08.761315+00:00
-- url     : https://prove2.me/submissions/9393a06b-0fb0-42ac-ab82-b4f956467b28

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_phaseOperator_mul_atom

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
theorem _root_.solution (logical : Binary (Physical S (n + 2))) (s : Visible S n) :
    dressed S n logical * atom S n s =
      commutationPhase (correction S n s) logical • (toHermitianQubitOperator logical * atom S n s) := by
  rw [dressed, mul_assoc, phaseOperator_mul_atom, mul_smul_comm]
end QEC.Coding.BDL26PairedDecoderPhase
