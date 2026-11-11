-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderPhase.pauli_mul_atom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T15:22:57.106931+00:00
-- url     : https://prove2.me/submissions/a3aec4cd-a212-4dfd-ae8f-867d3a601ed6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
import Theorems.Thm_QEC_Coding_CSSGibbs_pauli_mul_realizable_projector


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
theorem _root_.solution (E : Binary (Physical S (n + 2))) (s : Visible S n) :
    toHermitianQubitOperator E * atom S n s =
      atom S n (translation S n E s) * toHermitianQubitOperator E :=
  CSSGibbs.pauli_mul_realizable_projector _ _ (row_orthogonal S (n + 2)) E s
end QEC.Coding.BDL26PairedDecoderPhase
