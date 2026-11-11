-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderPhase.dressed_commute_hamiltonian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:35:30.588327+00:00
-- url     : https://prove2.me/submissions/985841c9-cf08-4ce4-b283-e62f47ecfb14

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_normalizer_commute_hamiltonian
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_phaseOperator_commute_hamiltonian

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
theorem _root_.solution (logical : Binary (Physical S (n + 2)))
    (hlogical : (code S n).InBinaryNormalizer logical) :
    Commute (dressed S n logical) (hamiltonian S (n + 2)) :=
  (normalizer_commute_hamiltonian S n logical hlogical).mul_left
    (phaseOperator_commute_hamiltonian S n logical)
end QEC.Coding.BDL26PairedDecoderPhase
