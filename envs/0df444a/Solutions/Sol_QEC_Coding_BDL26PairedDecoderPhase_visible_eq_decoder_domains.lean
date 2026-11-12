-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderPhase.visible_eq_decoder_domains
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:10:29.345397+00:00
-- url     : https://prove2.me/submissions/35de0687-5ce8-4512-968a-bb808671ef33

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase

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
theorem _root_.solution :
    Visible S n = (XSyndromeDomain S n × ZSyndromeDomain S n) := rfl
end QEC.Coding.BDL26PairedDecoderPhase
