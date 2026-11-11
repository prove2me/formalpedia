-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderPhase.residual_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:47:20.533037+00:00
-- url     : https://prove2.me/submissions/664f855c-937b-437d-b744-37618e54cc1d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_translation_coordinates
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_pairedResidual_phase


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
theorem _root_.solution (s : Visible S n) (E : Binary (Physical S (n + 2))) :
    (residual S n s E).phase = E.phase +
      (∑ q, xCorrection S n s.1 q * E.vector.zPart q) +
      ∑ q, (E.vector.xPart q + xCorrection S n s.1 q) *
        zCorrection S n (translation S n E s).2 q := by
  rw [translation_coordinates]
  exact pairedResidual_phase S n s.1 s.2 E
end QEC.Coding.BDL26PairedDecoderPhase
