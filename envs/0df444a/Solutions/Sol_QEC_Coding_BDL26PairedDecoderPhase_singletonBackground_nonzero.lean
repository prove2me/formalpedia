-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderPhase.singletonBackground_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:36:30.941237+00:00
-- url     : https://prove2.me/submissions/2ab5a177-a6a1-47f6-80b0-07e1eb738217

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_singleton_xSyndrome_ne_zero
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_singleton_zSyndrome_ne_zero


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
theorem _root_.solution (q : Physical S (n + 2)) :
    (singletonBackground S n q).1.val ≠ 0 ∧ (singletonBackground S n q).2.val ≠ 0 :=
  ⟨singleton_zSyndrome_ne_zero S (n + 2) q, singleton_xSyndrome_ne_zero S (n + 2) q⟩
end QEC.Coding.BDL26PairedDecoderPhase
