-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderPhase.coupling_protected_atom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:12:23.874474+00:00
-- url     : https://prove2.me/submissions/6d27b839-990d-448f-a813-66d7aafce109

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_protected_atom

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
theorem _root_.solution (s : Visible S n) (q : Physical S (n + 2))
    (axis : CSSDaviesLocality.Axis) (logical : Binary (Physical S (n + 2)))
    (hlogical : (code S n).InBinaryNormalizer logical)
    (hx : ∃ a, wordLinearMapTranspose (xSyndrome S (n + 2)) a =
      (residual S n s (CSSDaviesLocality.singlePauli q axis)).vector.xPart)
    (hz : ∃ b, wordLinearMapTranspose (zSyndrome S (n + 2)) b =
      (residual S n s (CSSDaviesLocality.singlePauli q axis)).vector.zPart) :
    (BDL26CSSDaviesLocality.coupling S (n + 2) q axis * dressed S n logical -
      dressed S n logical * BDL26CSSDaviesLocality.coupling S (n + 2) q axis) * atom S n s = 0 :=
  protected_atom S n s (CSSDaviesLocality.singlePauli q axis) logical hlogical hx hz
end QEC.Coding.BDL26PairedDecoderPhase
