-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderPhase.residual_commutes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:22:49.352025+00:00
-- url     : https://prove2.me/submissions/402ea82e-345e-49b1-b148-0ce4190e7376

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_residual_inGeneratedGroupUpToSign
import Theorems.Thm_QEC_Coding_PauliSymplectic_commutes_comm
import Theorems.Thm_QEC_Coding_PauliSymplectic_commutes_iff_of_binaryUpToSign_left


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
theorem _root_.solution (s : Visible S n) (E logical : Binary (Physical S (n + 2)))
    (hlogical : (code S n).InBinaryNormalizer logical)
    (hx : ∃ a, wordLinearMapTranspose (xSyndrome S (n + 2)) a =
      (residual S n s E).vector.xPart)
    (hz : ∃ b, wordLinearMapTranspose (zSyndrome S (n + 2)) b =
      (residual S n s E).vector.zPart) : Commutes (residual S n s E) logical := by
  obtain ⟨g, hg, hv⟩ := residual_inGeneratedGroupUpToSign S n s E hx hz
  exact (commutes_iff_of_binaryUpToSign_left hv).mpr
    ((commutes_comm g logical).mpr (hlogical g hg))
end QEC.Coding.BDL26PairedDecoderPhase
