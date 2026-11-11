-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderPhase.bridgeError_boundaries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:58:44.085126+00:00
-- url     : https://prove2.me/submissions/3d84b707-acac-4fb8-80a5-29b8c57eaaa9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_bridgeError_residual_vectors

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
theorem _root_.solution (s t : Visible S n) :
    (∃ a, wordLinearMapTranspose (xSyndrome S (n + 2)) a =
      (residual S n s (bridgeError S n s t)).vector.xPart) ∧
    (∃ b, wordLinearMapTranspose (zSyndrome S (n + 2)) b =
      (residual S n s (bridgeError S n s t)).vector.zPart) := by
  obtain ⟨hx, hz⟩ := bridgeError_residual_vectors S n s t
  exact ⟨⟨0, by rw [map_zero, hx]⟩, ⟨0, by rw [map_zero, hz]⟩⟩
end QEC.Coding.BDL26PairedDecoderPhase
