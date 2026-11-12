-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderPhase.source_even_protected_atom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:16:14.9112+00:00
-- url     : https://prove2.me/submissions/e256b26d-1c74-4be6-9904-43bf82e8e70b

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
theorem _root_.solution (k : Nat) (hk : 1 ≤ k) :
    ∃ j : Nat, j + 2 = 2 * k ∧
      ∀ (s : Visible S j) (E logical : Binary (Physical S (j + 2))),
      (code S j).InBinaryNormalizer logical →
      (∃ a, wordLinearMapTranspose (xSyndrome S (j + 2)) a = (residual S j s E).vector.xPart) →
      (∃ b, wordLinearMapTranspose (zSyndrome S (j + 2)) b = (residual S j s E).vector.zPart) →
      (toHermitianQubitOperator E * dressed S j logical - dressed S j logical * toHermitianQubitOperator E) *
        atom S j s = 0 :=
  ⟨2 * (k - 1), source_even_level k hk, fun s E logical hlogical hx hz => protected_atom S _ s E logical hlogical hx hz⟩
end QEC.Coding.BDL26PairedDecoderPhase
