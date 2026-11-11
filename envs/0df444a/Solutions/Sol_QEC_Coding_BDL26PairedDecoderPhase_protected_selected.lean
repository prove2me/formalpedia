-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderPhase.protected_selected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:03:02.147223+00:00
-- url     : https://prove2.me/submissions/8db63309-2da5-454e-9ace-dfabd52a7908

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
theorem _root_.solution (A : Finset (Visible S n)) (E logical : Binary (Physical S (n + 2)))
    (hlogical : (code S n).InBinaryNormalizer logical)
    (hx : ∀ s ∈ A, ∃ a, wordLinearMapTranspose (xSyndrome S (n + 2)) a =
      (residual S n s E).vector.xPart)
    (hz : ∀ s ∈ A, ∃ b, wordLinearMapTranspose (zSyndrome S (n + 2)) b =
      (residual S n s E).vector.zPart) :
    (toHermitianQubitOperator E * dressed S n logical - dressed S n logical * toHermitianQubitOperator E) *
      BDL26TwoSectorBadProjector.selected S (n + 2) A = 0 := by
  change _ * (∑ s ∈ A, atom S n s) = 0
  rw [Finset.mul_sum]
  exact Finset.sum_eq_zero (fun s hs => protected_atom S n s E logical hlogical (hx s hs) (hz s hs))
end QEC.Coding.BDL26PairedDecoderPhase
