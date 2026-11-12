-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderPhase.protected_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:11:49.395244+00:00
-- url     : https://prove2.me/submissions/d9e005d1-f511-4802-8154-fd2d817ea8f7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_protected_selected
import Theorems.Thm_QEC_Coding_CSSGibbs_selectedProjector_total


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
theorem _root_.solution (E logical : Binary (Physical S (n + 2)))
    (hlogical : (code S n).InBinaryNormalizer logical)
    (hx : ∀ s : Visible S n, ∃ a, wordLinearMapTranspose (xSyndrome S (n + 2)) a =
      (residual S n s E).vector.xPart)
    (hz : ∀ s : Visible S n, ∃ b, wordLinearMapTranspose (zSyndrome S (n + 2)) b =
      (residual S n s E).vector.zPart) :
    Commute (toHermitianQubitOperator E) (dressed S n logical) := by
  have h := protected_selected S n Finset.univ E logical hlogical (fun s _ => hx s) (fun s _ => hz s)
  change (toHermitianQubitOperator E * dressed S n logical -
    dressed S n logical * toHermitianQubitOperator E) *
    CSSGibbs.selectedProjector (zSyndrome S (n + 2)) (xSyndrome S (n + 2))
      (row_orthogonal S (n + 2)) Finset.univ = 0 at h
  rw [CSSGibbs.selectedProjector_total, mul_one] at h
  show toHermitianQubitOperator E * dressed S n logical = dressed S n logical * toHermitianQubitOperator E
  exact sub_eq_zero.mp h
end QEC.Coding.BDL26PairedDecoderPhase
