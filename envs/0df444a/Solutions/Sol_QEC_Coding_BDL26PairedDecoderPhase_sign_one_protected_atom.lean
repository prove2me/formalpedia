-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderPhase.sign_one_protected_atom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:14:40.356411+00:00
-- url     : https://prove2.me/submissions/a9254027-82c6-4ffb-b3d5-64a5b14c44c8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_protected_atom
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_sign_one_operator
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
      (residual S n s E).vector.zPart) :
    (toHermitianQubitOperator (binaryMul (binarySign 1) E) * dressed S n logical -
      dressed S n logical * toHermitianQubitOperator (binaryMul (binarySign 1) E)) * atom S n s = 0 := by
  rw [sign_one_operator, neg_mul, mul_neg, neg_sub_neg, sub_mul]
  have hp := protected_atom S n s E logical hlogical hx hz
  rw [sub_mul] at hp
  exact sub_eq_zero.mpr (sub_eq_zero.mp hp).symm
end QEC.Coding.BDL26PairedDecoderPhase
