-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderPhase.singletonBackground_corrections_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:13:21.515211+00:00
-- url     : https://prove2.me/submissions/158745a2-532a-4106-bc7c-39a431e301f8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_singletonBackground_nonzero
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_xCorrection_syndrome
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_zCorrection_syndrome
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
theorem _root_.solution (q : Physical S (n + 2)) :
    xCorrection S n (singletonBackground S n q).1 ≠ 0 ∧
      zCorrection S n (singletonBackground S n q).2 ≠ 0 := by
  constructor
  · intro h
    have he := xCorrection_syndrome S n (singletonBackground S n q).1
    rw [h, map_zero] at he
    exact (singletonBackground_nonzero S n q).1 he.symm
  · intro h
    have he := zCorrection_syndrome S n (singletonBackground S n q).2
    rw [h, map_zero] at he
    exact (singletonBackground_nonzero S n q).2 he.symm
end QEC.Coding.BDL26PairedDecoderPhase
