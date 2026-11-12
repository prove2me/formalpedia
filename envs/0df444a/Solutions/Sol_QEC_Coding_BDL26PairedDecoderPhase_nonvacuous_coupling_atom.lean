-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderPhase.nonvacuous_coupling_atom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:21:17.649237+00:00
-- url     : https://prove2.me/submissions/d72e6e24-2da5-4d2e-98c4-6d5b14f846e4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_atom_ne_zero
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_coupling_ne_zero
import Theorems.Thm_QEC_Coding_BDL26SectorTranslation_atom_ne_zero


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
theorem _root_.solution (q : Physical S (n + 2)) (axis : CSSDaviesLocality.Axis)
    (s : Visible S n) :
    BDL26CSSDaviesLocality.coupling S (n + 2) q axis ≠ 0 ∧ atom S n s ≠ 0 :=
  ⟨BDL26CSSDaviesLocality.coupling_ne_zero S (n + 2) q axis, atom_ne_zero S n s⟩
end QEC.Coding.BDL26PairedDecoderPhase
