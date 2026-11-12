-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderPhase.actual_Y
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:13:07.024102+00:00
-- url     : https://prove2.me/submissions/c9dba529-9249-4f70-89d9-d24315cff931

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderPhase_translation_coordinates
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_coupling_y
attribute [local simp] QEC.Coding.BDL26CSSDaviesLocality.coupling_y



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
theorem _root_.solution (s : Visible S n) (q : Physical S (n + 2)) :
    translation S n (CSSDaviesLocality.singlePauli q .y) s =
      (translateX S n s.1 (Pi.single q 1), translateZ S n s.2 (Pi.single q 1)) ∧
    BDL26CSSDaviesLocality.coupling S (n + 2) q .y =
      Complex.I • (Qubit.localX q * Qubit.localZ q) :=
  ⟨translation_coordinates S n s _, BDL26CSSDaviesLocality.coupling_y S (n + 2) q⟩
end QEC.Coding.BDL26PairedDecoderPhase
