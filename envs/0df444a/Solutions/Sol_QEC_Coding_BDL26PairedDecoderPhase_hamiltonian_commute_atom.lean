-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderPhase.hamiltonian_commute_atom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:48:25.499204+00:00
-- url     : https://prove2.me/submissions/e838342a-0cb4-49e1-9c05-5ee9c12f6e6d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TransposedStoppedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_SectorTranslation
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
import Theorems.Thm_QEC_Coding_CSSGibbs_hamiltonian_syndrome_resolution
import Theorems.Thm_QEC_Coding_CSSGibbs_projector_commute


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
theorem _root_.solution (s : Visible S n) :
    Commute (hamiltonian S (n + 2)) (atom S n s) := by
  change Commute (CSSGibbs.hamiltonian (zSyndrome S (n + 2)) (xSyndrome S (n + 2))) _
  rw [CSSGibbs.hamiltonian_syndrome_resolution _ _ (row_orthogonal S (n + 2))]
  apply Commute.sum_left
  intro t _
  exact (CSSGibbs.projector_commute _ _ (row_orthogonal S (n + 2)) t _).smul_left _
end QEC.Coding.BDL26PairedDecoderPhase
