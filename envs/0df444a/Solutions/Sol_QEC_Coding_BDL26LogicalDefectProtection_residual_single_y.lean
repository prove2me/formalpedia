-- Prove2me | solution 1 for QEC.Coding.BDL26LogicalDefectProtection.residual_single_y
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T19:23:48.377004+00:00
-- url     : https://prove2.me/submissions/6ce20d4d-b283-4d1e-bec0-b15a9ad9afd7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BoundedRateDavies
import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDefectProtection
import Theorems.Thm_QEC_Coding_BDL26CSSDaviesLocality_coupling_y
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_pairedResidual_xPart
import Theorems.Thm_QEC_Coding_BDL26TransposedStoppedDecoder_pairedResidual_zPart
attribute [local simp] QEC.Coding.BDL26CSSDaviesLocality.coupling_y



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LogicalDefectProtection
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26TransposedStoppedDecoder
open StabilizerCode.DecoderDressedLogical
open scoped BigOperators
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26LogicalDefectProtection._p2m_local_instance_6c2d909602_23
attribute [local instance] QEC.Coding.BDL26LogicalDefectProtection._p2m_local_instance_6c2d909602_24
namespace QEC.Coding.BDL26LogicalDefectProtection
theorem _root_.solution (s : Visible S n) (q : Physical S (n+2)) :
    (residual S n s (CSSDaviesLocality.singlePauli q .y)).vector.xPart = deltaX S n s.1 q ∧
    (residual S n s (CSSDaviesLocality.singlePauli q .y)).vector.zPart = deltaZ S n s.2 q ∧
    BDL26CSSDaviesLocality.coupling S (n+2) q .y = Complex.I • (Qubit.localX q * Qubit.localZ q) :=
  ⟨pairedResidual_xPart S n s.1 s.2 _, pairedResidual_zPart S n s.1 s.2 _,
    BDL26CSSDaviesLocality.coupling_y S (n+2) q⟩
end QEC.Coding.BDL26LogicalDefectProtection
