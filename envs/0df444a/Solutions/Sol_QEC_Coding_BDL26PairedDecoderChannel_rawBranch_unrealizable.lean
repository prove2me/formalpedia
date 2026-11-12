-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderChannel.rawBranch_unrealizable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:22:20.383198+00:00
-- url     : https://prove2.me/submissions/3a93e037-96e9-4e5f-bed1-79f2b65c70af

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderPhase
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedDecoderChannel
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase
open StabilizerCode.DecoderDressedLogical
open scoped BigOperators TensorProduct
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26PairedDecoderChannel._p2m_local_instance_c895a38b5b_28
attribute [local instance] QEC.Coding.BDL26PairedDecoderChannel._p2m_local_instance_c895a38b5b_29
namespace QEC.Coding.BDL26PairedDecoderChannel
theorem _root_.solution
    (w : Word (ZMod 2) (Sum (ZLabel S (n+2)) (XLabel S (n+2))))
    (hw : w ∉ CSSGibbs.realizableSyndromes (zSyndrome S (n+2)) (xSyndrome S (n+2)))
    (A : Op S n) : rawBranch S n w A = 0 := by
  apply Finset.sum_eq_zero
  intro s _
  rw [if_neg]
  intro h
  apply hw
  rw [← h]
  exact Finset.mem_map.mpr ⟨s, Finset.mem_univ _, rfl⟩
end QEC.Coding.BDL26PairedDecoderChannel
