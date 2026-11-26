-- Prove2me | solution 1 for Section5DecoderLayout.integer_matrix_direction_spec
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:52:39.42313+00:00
-- url     : https://prove2.me/submissions/54acf54a-c0a7-4af9-90f8-7fe9649fa7e1

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5CanonicalPoweredDecoder
import Definitions.Def_Section5Verified_Section5DecoderLayout
import Definitions.Def_Section5Verified_Section5ExactMatrixPowerCircuit
import Definitions.Def_Section5Verified_Section5IntegerDirectionCircuit
import Definitions.Def_Section5Verified_Section5IntegerDirectionSpec
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5IntegerSpectralBridge
import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Mathlib
import Theorems.Thm_Section5DecoderLayout_integer_matrix_direction_circuit
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives InnerProductSpace
namespace Section5DecoderLayout
end Section5DecoderLayout
open Section5DecoderLayout
theorem solution (N K b f q c : ℕ)
    (hn : N+1 ≤ 2^c) (hwidth : (K+1)*(q+1+c+1) < b)
    (hf : f ≤ (q+1)*(K+1)) (hfit : (q+1)*(K+1)+2 ≤ b+1)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1)
    (hiter : 800*((N+1:ℕ):ℝ)/ε ≤ (2:ℝ)^(K+1))
    (hbits : 144*((N+1:ℕ):ℝ)^2*(4:ℝ)^(K+1)/ε ≤ (2:ℝ)^f) :
    ∃ circ : Circuit gatesRev (Section5DecoderLayout.width N K b f),
      circ.size ≤ (88*(N+1)^3*(b+1)^3)*K+Section5DecoderLayout.decoderGateBound N b f ∧ Section5DecoderLayout.DirectionSpec N K b f q ε circ := by
  obtain ⟨circ,hc,hact⟩ := Section5DecoderLayout.integer_matrix_direction_circuit N K b f q c hn hwidth hf hfit
  refine ⟨circ,hc,?_⟩
  intro z hz hzfuture M hM w hw herror
  exact hact z hz hzfuture hM ε hε hε' hiter hbits w hw herror
