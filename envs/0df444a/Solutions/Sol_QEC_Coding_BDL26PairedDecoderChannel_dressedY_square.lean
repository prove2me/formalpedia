-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderChannel.dressedY_square
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-11T08:08:53.800582+00:00
-- url     : https://prove2.me/submissions/ea40c42e-677c-4dc9-952a-3ccb059558b7

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

theorem solution : dressedY S n * dressedY S n = 1 := by
  have hzx : dressedZ S n * dressedX S n = -(dressedX S n * dressedZ S n) :=
    (dressedPauliPair S n).z_x_anticommute
  have hxx : dressedX S n * dressedX S n = 1 := (dressedPauliPair S n).x_sq
  have hzz : dressedZ S n * dressedZ S n = 1 := (dressedPauliPair S n).z_sq
  rw [dressedY, smul_mul_smul_comm]
  have h : (dressedX S n * dressedZ S n) * (dressedX S n * dressedZ S n) = -1 := by
    calc
      _ = dressedX S n * (dressedZ S n * dressedX S n) * dressedZ S n := by simp only [mul_assoc]
      _ = -1 := by
        rw [hzx]
        calc
          _ = -((dressedX S n * dressedX S n) * (dressedZ S n * dressedZ S n)) := by noncomm_ring
          _ = -1 := by rw [hxx, hzz, one_mul]
  rw [h, Complex.I_mul_I]
  simp
