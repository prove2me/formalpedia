-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderGibbs.channel_left_support
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-11T08:27:35.183202+00:00
-- url     : https://prove2.me/submissions/bd9c65e4-8569-402d-8a72-4b4dd707aa83

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderChannel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_GibbsSyndrome_Translation
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_PairedDecoderGibbs
import Theorems.Thm_QEC_Coding_BDL26PairedDecoderChannel_channel_apply
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedDecoderGibbs
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian BDL26PairedDecoderPhase BDL26PairedDecoderChannel
open scoped BigOperators TensorProduct
variable (S : OddScale) (n : Nat)
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_23
attribute [local instance] QEC.Coding.BDL26PairedDecoderGibbs._p2m_local_instance_0acfdf3e5b_24

theorem ground_square_local :
    groundProjector S n * groundProjector S n = groundProjector S n :=
  CSSGibbs.projector_square _ _ _ _

theorem solution (A : Op S n) :
    groundProjector S n * channel S n A = channel S n A := by
  rw [channel_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have hl : groundProjector S n * (correctionOperator S n s * atom S n s) =
      correctionOperator S n s * atom S n s := by
    rw [correction_mul_atom, ← mul_assoc, ground_square_local]
  calc
    _ = (groundProjector S n * (correctionOperator S n s * atom S n s)) *
        A * (atom S n s * correctionOperator S n s) := by noncomm_ring
    _ = _ := by rw [hl]; noncomm_ring
