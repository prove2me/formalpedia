-- Prove2me | solution 1 for QEC.Coding.BDL26PairedDecoderGibbs.channel_right_support
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-11T08:27:35.629521+00:00
-- url     : https://prove2.me/submissions/8a7c74fc-dcb3-407a-99d0-21485922e638

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

theorem ground_adjoint_local :
    LinearMap.adjoint (groundProjector S n) = groundProjector S n :=
  CSSGibbs.projector_adjoint _ _ _ _

theorem atom_mul_correction_local (s : Visible S n) :
    atom S n s * correctionOperator S n s =
      correctionOperator S n s * groundProjector S n := by
  have h := congrArg LinearMap.adjoint (correction_mul_atom S n s)
  simpa only [Module.End.mul_eq_comp, LinearMap.adjoint_comp, atom_adjoint,
    correction_adjoint, ground_adjoint_local] using h

theorem solution (A : Op S n) :
    channel S n A * groundProjector S n = channel S n A := by
  rw [channel_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  have hr : (atom S n s * correctionOperator S n s) * groundProjector S n =
      atom S n s * correctionOperator S n s := by
    rw [atom_mul_correction_local, mul_assoc, ground_square_local]
  calc
    _ = (correctionOperator S n s * atom S n s) * A *
        ((atom S n s * correctionOperator S n s) * groundProjector S n) := by noncomm_ring
    _ = _ := by rw [hr]; noncomm_ring
