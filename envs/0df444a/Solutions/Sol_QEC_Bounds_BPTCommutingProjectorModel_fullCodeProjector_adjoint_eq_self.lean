-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.fullCodeProjector_adjoint_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:11:04.254115+00:00
-- url     : https://prove2.me/submissions/6971e794-25c5-438e-b23c-e2d61bf9a80b

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projector_adjoint_eq_self
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_adjoint_eq_self


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {κ : Type v} [Fintype κ]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution (M : BPTCommutingProjectorModel L κ) :
    LinearMap.adjoint M.fullCodeProjector = M.fullCodeProjector :=
  M.codeSpace.projector_adjoint_eq_self
end QEC.Bounds.BPTCommutingProjectorModel
