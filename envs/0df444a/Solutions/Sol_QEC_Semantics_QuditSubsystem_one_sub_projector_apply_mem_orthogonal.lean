-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.one_sub_projector_apply_mem_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:56:57.792434+00:00
-- url     : https://prove2.me/submissions/429ab9d7-5a35-4cdf-bc51-c866c7aea3f6

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_adjoint_eq_self
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_eq_self_of_mem


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v w
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] (C : QuantumCode H) (z : H) :
    ((1 - C.projector : Operator H) z) ∈ C.carrierᗮ := by
  rw [Submodule.mem_orthogonal']
  intro y hy
  have hprojected : inner Complex (C.projector z) y = inner Complex z y := by
    calc
      inner Complex (C.projector z) y =
          inner Complex z (LinearMap.adjoint C.projector y) :=
            (LinearMap.adjoint_inner_right (𝕜 := Complex) C.projector z y).symm
      _ = inner Complex z (C.projector y) := by
            rw [C.projector_adjoint_eq_self]
      _ = inner Complex z y := by rw [C.projector_eq_self_of_mem hy]
  change inner Complex (z - C.projector z) y = 0
  rw [inner_sub_left, hprojected]
  ring
end QEC.Semantics.QuditSubsystem
