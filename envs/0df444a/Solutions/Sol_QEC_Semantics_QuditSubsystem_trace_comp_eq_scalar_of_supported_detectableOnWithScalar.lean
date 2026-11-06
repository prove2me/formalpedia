-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.trace_comp_eq_scalar_of_supported_detectableOnWithScalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:57:03.465621+00:00
-- url     : https://prove2.me/submissions/cfd83d6f-5648-4df3-8bba-465cb527f09f

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Theorems.Thm_QEC_Semantics_DensityOperator_supportedOn_comp_projector_eq_self
import Theorems.Thm_QEC_Semantics_DensityOperator_supportedOn_projector_comp_eq_self
import Theorems.Thm_QEC_Semantics_projectorEquation_of_detectableOnWithScalar


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
    [FiniteQuantumSystem H] (C : QuantumCode H) (E : Operator H) (c : Complex)
    (hdetect : DetectableOnWithScalar C E c) (rho : DensityOperator H)
    (hsupported : DensityOperator.SupportedOn C rho) :
    LinearMap.trace Complex H (E.comp rho.toOperator) = c := by
  have hleft := DensityOperator.supportedOn_projector_comp_eq_self C rho hsupported
  have hright := DensityOperator.supportedOn_comp_projector_eq_self C rho hsupported
  have hcompression := projectorEquation_of_detectableOnWithScalar hdetect
  calc
    LinearMap.trace Complex H (E.comp rho.toOperator) =
        LinearMap.trace Complex H
          (((C.projector.comp E).comp C.projector).comp rho.toOperator) := by
            symm
            calc
              LinearMap.trace Complex H
                  (((C.projector.comp E).comp C.projector).comp rho.toOperator) =
                  LinearMap.trace Complex H (C.projector.comp (E.comp rho.toOperator)) := by
                    rw [LinearMap.comp_assoc, LinearMap.comp_assoc, hleft]
              _ = LinearMap.trace Complex H ((E.comp rho.toOperator).comp C.projector) :=
                    (LinearMap.trace_comp_comm' C.projector (E.comp rho.toOperator)).symm
              _ = LinearMap.trace Complex H (E.comp (rho.toOperator.comp C.projector)) := by
                    rw [LinearMap.comp_assoc]
              _ = LinearMap.trace Complex H (E.comp rho.toOperator) := by rw [hright]
    _ = LinearMap.trace Complex H ((c • C.projector).comp rho.toOperator) := by
          rw [hcompression]
    _ = c := by
          rw [LinearMap.smul_comp, hleft, map_smul, rho.trace_one]
          ring
end QEC.Semantics.QuditSubsystem
