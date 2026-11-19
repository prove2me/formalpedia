-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.sourceAReturnedHInfidelity_le_aInputError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:32:33.621869+00:00
-- url     : https://prove2.me/submissions/2f9d087a-931c-4a1c-beb5-47385ded876a

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
import Theorems.Thm_QEC_Distillation_BK15_Threshold_sourceAReturnedH_referenceSquaredOverlap
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hDirectionFidelity_mem_Icc
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hFidelity_mem_Icc
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hProjector_isSymmetricProjection
import Theorems.Thm_QEC_Distillation_OneQubitMagic_projectionSquaredOverlap_nonneg


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Threshold
open Semantics Semantics.Qubit
open NoisyInput Protocol Recurrence
open OneQubitMagic
namespace QEC.Distillation.BK15.Threshold
theorem _root_.solution
    (sigma : DensityOperator QubitSpace) :
    1 - hFidelity (sourceA0Transport.symm.conjDensity sigma) ^ 2 <=
      aInputError sigma := by
  let returned : DensityOperator QubitSpace :=
    sourceA0Transport.symm.conjDensity sigma
  have href_le : hDirectionFidelity returned hReference <= hFidelity returned := by
    unfold hFidelity
    exact Finset.le_sup' (hDirectionFidelity returned)
      (Finset.mem_univ hReference)
  have hdir_nonneg : 0 <= hDirectionFidelity returned hReference :=
    (hDirectionFidelity_mem_Icc returned hReference).1
  have hfidelity_nonneg : 0 <= hFidelity returned :=
    (hFidelity_mem_Icc returned).1
  have hsquare : hDirectionFidelity returned hReference ^ 2 <=
      hFidelity returned ^ 2 := by
    have hfactor : 0 <=
        (hFidelity returned - hDirectionFidelity returned hReference) *
          (hFidelity returned + hDirectionFidelity returned hReference) :=
      mul_nonneg (sub_nonneg.mpr href_le)
        (add_nonneg hfidelity_nonneg hdir_nonneg)
    nlinarith
  have hoverlap := sourceAReturnedH_referenceSquaredOverlap sigma
  have hprojection_nonneg : 0 <=
      projectionSquaredOverlap (hProjector hReference) returned :=
    projectionSquaredOverlap_nonneg (hProjector hReference) returned
      (hProjector_isSymmetricProjection hReference)
  have hdirection_sq : hDirectionFidelity returned hReference ^ 2 =
      projectionSquaredOverlap (hProjector hReference) returned := by
    unfold hDirectionFidelity projectionFidelity
    rw [Real.sq_sqrt]
    exact hprojection_nonneg
  unfold aInputError
  rw [← hoverlap]
  nlinarith
end QEC.Distillation.BK15.Threshold
