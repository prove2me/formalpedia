-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.prepareMeasuredResources_noisyResources_toOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:27:14.250181+00:00
-- url     : https://prove2.me/submissions/2dadcfc6-5c5b-4088-83b2-f8a26ff4bc69

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open QEC.Distillation.Triorthogonal.BH12Protocol
open Semantics
open Coding
open Coding.PauliSymplectic
open BH12EvenFamily
open BH12NoisyInjection
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
namespace QEC.Distillation.Triorthogonal.BH12Protocol
theorem _root_.solution (q : Nat)
    (p : ErrorParameter) :
    (prepareMeasuredResources q (noisyResources q p)).toOperator =
      ∑ error : PhysicalError q,
        (errorWordProbability p error : Complex) •
          (errorWordBasisDensity error).toOperator := by
  rw [prepareMeasuredResources_toOperator]
  apply Finset.sum_congr rfl
  intro error _
  rw [measuredErrorWordProbability_noisyResources]
end QEC.Distillation.Triorthogonal.BH12Protocol
