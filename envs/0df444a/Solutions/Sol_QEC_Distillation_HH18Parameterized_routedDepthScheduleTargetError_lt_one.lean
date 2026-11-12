-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthScheduleTargetError_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:01:04.419723+00:00
-- url     : https://prove2.me/submissions/7ad2ba82-e7d8-4ea9-a5ec-66af8ceb7f6b

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    routedDepthScheduleTargetError w r m epsilon depth < 1 := by
  unfold routedDepthScheduleTargetError
  have hbaseNonneg : 0 ≤ routedDepthIterationScale w r m * epsilon.1 :=
    mul_nonneg (routedDepthIterationScale_pos w r m).le epsilon.property.1
  have hdistance : 1 ≤ codeDistance r w :=
    (codeDistance_two_le h).trans' (by omega)
  have hpower : 1 ≤ codeDistance r w ^ depth :=
    one_le_pow₀ hdistance
  calc
    (routedDepthIterationScale w r m * epsilon.1) ^ (codeDistance r w ^ depth) ≤
        (1 / 4 : ℝ) ^ (codeDistance r w ^ depth) :=
      pow_le_pow_left₀ hbaseNonneg hsmall _
    _ ≤ (1 / 4 : ℝ) ^ 1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hpower
    _ < 1 := by norm_num
end QEC.Distillation.HH18Parameterized
