-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.measurable_parameterized_select
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T22:34:33.460198+00:00
-- url     : https://prove2.me/submissions/c2554943-4b8c-4399-8960-d88ac5b28ab0

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ParameterizedExecution
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_firstBadFrom_parameter
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_firstBadFrom


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
variable {A W I : Type*} [MeasurableSpace A] [MeasurableSpace W]
variable [Fintype I] [LinearOrder I] [MeasurableSpace I]
variable (B : A → I → Set W) [∀ a i, DecidablePred (· ∈ B a i)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution
    (hB : ∀ i, MeasurableSet {z : A × W | z.2 ∈ B z.1 i}) :
    Measurable (fun z : A × W => select (B z.1) z.2) := by
  have h := measurable_firstBadFrom
    (fun i => {z : A × W | z.2 ∈ B z.1 i}) hB (Finset.univ.sort (· ≤ ·))
  convert h using 1
  funext z
  exact firstBadFrom_parameter B _ z.1 z.2
end QEC.Coding.ProbabilisticConstruction.Resampling
