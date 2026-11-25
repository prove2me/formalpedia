-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurable_belowIndicator_b4d0ba7dc339
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:24:03.214483+00:00
-- url     : https://prove2.me/submissions/acc1960b-d549-46f9-8c99-2cd8352a6aa5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PScalingLaw
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurableSet_below_0126053ea997

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]
attribute [local instance] archMulAction
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution {h : HermitianForm F E W} {v : Basis ι E W}
    (M : Majorant h v) (y : InfinitePlace E → ι → ℂ) (t : ℝ) :
    Measurable (belowIndicator M y t) :=
  measurable_one.indicator (measurableSet_below M y t)
end GroundTheory.Heights₂.Heights.FiniteCovolume
