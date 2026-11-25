-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_measurableSet_below_0126053ea997
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:49:00.004327+00:00
-- url     : https://prove2.me/submissions/e00eb1b4-ed37-4918-8faa-515baa8be2d7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PScalingLaw
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_continuous_len_inv_smul_911561361b0e

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
    MeasurableSet {g : archUnitary h v | M.len (g⁻¹ • y) < t} :=
  (isOpen_lt (continuous_len_inv_smul M y) continuous_const).measurableSet
end GroundTheory.Heights₂.Heights.FiniteCovolume
