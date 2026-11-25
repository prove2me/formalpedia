-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_continuous_len_inv_smul_911561361b0e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:11:21.353903+00:00
-- url     : https://prove2.me/submissions/01ed9522-3fd7-488c-a83e-c0bb72e33854

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PScalingLaw

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
theorem _root_.solution {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (y : InfinitePlace E → ι → ℂ) : Continuous fun g : archUnitary h v => M.len (g⁻¹ • y) := by
  have hw : ∀ w, Continuous fun g : archUnitary h v => (g⁻¹ • y) w := fun w =>
    (Units.continuous_val.comp ((continuous_apply w).comp
      (continuous_subtype_val.comp continuous_inv))).matrix_mulVec continuous_const
  unfold Majorant.len
  refine Real.continuous_sqrt.comp (continuous_finset_sum _ fun w _ => ?_)
  exact Complex.continuous_re.comp
    (((continuous_star.comp (hw w))).dotProduct (continuous_const.matrix_mulVec (hw w)))
end GroundTheory.Heights₂.Heights.FiniteCovolume
