-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_continuous_unipCoord_2bb02502c78f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:50:18.738707+00:00
-- url     : https://prove2.me/submissions/e77bb777-8238-4649-968d-d8546eff6ff0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipotentCoordProper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology
noncomputable section
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
  [NumberField E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) :
    Continuous (unipCoord h v x₀ w₀) := by
  refine continuous_pi fun w => ?_
  have hc : Continuous fun n : unipRadical h v x₀ =>
      (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) :=
    Units.continuous_val.comp ((continuous_apply w).comp
      (continuous_subtype_val.comp continuous_subtype_val))
  exact (hc.matrix_mulVec continuous_const).sub continuous_const
end GroundTheory.Heights₂.Heights.FiniteCovolume
