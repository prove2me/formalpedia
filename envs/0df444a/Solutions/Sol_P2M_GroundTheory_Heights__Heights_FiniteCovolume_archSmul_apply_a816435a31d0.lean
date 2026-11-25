-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_archSmul_apply_a816435a31d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:13:01.532377+00:00
-- url     : https://prove2.me/submissions/b8c14cf6-dfaf-4e27-b16c-a32f44f5e319

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
theorem _root_.solution {h : HermitianForm F E W} {v : Basis ι E W} (g : archUnitary h v)
    (y : InfinitePlace E → ι → ℂ) (w : InfinitePlace E) :
    (g • y) w = ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ y w := rfl
end GroundTheory.Heights₂.Heights.FiniteCovolume
