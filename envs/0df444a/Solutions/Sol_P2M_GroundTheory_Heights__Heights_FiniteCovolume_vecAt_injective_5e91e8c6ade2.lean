-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_vecAt_injective_5e91e8c6ade2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:36:36.907812+00:00
-- url     : https://prove2.me/submissions/a61a1391-6344-4030-9f53-6b855427af08

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
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution (v : Basis ι E W) : Function.Injective (vecAt v) := by
  intro x y hxy
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
  apply v.repr.injective
  ext i
  exact w.embedding.injective (congrFun (congrFun hxy w) i)
end GroundTheory.Heights₂.Heights.FiniteCovolume
