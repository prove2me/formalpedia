-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_unipRadical_le_vecFixGroup_d0154db07684
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:13:12.657704+00:00
-- url     : https://prove2.me/submissions/94757798-ab5d-4f66-a303-414bbf4699f1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsVecFixGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsComplementForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerLevi

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
open scoped ENNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]
omit [NumberField E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    unipRadical h v x₀ ≤ vecFixGroup h v x₀ :=
  fun _ hg w => (hg w).1
end GroundTheory.Heights₂.Heights.FiniteCovolume
