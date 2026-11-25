-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BlockSurjectivity_evalBlock_apply_ca2f47e524b2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:26.592905+00:00
-- url     : https://prove2.me/submissions/710dc776-b995-4912-8703-569eeaceb34d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousSepBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Module
noncomputable section
open GroundTheory.Heights₂.Heights.BlockSurjectivity
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.BlockSurjectivity
theorem _root_.solution {k₀ : ι} (w : Cone (fun _ : Unit ↦ n k₀) ℂ) (f : BlockRing n k₀) :
    evalBlock w f = evalCone w f := rfl
end GroundTheory.Heights₂.Heights.BlockSurjectivity
