-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_addBlockPt_eq_joinPt_6641156ea292
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:09:50.109037+00:00
-- url     : https://prove2.me/submissions/7bcd5ac3-6b3a-474d-ae38-e6566092fd16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsGluing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_LocallyFreeSpreadHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_AddBlockPullbackOfChartBundlePullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} {ι : K → Type} {κ : Type}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {Ω Ω' : Type} [Field Ω] [Field Ω'] [Algebra Ω Ω']
    (y : (Σ k, ι k) → Ω) (z : κ → Ω') :
    addBlockPt (Ω := Ω) (Ω' := Ω') y z =
      IndefiniteRowSideFullHecke.Antisym.joinPt (fun q => algebraMap Ω Ω' (y q))
        (fun q : (Σ _ : Unit, κ) => z q.2) ∘ addBlockIdxEquiv := by
  funext q
  rcases q with ⟨_ | k, i⟩ <;> rfl
end GroundTheory.Heights₂.Heights
