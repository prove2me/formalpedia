-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_JetOfMonomialSum_snoc_const_55250f806c20
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:02.638641+00:00
-- url     : https://prove2.me/submissions/50069ea7-ff02-42b4-8248-d656fae861b7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_JetOfMonomialSumStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PJetOfMonomialSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.EffectiveHS
open GroundTheory.Heights₂.Heights.EffectiveHS.JetOfMonomialSum
open Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {x : E}
namespace GroundTheory.Heights₂.Heights.EffectiveHS.JetOfMonomialSum
theorem _root_.solution {F : Type*} (k : ℕ) (w : F) :
    (Fin.snoc (fun _ : Fin k => w) w : Fin (k + 1) → F) = fun _ => w := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
end GroundTheory.Heights₂.Heights.EffectiveHS.JetOfMonomialSum
