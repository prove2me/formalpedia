-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.blockCoordEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:17:05.636809+00:00
-- url     : https://prove2.me/submissions/7948515d-a466-4754-bab6-343a8e9099a0

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {B n : ℕ} (y : Fin B → EuclideanSpace ℂ (Fin n)) (p : Fin B × Fin n) :
    blockCoordEquiv B n y p = WithLp.ofLp (y p.1) p.2 := rfl
end ReciprocityTheory.MultiplicativeHeights
