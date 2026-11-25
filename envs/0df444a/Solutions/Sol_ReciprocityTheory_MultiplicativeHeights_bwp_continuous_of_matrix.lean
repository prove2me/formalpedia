-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.bwp_continuous_of_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:04:22.600055+00:00
-- url     : https://prove2.me/submissions/de989be5-0f4b-40f0-86f9-61694cc26c33

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_BWPolyA
import Definitions.Def_ReciprocityTheory_SemistableReduction_BWPolyC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Polynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {p : ℕ} :
    Continuous (fun y : Fin p → Fin p → ℂ => Matrix.of y) := by
  first
    | exact continuous_id
    | exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp (continuous_apply i)
end ReciprocityTheory.MultiplicativeHeights
