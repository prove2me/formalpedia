-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.GS.star_sgn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:01:26.046805+00:00
-- url     : https://prove2.me/submissions/f887d8e0-5cf7-4f32-9821-bcf2d660e326

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixOfPerp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.GS
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {k r : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.GS
theorem _root_.solution (i : Fin (2 * r + k + 1)) : star (sgnI k r i) = sgnI k r i := by
  unfold sgnI; split_ifs <;> simp
end ReciprocityTheory.ChartRestriction.DS.Xi.GS
