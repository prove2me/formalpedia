-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.GS.sgn_sig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:39:26.598429+00:00
-- url     : https://prove2.me/submissions/4c836cdc-52a0-4b55-a3c1-700e4c03db70

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
theorem _root_.solution (i : Fin (2 * r + k + 1)) : sgnI k r (sigI k r i) = sgnI k r i := by
  unfold sgnI; rw [sigI_val]; split_ifs <;> first | rfl | (exfalso; omega)
end ReciprocityTheory.ChartRestriction.DS.Xi.GS
