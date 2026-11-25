-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.GS.HE_HE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:35:40.635645+00:00
-- url     : https://prove2.me/submissions/b734a73e-f77c-48a3-a6c3-4560ea057b87

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixOfPerp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_hpk_invol
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_HE_apply

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
theorem _root_.solution (x : EE k r) : HE k r (HE k r x) = x := by
  rw [HE_apply, HE_apply, WithLp.ofLp_toLp, hpk_invol]
end ReciprocityTheory.ChartRestriction.DS.Xi.GS
