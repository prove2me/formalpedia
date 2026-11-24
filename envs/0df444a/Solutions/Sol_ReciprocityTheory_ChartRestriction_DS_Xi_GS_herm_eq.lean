-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.GS.herm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:59:49.945369+00:00
-- url     : https://prove2.me/submissions/db67316d-8777-4f2b-ab67-8a1913b640c1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixOfPerp
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
theorem _root_.solution (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = inner ℂ (WithLp.toLp 2 w : EE k r) (HE k r (WithLp.toLp 2 v)) := by
  rw [HE_apply, EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, WithLp.ofLp_toLp, herm,
    dotProduct_comm]
end ReciprocityTheory.ChartRestriction.DS.Xi.GS
