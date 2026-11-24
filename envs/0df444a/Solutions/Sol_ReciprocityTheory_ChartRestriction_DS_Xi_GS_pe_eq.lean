-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.GS.pe_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:15:42.030643+00:00
-- url     : https://prove2.me/submissions/5ba186e7-7daf-498d-933b-e25d7d7cbe15

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ExistsKmat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ProdIicCastLE
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
theorem _root_.solution (a : Fin (r + 1)) :
    (WithLp.toLp 2 (phiV' k r a) : EE k r) = HE k r (WithLp.toLp 2 (phiV k r a)) := by
  rw [HE_apply, WithLp.ofLp_toLp]; rfl
end ReciprocityTheory.ChartRestriction.DS.Xi.GS
