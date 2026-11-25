-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Xi_GS_phiV__iso__adcc9f6fb623
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:52:33.578936+00:00
-- url     : https://prove2.me/submissions/bd5ac3ba-bf31-49b6-81fc-a0a139eff684

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ExistsKmat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ProdIicCastLE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_pe_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_herm_eq


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
theorem _root_.solution (hk : 1 ≤ k) (a b : Fin (r + 1)) : herm (Hpk k r) (phiV' k r a) (phiV' k r b) = 0 := by
  rw [herm_eq]; exact pe_iso hk b a
end ReciprocityTheory.ChartRestriction.DS.Xi.GS
