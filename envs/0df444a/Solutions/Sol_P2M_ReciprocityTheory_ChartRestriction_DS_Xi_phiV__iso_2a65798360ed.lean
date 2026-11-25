-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Xi_phiV__iso_2a65798360ed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:59:54.752783+00:00
-- url     : https://prove2.me/submissions/8b8ed25c-ee4a-4e7a-a28b-a1a38fc34cde

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ExistsKmat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ProdIicCastLE
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_GS_phiV__iso__adcc9f6fb623

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
namespace ReciprocityTheory.ChartRestriction.DS.Xi
theorem _root_.solution (k r : ℕ) (hk : 1 ≤ k) (a b : Fin (r + 1)) :
    herm (Hpk k r) (phiV' k r a) (phiV' k r b) = 0 := GS.phiV'_iso' hk a b
end ReciprocityTheory.ChartRestriction.DS.Xi
