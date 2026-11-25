-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.GS.pe_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:07:18.260487+00:00
-- url     : https://prove2.me/submissions/120a2d3a-e3f7-4a14-934f-83a017a3663d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ExistsKmat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ProdIicCastLE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_pe_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_HE_HE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_HE_adj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_qe_orth


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
theorem _root_.solution (hk : 1 ≤ k) : Orthonormal ℂ (fun a => (WithLp.toLp 2 (phiV' k r a) : EE k r)) := by
  have h := qe_orth (k := k) (r := r) hk
  rw [orthonormal_iff_ite] at h ⊢
  intro a b; simp only [pe_eq, HE_adj, HE_HE]; exact h a b
end ReciprocityTheory.ChartRestriction.DS.Xi.GS
