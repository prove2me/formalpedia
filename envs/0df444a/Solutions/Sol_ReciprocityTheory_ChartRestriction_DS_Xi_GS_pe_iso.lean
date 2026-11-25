-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.GS.pe_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:43:15.584254+00:00
-- url     : https://prove2.me/submissions/39d16a9f-b820-4ec5-a5c9-ad359cd3d710

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ExistsKmat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ProdIicCastLE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_pe_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_HE_HE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_HE_adj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_HE_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_hpk_mulVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_inner_bvec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_phiV_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_toLp_phiV


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
theorem _root_.solution (hk : 1 ≤ k) (a b : Fin (r + 1)) :
    inner ℂ (WithLp.toLp 2 (phiV' k r a) : EE k r) (HE k r (WithLp.toLp 2 (phiV' k r b))) = 0 := by
  rw [pe_eq, pe_eq, HE_HE, HE_adj, HE_apply, WithLp.ofLp_toLp, toLp_phiV a]
  by_cases ha : a.val < r
  · rw [if_pos ha, inner_bvec, hpk_mulVec, phiV_apply]
    simp only [sigI_val, sgnI]
    split_ifs <;> first | rfl | (exfalso; omega) | simp
  · rw [if_neg ha, inner_smul_left, inner_add_left, inner_bvec, inner_bvec, hpk_mulVec, hpk_mulVec,
      phiV_apply, phiV_apply]
    simp only [sigI_val, sgnI, starRingEnd_apply]
    split_ifs <;> first | rfl | (exfalso; omega) | ring | simp
end ReciprocityTheory.ChartRestriction.DS.Xi.GS
