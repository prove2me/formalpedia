-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.GS.qe_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:56:39.54513+00:00
-- url     : https://prove2.me/submissions/0b591b9b-e7cc-419a-ac3a-be3b81560cbe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixOfPerp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ExistsKmat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_inner_bvec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_phiV_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_toLp_phiV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_hcc

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
theorem _root_.solution (hk : 1 ≤ k) : Orthonormal ℂ (fun a => (WithLp.toLp 2 (phiV k r a) : EE k r)) := by
  have key : (starRingEnd ℂ) ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := hcc
  rw [orthonormal_iff_ite]
  intro a b
  have hA := a.isLt
  have hB := b.isLt
  rw [toLp_phiV]
  by_cases ha : a.val < r
  · rw [if_pos ha, inner_bvec, phiV_apply]
    split_ifs <;> first
      | rfl
      | (exfalso; (try simp only [Fin.val_mk, Fin.ext_iff] at *) <;> omega)
      | simp
  · rw [if_neg ha, inner_smul_left, inner_add_left, inner_bvec, inner_bvec, phiV_apply, phiV_apply]
    split_ifs <;> first
      | (exfalso; (try simp only [Fin.val_mk, Fin.ext_iff] at *) <;> omega)
      | (exfalso; exact ‹¬a = b› (Fin.ext (by omega)))
      | (exfalso; simp_all; done)
      | (exfalso; simp_all <;> omega)
      | (simp; done)
      | (simp only [add_zero, zero_add, mul_one]; linear_combination (2 : ℂ) * key)
end ReciprocityTheory.ChartRestriction.DS.Xi.GS
