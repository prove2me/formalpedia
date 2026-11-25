-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.hpk_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:36:31.468675+00:00
-- url     : https://prove2.me/submissions/007f8a1b-e38d-463c-9c53-7fa89bf095e1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_hpk_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_sg_lt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_sg_sg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_sg_rk
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_BL_hpk_apply__1773ba6bb307

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.BL
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨sg k r i.val, sg_lt i.2⟩ : Fin _)]
  · rw [hpk_apply k r i ⟨sg k r i.val, sg_lt i.2⟩, hpk_apply' k r _ (sg_lt i.2) j, sg_sg i.2, Matrix.one_apply,
      if_pos (show ((⟨sg k r i.val, sg_lt i.2⟩ : Fin (2 * r + k + 1)).val = sg k r i.val) from rfl)]
    have hs := sg_rk (k := k) (r := r) i.2
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, if_pos rfl]
      by_cases h : i.val = r + k
      · rw [if_pos h, if_pos (hs.2 h)]; norm_num
      · rw [if_neg h, if_neg (fun h' => h (hs.1 h'))]; norm_num
    · rw [if_neg hij, if_neg (fun h : j.val = i.val => hij (Fin.ext h.symm)), mul_zero]
  · intro b _ hb; rw [hpk_apply k r i b, if_neg (fun h => hb (Fin.ext h)), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
