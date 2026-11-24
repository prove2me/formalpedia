-- Prove2me | solution 1 for P2M_Formalism_L2_G_Model_TS_coeffWord__69b95f085c34
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:27:21.144231+00:00
-- url     : https://prove2.me/submissions/9f85286c-0263-427f-8d6a-1c2c43332b30

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ColSums
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_CwlApplyWordAppendSingle
import Theorems.Thm_Formalism_L2_G_Model_TS_cwl_coeffT_Phi
import Theorems.Thm_Formalism_L2_G_Model_TS_cw_eval_coeffT
import Theorems.Thm_Formalism_L2_G_Model_TS_cw_eval_Phi
import Theorems.Thm_Formalism_L2_G_Model_TS_cw_foldl_point
import Theorems.Thm_Formalism_L2_G_Model_TS_cw_mem_letters
import Theorems.Thm_Formalism_L2_G_Model_TS_cw_letters_pairwise
import Theorems.Thm_Formalism_L2_G_Model_TS_cw_wordOf
import Theorems.Thm_Formalism_L2_G_Model_TS_cw_prod_pt
import Theorems.Thm_Formalism_L2_G_Model_TS_cw_ext
import Theorems.Thm_Formalism_GradedWeylDivisibility_lccomp_weight_colW_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility
namespace Formalism.L2.G.Model.TS
theorem _root_.solution : CoeffWord := by
  classical
  intro R _ r n ν F e hF he hsum
  have hw : wordOf e = (cwLetters r n).map fun l => (l.1, l.2.1, cwStrict e l.2.2) := by
    rw [cw_wordOf]
    apply List.map_congr_left
    intro l hl
    have h0 := (cw_mem_letters l).mp hl
    have hlt : l.2.2.2.val < l.2.2.1.val := by rw [h0.1, h0.2.1]; exact h0.2.2
    simp [cwStrict, hlt]
  have hnd : ((cwLetters r n).map (·.2.2)).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact cw_letters_pairwise.imp fun h => h.2
  have hmem : ∀ v : Fin r × Fin n, v ∈ (cwLetters r n).map (·.2.2) ↔ v.2.val < v.1.val := by
    intro v
    rw [List.mem_map]
    constructor
    · rintro ⟨l, hl, rfl⟩
      have h0 := (cw_mem_letters l).mp hl
      rw [h0.1, h0.2.1]; exact h0.2.2
    · intro hv
      exact ⟨(⟨v.2.val, by omega⟩, v.1, v), (cw_mem_letters _).mpr ⟨rfl, rfl, hv⟩, rfl⟩
  have hcond : ∀ u, u ∉ (cwLetters r n).map (·.2.2) → cwStrict e u = 0 := by
    intro u hu
    rw [hmem] at hu
    simp [cwStrict, hu]
  have key := cwl_coeffT_Phi (cwLetters r n) hnd F (cwStrict e)
  rw [if_pos hcond, ← hw] at key
  rw [← key, cw_eval_coeffT]
  have hid : (fun v => (C (idFrame R r n v) : MvPolynomial (Fin r × Fin n) R)) =
      idFrame (MvPolynomial (Fin r × Fin n) R) r n := by
    funext v
    simp only [idFrame]
    split_ifs <;> simp
  rw [hid, cw_eval_Phi, cw_foldl_point _ (fun l hl => (cw_mem_letters l).mp hl) cw_letters_pairwise]
  have hpt : (fun v => idFrame (MvPolynomial (Fin r × Fin n) R) r n v +
      if v ∈ (cwLetters r n).map (·.2.2) then X v else 0) = cwPt := by
    funext v
    simp only [hmem]
    rfl
  rw [hpt, cwl_iota, eval_map, eval₂_eq', coeff_sum]
  simp only [coeff_C_mul, cw_prod_pt]
  rw [Finset.sum_eq_single e]
  · rw [if_pos he, coeff_monomial, if_pos rfl, mul_one]
  · intro m hm hne
    split_ifs with hL
    · rw [coeff_monomial, if_neg, mul_zero]
      intro hs
      apply hne
      refine cw_ext m e hL he hs fun s => ?_
      rw [hsum s, ← lccomp_weight_colW_apply, hF (mem_support_iff.mp hm)]
    · simp
  · intro h
    rw [notMem_support_iff.mp h, zero_mul]
end Formalism.L2.G.Model.TS
