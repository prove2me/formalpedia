-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.degAdd_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:21:35.444272+00:00
-- url     : https://prove2.me/submissions/ae1cee59-584f-4783-8555-12f0744545c5

import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsIntSmulMemSpan
import Definitions.Def_ReciprocityTheory_SemistableReduction_EmbMatMulVecInjective
import Definitions.Def_ReciprocityTheory_SemistableReduction_DegAddHolds
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DegAdd_indep_parts
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DegAdd_index_split
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DegAdd_log_det_gram_append
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DegAdd_relIndex_ne_zero_of_fg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open NumberField
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution : DegAddStatement := by
  intro K _ _ r k m H L b c hH hL hb hc hlin hspan
  obtain ⟨hbi, -, hdis⟩ := DegAdd.indep_parts hlin
  have hidx := DegAdd.index_split L b c hb hc hdis
  have hne := DegAdd.relIndex_ne_zero_of_fg L hL (Fin.append b c) hspan
  rw [hidx] at hne
  have h1 := left_ne_zero_of_mul hne
  have h2 := right_ne_zero_of_mul hne
  have hs : ∑ σ : K →+* ℂ, Real.log (gramC (H σ) σ (Fin.append b c)).det.re =
      ∑ σ : K →+* ℂ, Real.log (gramC (H σ) σ b).det.re +
        ∑ σ : K →+* ℂ, Real.log (quotGramC (H σ) σ b c).det.re := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ => DegAdd.log_det_gram_append (H σ) σ b c (hH σ) hbi hlin
  unfold latDeg quotDeg
  rw [hidx, Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr h1) (Nat.cast_ne_zero.mpr h2), hs]
  ring
end ReciprocityTheory.MultiplicativeHeights
