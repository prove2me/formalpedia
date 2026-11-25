-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.BigCasimir.factorAd_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:28:31.717269+00:00
-- url     : https://prove2.me/submissions/f40cb1bc-f6de-473b-afd9-f3295a22015e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Permute
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCasA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_factorAd_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_positionPerm_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_inner_ite_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_inner_ite_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.BigCasimir
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS.BigCasimir
theorem _root_.solution (k : ℕ) (i : Fin k) (a b : Fin n) (F G : Big n k M) :
    inner ℂ (factorAd k i a b F) G = inner ℂ F (factorAd k i b a G) := by
  simp only [PiLp.inner_apply, factorAd_apply, inner_sub_left, inner_sub_right, Finset.sum_sub_distrib,
    inner_ite_left, inner_ite_right]
  congr 1
  · refine Fintype.sum_equiv (positionPerm i (Equiv.prodCongr (Equiv.swap a b) (Equiv.refl _))) _ _
      fun κ => ?_
    rcases hx : κ i with ⟨x, y⟩
    simp only [positionPerm_apply, Function.update_self, Function.update_idem, hx, Equiv.prodCongr_apply,
      Prod.map, Equiv.refl_apply]
    by_cases h : x = a
    · subst h
      simp only [Equiv.swap_apply_left, if_true]
      rw [← hx, Function.update_eq_self]
    · have : Equiv.swap a b x ≠ b := by
        rw [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]; exact h
      simp [h, this]
  · refine Fintype.sum_equiv (positionPerm i (Equiv.prodCongr (Equiv.refl _) (Equiv.swap a b))) _ _
      fun κ => ?_
    rcases hx : κ i with ⟨x, y⟩
    simp only [positionPerm_apply, Function.update_self, Function.update_idem, hx, Equiv.prodCongr_apply,
      Prod.map, Equiv.refl_apply]
    by_cases h : y = b
    · subst h
      simp only [Equiv.swap_apply_right, if_true]
      rw [← hx, Function.update_eq_self]
    · have : Equiv.swap a b y ≠ a := by
        rw [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]; exact h
      simp [h, this]
end ReciprocityTheory.ChartRestriction.DS.BigCasimir
