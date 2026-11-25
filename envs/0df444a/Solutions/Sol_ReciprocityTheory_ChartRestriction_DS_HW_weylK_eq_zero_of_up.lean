-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.weylK_eq_zero_of_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:27:14.517856+00:00
-- url     : https://prove2.me/submissions/59e9e9ce-e940-4ccf-9785-2d9c77a40b16

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_WeylVanish
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_weylK_eq_zero_of_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_exists_consec_pred
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_rhoC_consec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
private theorem int_eq_of_le_lt {x y : ℝ} (hx : ∃ m : ℤ, x = m) (hy : ∃ m : ℤ, y = m) (h1 : x ≤ y)
    (h2 : y < x + 1) : y = x := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨k, rfl⟩ := hy
  have e1 : m ≤ k := by exact_mod_cast h1
  have e2 : k < m + 1 := by exact_mod_cast h2
  have : k = m := by omega
  rw [this]
end ReciprocityTheory.ChartRestriction.DS.HW
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (ε : Fin n → Bool) (Λ μ : Fin n → ℝ) (s : Fin n) (hint : ∀ a, ∃ m : ℤ, Λ a = m)
    (hdom : KDom ε Λ) (hμ : ∀ c, ε c = ε s → μ c = Λ c + if c = s then 1 else 0)
    {a b : Fin n} (hab : a < b) (hε : ε a = ε b) (has : ε a = ε s) (hlt : μ a < μ b) : weylK ε μ = 0 := by
  have hbs' : ε b = ε s := hε.symm.trans has
  have hma := hμ a has
  have hmb := hμ b hbs'
  have hΛ := hdom a b hab hε

  have hbs : b = s := by
    by_contra hne
    rw [if_neg hne] at hmb
    split_ifs at hma <;> linarith
  subst hbs
  have has' : a ≠ b := ne_of_lt hab
  rw [if_neg has'] at hma
  rw [if_pos rfl] at hmb
  have hEq : Λ a = Λ b := int_eq_of_le_lt (hint b) (hint a) hΛ (by linarith)
  obtain ⟨a', haa', ha's, hε', hc⟩ := exists_consec_pred ε hab hε
  have hΛ' : Λ a' = Λ b := by
    have h1 : Λ b ≤ Λ a' := hdom a' b ha's hε'
    have h2 : Λ a' ≤ Λ a := by
      rcases eq_or_lt_of_le haa' with h | h
      · rw [h]
      · exact hdom a a' h (hε.trans hε'.symm)
    linarith
  have hρ := rhoC_consec ε ha's hε' hc
  have hma' := hμ a' hε'
  rw [if_neg (ne_of_lt ha's)] at hma'
  refine weylK_eq_zero_of_eq ε μ ha's hε' ?_
  simp only [Pi.add_apply]
  linarith
end ReciprocityTheory.ChartRestriction.DS.HW
