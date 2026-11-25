-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.lowComp_lin_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:22:37.50785+00:00
-- url     : https://prove2.me/submissions/eda1a171-e286-4076-bf46-90a80db8df2a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_LowComp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_lowComp_entry_wt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} {ε : Fin n → Bool}
    {M : Fin n → Fin n → Matrix ι ι ℂ} {γ : ι → Fin n → ℝ}
    (hM : Formalism.REAL.KRel ε M) (hd : ∀ a, M a a = Matrix.diagonal fun i => ((γ i a : ℝ) : ℂ))
    {a b : Fin n} (hab : a < b) (he : ε a = ε b) {j k : ι} (hne : M a b j k ≠ 0) :
    lowCompLin (γ k) = lowCompLin (γ j) + (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  have hk := lowComp_entry_wt hM hd hab he hne
  unfold lowCompLin
  simp only [hk, mul_add, mul_sub, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp
end ReciprocityTheory.ChartRestriction.DS.HW
