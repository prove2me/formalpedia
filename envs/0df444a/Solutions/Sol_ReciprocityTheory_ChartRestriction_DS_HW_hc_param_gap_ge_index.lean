-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.hc_param_gap_ge_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:13:09.632386+00:00
-- url     : https://prove2.me/submissions/b1f45605-490b-4a1c-bae0-69bafcb173ae

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_HcParamGapGeIndex

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
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (lam : Fin n → ℝ) (hlam : IsHCParam lam) (a b : Fin n) (hab : a ≤ b) :
    ((b : ℕ) : ℝ) - (a : ℕ) ≤ lam a - lam b := by

  have gap : ∀ i j : Fin n, i < j → lam j + 1 ≤ lam i := by
    intro i j hij
    obtain ⟨mi, hi⟩ := hlam.2 i
    obtain ⟨mj, hj⟩ := hlam.2 j
    have hlt : lam j < lam i := hlam.1 hij
    have h1 : (mj : ℝ) < mi := by linarith
    have h2 : mj < mi := by exact_mod_cast h1
    have h3 : (mj : ℝ) + 1 ≤ mi := by
      have := Int.add_one_le_of_lt h2
      exact_mod_cast this
    linarith
  have key : ∀ k : ℕ, ∀ c : Fin n, a ≤ c → (c : ℕ) = a + k → ((c : ℕ) : ℝ) - (a : ℕ) ≤ lam a - lam c := by
    intro k
    induction k with
    | zero =>
      intro c _ hc
      have : c = a := Fin.ext (by omega)
      subst this
      simp
    | succ k ih =>
      intro c hac hc
      have hc1 : (c : ℕ) - 1 < n := by omega
      let c' : Fin n := ⟨(c : ℕ) - 1, hc1⟩
      have hac' : a ≤ c' := Fin.le_def.mpr (by show (a : ℕ) ≤ (c : ℕ) - 1; omega)
      have hc' : (c' : ℕ) = a + k := by show (c : ℕ) - 1 = _; omega
      have h1 := ih c' hac' hc'
      have h2 := gap c' c (Fin.lt_def.mpr (by show (c : ℕ) - 1 < c; omega))
      have h3 : ((c : ℕ) : ℝ) = ((c' : ℕ) : ℝ) + 1 := by
        rw [show (c : ℕ) = (c' : ℕ) + 1 by show (c : ℕ) = (c : ℕ) - 1 + 1; omega]
        push_cast
        ring
      linarith
  have hab' := Fin.le_def.mp hab
  exact key ((b : ℕ) - a) b hab (by omega)
end ReciprocityTheory.ChartRestriction.DS.HW
