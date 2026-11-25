-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.nuNext_tele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:24:24.206794+00:00
-- url     : https://prove2.me/submissions/df44dacf-ea57-40b0-b9ad-39310e3c6a0d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_sum_Ico_tele

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (ν : Fin n → ℝ) {a b : Fin n} (hba : b < a) :
    ∑ i : Fin n, (if (b : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (a : ℕ) then ν i - nuNext ν i else 0) = ν b - ν a := by
  let f : ℕ → ℝ := fun k => if h : k < n then ν ⟨k, h⟩ else 0
  have h1 : ∀ i : Fin n, (if (b : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (a : ℕ) then ν i - nuNext ν i else 0) =
      (if (b : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < (a : ℕ) then f i - f (i + 1) else 0) := by
    intro i
    simp [f, nuNext, i.isLt]
  rw [Finset.sum_congr rfl (fun i _ => h1 i),
    Fin.sum_univ_eq_sum_range (fun k => if (b : ℕ) ≤ k ∧ k < (a : ℕ) then f k - f (k + 1) else 0) n,
    ← Finset.sum_filter]
  have hfil : (Finset.range n).filter (fun k => (b : ℕ) ≤ k ∧ k < (a : ℕ)) = Finset.Ico (b : ℕ) a := by
    ext k
    have := a.isLt
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hfil, sum_Ico_tele f (b := (b : ℕ)) (a : ℕ) (Fin.lt_iff_val_lt_val.mp hba).le]
  simp [f, b.isLt, a.isLt]
end ReciprocityTheory.ChartRestriction.DS.S7
