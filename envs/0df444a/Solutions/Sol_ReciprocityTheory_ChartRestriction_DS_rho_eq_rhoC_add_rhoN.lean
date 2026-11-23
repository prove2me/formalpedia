-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.rho_eq_rhoC_add_rhoN
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:37.265889+00:00
-- url     : https://prove2.me/submissions/1fa6a14b-bb5b-402f-ab5a-17f2f2097b89

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_RhoEqRhoCAddRhoN

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (ε : Fin n → Bool) : rho n = rhoC ε + rhoN ε := by
  classical
  funext a
  simp only [rho, rhoC, rhoN, Pi.add_apply]

  have hgt : (univ.filter fun b : Fin n => a < b ∧ ε b = ε a).card +
      (univ.filter fun b : Fin n => a < b ∧ ε b ≠ ε a).card = n - 1 - (a : ℕ) := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.Ioi a)
      (fun b => ε b = ε a)
    rw [Fin.card_Ioi] at h
    rw [← h]
    congr 2 <;> ext b <;> simp

  have hlt : (univ.filter fun b : Fin n => b < a ∧ ε b = ε a).card +
      (univ.filter fun b : Fin n => b < a ∧ ε b ≠ ε a).card = (a : ℕ) := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.Iio a)
      (fun b => ε b = ε a)
    rw [Fin.card_Iio] at h
    rw [← h]
    congr 2 <;> ext b <;> simp
  have ha := a.isLt
  have hc : ((n - 1 - (a : ℕ) : ℕ) : ℝ) = (n : ℝ) - 1 - (a : ℕ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
  have c1 := congrArg (Nat.cast : ℕ → ℝ) hgt
  have c2 := congrArg (Nat.cast : ℕ → ℝ) hlt
  push_cast at c1 c2
  rw [hc] at c1
  linarith
end ReciprocityTheory.ChartRestriction.DS
