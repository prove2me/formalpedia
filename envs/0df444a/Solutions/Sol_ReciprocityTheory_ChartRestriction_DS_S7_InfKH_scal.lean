-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.InfKH.scal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:13:17.676531+00:00
-- url     : https://prove2.me/submissions/5db7ddd6-8b02-4084-9bed-a231f5878d02

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_TauPart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ByParts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_RhoEqRhoCAddRhoN
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_LowMinusUpExpand

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
variable {ε : Fin n → Bool} {lam : Fin n → ℝ}
open ReciprocityTheory.ChartRestriction.DS.S7.InfKH
variable {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7.InfKH
theorem _root_.solution (μ : Fin n → ℤ) (hμ : IsMu lam μ) (B : Matrix (Fin n) (Fin n) ℂ) :
    2 * ∑ a, (μ a : ℂ) * B a a =
      2 * ∑ a, ((lowK ε lam a : ℝ) : ℂ) * B a a + 4 * ∑ a, ((rhoC ε a : ℝ) : ℂ) * B a a := by
  have key : ∀ a, ((μ a : ℤ) : ℂ) = ((lowK ε lam a : ℝ) : ℂ) + 2 * ((rhoC ε a : ℝ) : ℂ) := by
    intro a
    have hgt1 : (univ.filter (fun b => a < b ∧ ε b = ε a)).card +
        (univ.filter (fun b => a < b ∧ ε b ≠ ε a)).card = (univ.filter (fun b => a < b)).card := by
      first
      | (have h1 := Finset.filter_card_add_filter_neg_card_eq_card
            (s := univ.filter (fun b => a < b)) (fun b => ε b = ε a)
         simpa only [Finset.filter_filter, ne_eq] using h1)
      | (have h1 := Finset.card_filter_add_card_filter_not
            (s := univ.filter (fun b => a < b)) (fun b => ε b = ε a)
         simpa only [Finset.filter_filter, ne_eq] using h1)
    have hlt1 : (univ.filter (fun b => b < a ∧ ε b = ε a)).card +
        (univ.filter (fun b => b < a ∧ ε b ≠ ε a)).card = (univ.filter (fun b => b < a)).card := by
      first
      | (have h1 := Finset.filter_card_add_filter_neg_card_eq_card
            (s := univ.filter (fun b => b < a)) (fun b => ε b = ε a)
         simpa only [Finset.filter_filter, ne_eq] using h1)
      | (have h1 := Finset.card_filter_add_card_filter_not
            (s := univ.filter (fun b => b < a)) (fun b => ε b = ε a)
         simpa only [Finset.filter_filter, ne_eq] using h1)
    have hc1 : (univ.filter (fun b : Fin n => a < b)).card + (a : ℕ) + 1 = n := by
      have ha := a.isLt
      first
      | (rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
         omega)
      | (simp only [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
         omega)
    have hc2 : (univ.filter (fun b : Fin n => b < a)).card = (a : ℕ) := by
      first
      | rw [Finset.filter_gt_eq_Iio, Fin.card_Iio]
      | simp [Finset.filter_gt_eq_Iio]
    have hr : ((μ a : ℤ) : ℝ) = lowK ε lam a + 2 * rhoC ε a := by
      rw [hμ a]
      delta lowK rhoC rhoN rho
      simp only [Pi.add_apply, Pi.sub_apply]
      have e1 : ((univ.filter (fun b => a < b ∧ ε b = ε a)).card : ℝ) +
          (univ.filter (fun b => a < b ∧ ε b ≠ ε a)).card + (a : ℕ) + 1 = n := by
        exact_mod_cast (hgt1.symm ▸ hc1 : _)
      have e2 : ((univ.filter (fun b => b < a ∧ ε b = ε a)).card : ℝ) +
          (univ.filter (fun b => b < a ∧ ε b ≠ ε a)).card = (a : ℕ) := by
        exact_mod_cast (hlt1.trans hc2)
      linarith
    have h2 := congrArg (fun r : ℝ => (r : ℂ)) hr
    push_cast at h2 ⊢
    linear_combination h2
  have e : ∑ a, (μ a : ℂ) * B a a = ∑ a, ((lowK ε lam a : ℝ) : ℂ) * B a a +
      2 * ∑ a, ((rhoC ε a : ℝ) : ℂ) * B a a := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [key a]
    ring
  rw [e]
  ring
end ReciprocityTheory.ChartRestriction.DS.S7.InfKH
