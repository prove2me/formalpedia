-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.pRho_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:26:31.214004+00:00
-- url     : https://prove2.me/submissions/3aba8b0c-0d2f-4561-a3cf-f7569a7a1553

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_KTypeIntDomStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_Unique
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_PrhoEntryHasDerivAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_pRho_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_pDRho_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_prho_entry_hasDerivAt

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
open scoped Kronecker
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
variable {ε : Fin n → Bool} {β : Bool}
variable (ε β)
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution (X : Matrix (Fin n) (Fin n) ℂ) (hX : inK ε X) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) (i j : pIdx ε β) :
    HasDerivAt (fun t : ℝ =>
      ((pRho ε β (γ t) : unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ)) : Matrix (pIdx ε β) (pIdx ε β) ℂ) i j)
      (pDRho ε β X i j) 0 := by
  have hf : (fun t : ℝ =>
      ((pRho ε β (γ t) : unitary (Matrix (pIdx ε β) (pIdx ε β) ℂ)) : Matrix (pIdx ε β) (pIdx ε β) ℂ) i j) =
      fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i.1.1 j.1.1 *
        star (NormedSpace.exp ((t : ℂ) • X) i.1.2 j.1.2) := by
    funext t
    rw [pRho_apply, hγ t]
  rw [hf]
  have h := (prho_entry_hasDerivAt X i.1.1 j.1.1).mul (prho_entry_hasDerivAt X i.1.2 j.1.2).star
  have hs : star (X i.1.2 j.1.2) = -X j.1.2 i.1.2 := by
    have := congrFun (congrFun (onep_skew hX) j.1.2) i.1.2
    simpa only [Matrix.conjTranspose_apply, Matrix.neg_apply] using this
  have e : X i.1.1 j.1.1 * star (NormedSpace.exp (((0 : ℝ) : ℂ) • X) i.1.2 j.1.2) +
      NormedSpace.exp (((0 : ℝ) : ℂ) • X) i.1.1 j.1.1 * star (X i.1.2 j.1.2) = pDRho ε β X i j := by
    rw [pDRho_apply, hs]
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_apply]
    split_ifs <;> simp [sub_eq_add_neg]
  exact h.congr_deriv e
end ReciprocityTheory.ChartRestriction.DS.HW
