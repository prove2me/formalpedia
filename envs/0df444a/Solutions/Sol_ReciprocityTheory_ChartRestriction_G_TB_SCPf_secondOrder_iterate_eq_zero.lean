-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.SCPf.secondOrder_iterate_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:48:24.406461+00:00
-- url     : https://prove2.me/submissions/8395a12e-5d54-4868-bb11-ff9839bb5a0a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXHasSubst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondOrderIterateEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_secondOrder_support
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_nablaL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.TB.SCPf.nablaL_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {k : Type} [CommRing k] {ι : Type} [Fintype ι]
variable {π : Type} [Fintype π] [DecidableEq π]
namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf
theorem _root_.solution (c : ι → π) (s : ι → Bool) (κ : ι → ι → k)
    (hκ : ∀ l l', κ l l' ≠ 0 → c l = c l' ∧ s l = true ∧ s l' = false) (P : MvPolynomial ι k) (e : ℕ)
    (hP : ∀ n ∈ P.support, pairMin c s n ≤ e) (j : ℕ) (hj : e < j) :
    (secondOrder k κ)^[j] P = 0 := by
  have h : ∀ t, ∀ n ∈ ((secondOrder k κ)^[t] P).support, pairMin c s n + t ≤ e := by
    intro t
    induction t with
    | zero => simpa using hP
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact secondOrder_support c s κ hκ _ e t ih
  by_contra hne
  obtain ⟨n, hn⟩ : ((secondOrder k κ)^[j] P).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact hne
  have h2 := h j n hn
  omega
end ReciprocityTheory.ChartRestriction.G.TB.SCPf
