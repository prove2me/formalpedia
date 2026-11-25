-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.pt_subst_agree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:42:44.817651+00:00
-- url     : https://prove2.me/submissions/8d4b12d8-219a-4894-b3a2-68d0fd2f520b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_order_prod_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_order_prod_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries
noncomputable section
variable {R : Type*} [CommRing R] {τ : Type*} {ι : Type*}
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution {σ : Type*} {A A' : σ → MvPowerSeries τ R} (hA : HasSubst A)
    (hA' : HasSubst A') (hA0 : ∀ s, constantCoeff (A s) = 0)
    (hA0' : ∀ s, constantCoeff (A' s) = 0) (K : MvPowerSeries σ R) (k : ℕ)
    (hAA : ∀ s (e : τ →₀ ℕ), e.degree < k → coeff e (A s) = coeff e (A' s))
    (hK : ∀ α, coeff α K ≠ 0 → 2 ≤ α.degree ∨ ∀ s ∈ α.support, A s = A' s) :
    ∀ e : τ →₀ ℕ, e.degree < k + 1 → coeff e (subst A K) = coeff e (subst A' K) := by
  intro e he
  rw [coeff_subst hA K e, coeff_subst hA' K e]
  refine finsum_congr fun α => ?_
  by_cases hα : coeff α K = 0
  · simp [hα]
  congr 1
  simp only [Finsupp.prod]
  rcases hK α hα with h2 | hsame
  · have hdeg : α.degree = ∑ s ∈ α.support, α s := Finsupp.degree_apply α
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have h1 := pt_order_prod_pow A hA0 α α.support
      have h1' := pt_order_prod_pow A' hA0' α α.support
      have hlt : ((e.degree : ℕ) : ℕ∞) < ((∑ s ∈ α.support, α s : ℕ) : ℕ∞) := by
        exact_mod_cast (by omega : e.degree < ∑ s ∈ α.support, α s)
      rw [coeff_of_lt_order (lt_of_lt_of_le hlt h1), coeff_of_lt_order (lt_of_lt_of_le hlt h1')]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hAA' : ∀ s, ((j + 1 : ℕ) : ℕ∞) ≤ (A s - A' s).order := fun s =>
        nat_le_order fun d hd => by rw [map_sub, hAA s d hd, sub_self]
      have h := pt_order_prod_sub hA0 hA0' hAA' α α.support
      have hlt : ((e.degree : ℕ) : ℕ∞) < ((j + ∑ s ∈ α.support, α s : ℕ) : ℕ∞) := by
        exact_mod_cast (by omega : e.degree < j + ∑ s ∈ α.support, α s)
      have hz := coeff_of_lt_order (lt_of_lt_of_le hlt h)
      rw [map_sub, sub_eq_zero] at hz
      exact hz
  · have hprod : ∏ s ∈ α.support, A s ^ α s = ∏ s ∈ α.support, A' s ^ α s :=
      Finset.prod_congr rfl fun s hs => by rw [hsame s hs]
    rw [hprod]
end ReciprocityTheory.ChartRestriction.G.Sh
