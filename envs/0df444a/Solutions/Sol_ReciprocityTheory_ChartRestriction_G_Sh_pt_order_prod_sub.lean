-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.pt_order_prod_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:35:53.633282+00:00
-- url     : https://prove2.me/submissions/81821fd8-f47d-4d8e-8486-5e93d964e697

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_order_pow_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_order_prod_pow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries
noncomputable section
section PowerSeriesAgreement
variable {R : Type*} [CommRing R] {τ : Type*} {ι : Type*}
section Fixed
variable (T : (ι → MvPowerSeries τ R) → (ι → MvPowerSeries τ R))
  (P : (ι → MvPowerSeries τ R) → Prop)
end Fixed
section Order
private theorem natCast_le_order_iff_coeff_eq_zero {f : MvPowerSeries τ R} {n : ℕ} :
    (n : ℕ∞) ≤ f.order ↔ ∀ d : τ →₀ ℕ, d.degree < n → coeff d f = 0 :=
  ⟨fun h _ hd => coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) h), nat_le_order⟩
private theorem natCast_le_order_add {f g : MvPowerSeries τ R} {n : ℕ}
    (hf : (n : ℕ∞) ≤ f.order) (hg : (n : ℕ∞) ≤ g.order) : (n : ℕ∞) ≤ (f + g).order :=
  natCast_le_order_iff_coeff_eq_zero.2 fun d hd => by
    rw [map_add, natCast_le_order_iff_coeff_eq_zero.1 hf d hd, natCast_le_order_iff_coeff_eq_zero.1 hg d hd, add_zero]
private theorem natCast_add_le_order_mul {f g : MvPowerSeries τ R} {a b : ℕ}
    (hf : (a : ℕ∞) ≤ f.order) (hg : (b : ℕ∞) ≤ g.order) : ((a + b : ℕ) : ℕ∞) ≤ (f * g).order :=
  le_trans (by rw [Nat.cast_add]; exact add_le_add hf hg) le_order_mul
private theorem natCast_le_order_of_le {f : MvPowerSeries τ R} {a b : ℕ} (hab : a ≤ b)
    (h : (b : ℕ∞) ≤ f.order) : (a : ℕ∞) ≤ f.order :=
  le_trans (Nat.cast_le.mpr hab) h
private theorem one_le_order_of_constantCoeff_eq_zero {f : MvPowerSeries τ R} (hf : constantCoeff f = 0) :
    ((1 : ℕ) : ℕ∞) ≤ f.order := by
  refine nat_le_order fun d hd => ?_
  have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).1 (by omega)
  subst hd0
  simpa using hf
private theorem natCast_le_order_pow_of_constantCoeff_eq_zero {f : MvPowerSeries τ R} (hf : constantCoeff f = 0) (m : ℕ) :
    (m : ℕ∞) ≤ (f ^ m).order := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ]
    exact natCast_add_le_order_mul ih (one_le_order_of_constantCoeff_eq_zero hf)
end Order
end PowerSeriesAgreement
end
end ReciprocityTheory.ChartRestriction.G.Sh
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries
noncomputable section
variable {R : Type*} [CommRing R] {τ : Type*} {ι : Type*}
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution {σ : Type*} {A A' : σ → MvPowerSeries τ R} {j : ℕ}
    (hA : ∀ s, constantCoeff (A s) = 0) (hA' : ∀ s, constantCoeff (A' s) = 0)
    (hAA : ∀ s, ((j + 1 : ℕ) : ℕ∞) ≤ (A s - A' s).order) (α : σ →₀ ℕ) (S : Finset σ) :
    ((j + ∑ s ∈ S, α s : ℕ) : ℕ∞) ≤
      (∏ s ∈ S, A s ^ α s - ∏ s ∈ S, A' s ^ α s).order := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [MvPowerSeries.order_zero]
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.prod_insert ha]
    have key : A a ^ α a * ∏ s ∈ S, A s ^ α s - A' a ^ α a * ∏ s ∈ S, A' s ^ α s =
        (A a ^ α a - A' a ^ α a) * ∏ s ∈ S, A s ^ α s +
          A' a ^ α a * (∏ s ∈ S, A s ^ α s - ∏ s ∈ S, A' s ^ α s) := by ring
    rw [key]
    refine natCast_le_order_add ?_ ?_
    · exact natCast_le_order_of_le (by omega)
        (natCast_add_le_order_mul (pt_order_pow_sub (hAA a) (hA a) (hA' a) (α a))
          (pt_order_prod_pow A hA α S))
    · exact natCast_le_order_of_le (by omega) (natCast_add_le_order_mul (natCast_le_order_pow_of_constantCoeff_eq_zero (hA' a) (α a)) ih)
end ReciprocityTheory.ChartRestriction.G.Sh
