-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.pt_order_prod_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:30:51.503343+00:00
-- url     : https://prove2.me/submissions/bd4758d7-b551-4a24-a72b-fa8d64392c06

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
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
private theorem natCast_add_le_order_mul {f g : MvPowerSeries τ R} {a b : ℕ}
    (hf : (a : ℕ∞) ≤ f.order) (hg : (b : ℕ∞) ≤ g.order) : ((a + b : ℕ) : ℕ∞) ≤ (f * g).order :=
  le_trans (by rw [Nat.cast_add]; exact add_le_add hf hg) le_order_mul
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
theorem _root_.solution {σ : Type*} (A : σ → MvPowerSeries τ R)
    (hA : ∀ s, constantCoeff (A s) = 0) (α : σ →₀ ℕ) (S : Finset σ) :
    ((∑ s ∈ S, α s : ℕ) : ℕ∞) ≤ (∏ s ∈ S, A s ^ α s).order := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact natCast_add_le_order_mul (natCast_le_order_pow_of_constantCoeff_eq_zero (hA a) (α a)) ih
end ReciprocityTheory.ChartRestriction.G.Sh
