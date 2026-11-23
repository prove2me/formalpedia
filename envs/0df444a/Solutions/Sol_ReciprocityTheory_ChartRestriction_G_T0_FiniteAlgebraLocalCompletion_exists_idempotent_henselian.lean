-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.exists_idempotent_henselian
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:21.378588+00:00
-- url     : https://prove2.me/submissions/97913bed-b0fa-4a46-b98c-16d562b96b30

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPrecompleteFiniteModule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
open IsLocalRing Polynomial
namespace ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
theorem _root_.solution {S : Type*} [CommRing S] (J : Ideal S) [HenselianRing S J] (x : S) (N : ℕ)
    (hN : (x * x - x) ^ (N + 1) ∈ J) : ∃ e s : S, e * e = e ∧ e - x = s * (x * x - x) := by
  have hnil : (Ideal.Quotient.mk J x - Ideal.Quotient.mk J x ^ 2) ^ (N + 1) = 0 := by
    have : Ideal.Quotient.mk J x - Ideal.Quotient.mk J x ^ 2 = -(Ideal.Quotient.mk J (x * x - x)) := by
      simp only [map_sub, map_mul, pow_two, neg_sub]
    rw [this, neg_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 hN, mul_zero]
  have hid := isIdempotentElem_one_sub_one_sub_pow_pow _ (N + 1) hnil
  have hq : Ideal.Quotient.mk J (1 - (1 - x ^ (N + 1)) ^ (N + 1)) =
      1 - (1 - Ideal.Quotient.mk J x ^ (N + 1)) ^ (N + 1) := by simp
  have hid' : Ideal.Quotient.mk J (1 - (1 - x ^ (N + 1)) ^ (N + 1)) *
      Ideal.Quotient.mk J (1 - (1 - x ^ (N + 1)) ^ (N + 1)) =
      Ideal.Quotient.mk J (1 - (1 - x ^ (N + 1)) ^ (N + 1)) := by rw [hq]; exact hid.eq
  have hxW : IsIdempotentElem (Ideal.Quotient.mk (Ideal.span {x * x - x}) x) := by
    rw [IsIdempotentElem, ← map_mul, Ideal.Quotient.eq]
    exact Ideal.subset_span rfl
  have hqW : Ideal.Quotient.mk (Ideal.span {x * x - x}) (1 - (1 - x ^ (N + 1)) ^ (N + 1)) =
      Ideal.Quotient.mk (Ideal.span {x * x - x}) x := by
    simp only [map_sub, map_one, map_pow, hxW.pow_succ_eq, hxW.one_sub.pow_succ_eq, sub_sub_cancel]
  generalize 1 - (1 - x ^ (N + 1)) ^ (N + 1) = e0 at hid' hqW
  have h3 : e0 - x ∈ Ideal.span {x * x - x} := Ideal.Quotient.eq.1 hqW
  have h4 : e0 * e0 - e0 ∈ Ideal.span {x * x - x} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hqW, hxW.eq, sub_self]
  have h1 : (X ^ 2 - X : S[X]).eval e0 ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [eval_sub, eval_pow, eval_X, map_sub, map_pow, pow_two, hid', sub_self]
  have hd : (X ^ 2 - X : S[X]).derivative.eval e0 = 2 * e0 - 1 := by
    simp; ring
  have h2 : IsUnit (Ideal.Quotient.mk J ((X ^ 2 - X : S[X]).derivative.eval e0)) := by
    rw [hd]
    refine isUnit_iff_exists_inv.2 ⟨Ideal.Quotient.mk J (2 * e0 - 1), ?_⟩
    simp only [map_sub, map_mul, map_ofNat, map_one]
    linear_combination 4 * hid'
  have hmon : (X ^ 2 - X : S[X]).Monic :=
    monic_X_pow_sub (lt_of_le_of_lt degree_X_le (by norm_num))
  obtain ⟨e, he, hee⟩ := HenselianRing.is_henselian _ hmon e0 h1 h2
  have hee' : e * e = e := by
    have := he.eq_zero
    simp only [eval_sub, eval_pow, eval_X] at this
    linear_combination this
  have hu2 : (2 * e - 1) * (2 * e - 1) = 1 := by linear_combination 4 * hee'
  have hdu : IsUnit (e - e0 - (2 * e - 1)) := by
    have : e - e0 - (2 * e - 1) = (-(2 * e - 1)) * ((e - e0) * (-(2 * e - 1)) + 1) := by
      linear_combination (-(e - e0)) * hu2
    rw [this]
    exact (isUnit_iff_exists_inv.2 ⟨-(2 * e - 1), by linear_combination hu2⟩).mul
      (Ideal.mem_jacobson_bot.1 (HenselianRing.jac hee) _)
  have hdW : e - e0 ∈ Ideal.span {x * x - x} := by
    obtain ⟨v, hv⟩ := hdu.exists_left_inv
    have hdd : (e - e0) * (e - e0 - (2 * e - 1)) = e0 * e0 - e0 := by
      linear_combination (-1 : S) * hee'
    have : e - e0 = v * (e0 * e0 - e0) := by
      linear_combination (-(e - e0)) * hv + v * hdd
    rw [this]; exact Ideal.mul_mem_left _ _ h4
  have h5 : e - x ∈ Ideal.span {x * x - x} := by
    have : e - x = (e - e0) + (e0 - x) := by ring
    rw [this]; exact Ideal.add_mem _ hdW h3
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 h5
  exact ⟨e, s, hee', hs.symm⟩
end ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
