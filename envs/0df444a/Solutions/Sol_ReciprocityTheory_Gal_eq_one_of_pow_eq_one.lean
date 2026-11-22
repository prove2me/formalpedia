-- Prove2me | solution 1 for ReciprocityTheory.Gal.eq_one_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:29:51.18843+00:00
-- url     : https://prove2.me/submissions/31dec47a-b67a-4276-8c3b-4e097126c940

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open ReciprocityTheory ReciprocityTheory.Gal
variable {Ω : Type*} [Field Ω]
namespace ReciprocityTheory.Gal
theorem _root_.solution (A : ValuationSubring Ω) {N : ℕ} (hN : ¬ A.valuation (N : Ω) < 1)
    {ξ : Ω} (hξ : ξ ^ N = 1) (h : A.valuation (ξ - 1) < 1) : ξ = 1 := by
  have hξ1 : A.valuation ξ ≤ 1 := by
    have h2 := Valuation.map_add A.valuation (ξ - 1) 1
    rw [sub_add_cancel, Valuation.map_one] at h2
    exact h2.trans (max_le h.le le_rfl)
  have hpow : ∀ j : ℕ, A.valuation (ξ ^ j) ≤ 1 := fun j => by
    rw [Valuation.map_pow]
    exact pow_le_one' hξ1 j
  have hgeom : ∀ i : ℕ, A.valuation (ξ ^ i - 1) < 1 := by
    intro i
    rw [← geom_sum_mul, Valuation.map_mul]
    refine lt_of_le_of_lt (mul_le_of_le_one_left' ?_) h
    exact Valuation.map_sum_le _ (fun j _ => hpow j)
  by_contra hne
  have h3 := geom_sum_mul ξ N
  rw [hξ, sub_self] at h3
  have hS := (mul_eq_zero.1 h3).resolve_right (fun h4 => hne (sub_eq_zero.1 h4))
  have h5 := Valuation.map_sum_lt A.valuation (s := Finset.range N) (f := fun i => ξ ^ i - 1)
    one_ne_zero (fun i _ => hgeom i)
  rw [Finset.sum_sub_distrib, hS] at h5
  apply hN
  simpa using h5
end ReciprocityTheory.Gal
