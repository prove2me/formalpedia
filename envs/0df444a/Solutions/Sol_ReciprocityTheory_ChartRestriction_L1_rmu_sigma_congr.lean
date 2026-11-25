-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.rmu_sigma_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:39:29.436472+00:00
-- url     : https://prove2.me/submissions/0f6aadfa-7ef6-4b63-8929-3943ed3e1880

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_MuMEvalPowEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM Polynomial
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (s : Rmu l →+* Rmu l)
    (hs : ∀ (ζ : ℂ_[l]) (hζ : ζ ∈ muP l),
      ((s ⟨ζ, Subring.subset_closure hζ⟩ : Rmu l) : ℂ_[l]) = ζ ^ l) (x : Rmu l) :
    ∃ r ∈ Rmu l, ((s x : Rmu l) : ℂ_[l]) - (x : ℂ_[l]) ^ l = (l : ℂ_[l]) * r := by
  have hl : l.Prime := Fact.out
  have key : ∀ (y : ℂ_[l]) (hy : y ∈ Rmu l), ∃ r : Rmu l, s ⟨y, hy⟩ - ⟨y, hy⟩ ^ l = (l : Rmu l) * r := by
    intro y hy
    induction hy using Subring.closure_induction with
    | mem ζ hζ => exact ⟨0, Subtype.ext (by simp [hs ζ hζ])⟩
    | zero =>
      refine ⟨0, ?_⟩
      have : (⟨0, zero_mem _⟩ : Rmu l) = 0 := rfl
      rw [this, map_zero, zero_pow hl.ne_zero]; simp
    | one =>
      refine ⟨0, ?_⟩
      have : (⟨1, one_mem _⟩ : Rmu l) = 1 := rfl
      rw [this, map_one, one_pow]; simp
    | add a b ha hb iha ihb =>
      obtain ⟨r, hr⟩ := iha
      obtain ⟨t, ht⟩ := ihb
      obtain ⟨u, hu⟩ := exists_add_pow_prime_eq hl (⟨a, ha⟩ : Rmu l) ⟨b, hb⟩
      refine ⟨r + t - ⟨a, ha⟩ * ⟨b, hb⟩ * u, ?_⟩
      have : (⟨a + b, add_mem ha hb⟩ : Rmu l) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
      rw [this, map_add, hu]
      linear_combination hr + ht
    | neg a ha iha =>
      obtain ⟨r, hr⟩ := iha
      have : (⟨-a, neg_mem ha⟩ : Rmu l) = -⟨a, ha⟩ := rfl
      rw [this, map_neg]
      rcases hl.eq_two_or_odd' with h2 | hodd
      · refine ⟨-r - ⟨a, ha⟩ ^ 2, ?_⟩
        subst h2
        push_cast at hr ⊢
        linear_combination -hr
      · refine ⟨-r, ?_⟩
        rw [hodd.neg_pow]
        linear_combination -hr
    | mul a b ha hb iha ihb =>
      obtain ⟨r, hr⟩ := iha
      obtain ⟨t, ht⟩ := ihb
      refine ⟨r * s ⟨b, hb⟩ + ⟨a, ha⟩ ^ l * t, ?_⟩
      have : (⟨a * b, mul_mem ha hb⟩ : Rmu l) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
      rw [this, map_mul, mul_pow]
      linear_combination s ⟨b, hb⟩ * hr + ⟨a, ha⟩ ^ l * ht
  obtain ⟨r, hr⟩ := key x.1 x.2
  refine ⟨r, r.2, ?_⟩
  have := congrArg (Subtype.val) hr
  simpa using this
end ReciprocityTheory.ChartRestriction.L1
