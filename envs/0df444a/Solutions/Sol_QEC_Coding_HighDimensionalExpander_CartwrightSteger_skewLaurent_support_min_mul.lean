-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurent_support_min_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:31:58.537059+00:00
-- url     : https://prove2.me/submissions/be80031a-6898-43b8-a657-c0802ad21999

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewUnits
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurent_coeff_mul_at_support_min_ne_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Multiplicative SkewMonoidAlgebra
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    {f g : CartwrightStegerSkewLaurentRing P r}
    {a b : ℤ}
    (ha : Multiplicative.ofAdd a ∈ f.support)
    (hmina : ∀ x, Multiplicative.ofAdd x ∈ f.support → a ≤ x)
    (hb : Multiplicative.ofAdd b ∈ g.support)
    (hminb : ∀ x, Multiplicative.ofAdd x ∈ g.support → b ≤ x) :
    Multiplicative.ofAdd (a + b) ∈ (f * g).support ∧
      ∀ x, Multiplicative.ofAdd x ∈ (f * g).support → a + b ≤ x := by
  constructor
  · exact SkewMonoidAlgebra.mem_support_iff.mpr
      (skewLaurent_coeff_mul_at_support_min_ne_zero P r
        ha hmina hb hminb)
  · intro x hx
    have hx' := SkewMonoidAlgebra.support_mul f g hx
    rw [Finset.mem_mul] at hx'
    obtain ⟨u, hu, v, hv, huv⟩ := hx'
    have hueq : u = Multiplicative.ofAdd u.toAdd := rfl
    have hveq : v = Multiplicative.ofAdd v.toAdd := rfl
    have hule := hmina u.toAdd (hueq ▸ hu)
    have hvle := hminb v.toAdd (hveq ▸ hv)
    have hsum := congrArg Multiplicative.toAdd huv
    change u.toAdd + v.toAdd = x at hsum
    omega
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
