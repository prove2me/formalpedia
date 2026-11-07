-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurent_support_max_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:31:57.521208+00:00
-- url     : https://prove2.me/submissions/5414d6a8-93c0-44cf-bcae-5d47c1cd31dd

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewUnits
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurent_coeff_mul_at_support_max_ne_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Multiplicative SkewMonoidAlgebra
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    {f g : CartwrightStegerSkewLaurentRing P r}
    {a b : ℤ}
    (ha : Multiplicative.ofAdd a ∈ f.support)
    (hmaxa : ∀ x, Multiplicative.ofAdd x ∈ f.support → x ≤ a)
    (hb : Multiplicative.ofAdd b ∈ g.support)
    (hmaxb : ∀ x, Multiplicative.ofAdd x ∈ g.support → x ≤ b) :
    Multiplicative.ofAdd (a + b) ∈ (f * g).support ∧
      ∀ x, Multiplicative.ofAdd x ∈ (f * g).support → x ≤ a + b := by
  constructor
  · exact SkewMonoidAlgebra.mem_support_iff.mpr
      (skewLaurent_coeff_mul_at_support_max_ne_zero P r
        ha hmaxa hb hmaxb)
  · intro x hx
    have hx' := SkewMonoidAlgebra.support_mul f g hx
    rw [Finset.mem_mul] at hx'
    obtain ⟨u, hu, v, hv, huv⟩ := hx'
    have hueq : u = Multiplicative.ofAdd u.toAdd := rfl
    have hveq : v = Multiplicative.ofAdd v.toAdd := rfl
    have hule := hmaxa u.toAdd (hueq ▸ hu)
    have hvle := hmaxb v.toAdd (hveq ▸ hv)
    have hsum := congrArg Multiplicative.toAdd huv
    change u.toAdd + v.toAdd = x at hsum
    omega
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
