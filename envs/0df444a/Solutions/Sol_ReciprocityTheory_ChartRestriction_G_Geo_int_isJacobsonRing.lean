-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.int_isJacobsonRing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:35.539501+00:00
-- url     : https://prove2.me/submissions/2afa1c31-f4f5-48aa-8bd7-79ea95bdbf04

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open Ideal
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases hb : P = ⊥
  · subst hb
    refine le_antisymm (fun x hx => ?_) bot_le
    rw [Ideal.mem_jacobson_bot] at hx
    have h1 := Int.isUnit_iff.mp (by simpa using hx 1)
    have h2 := Int.isUnit_iff.mp (hx 2)
    rw [Ideal.mem_bot]
    omega
  · haveI : P.IsMaximal := hP.isMaximal hb
    exact Ideal.jacobson_eq_self_of_isMaximal
end ReciprocityTheory.ChartRestriction.G.Geo
