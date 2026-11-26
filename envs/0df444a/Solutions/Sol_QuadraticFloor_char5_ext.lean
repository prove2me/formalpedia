-- Prove2me | solution 1 for QuadraticFloor.char5_ext
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:52.311419+00:00
-- url     : https://prove2.me/submissions/8a09cf61-bbca-4093-aa58-d384c4a6913d

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
public import Theorems.Thm_QuadraticFloor_zmod5_eq_pow_lg

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution {ψ ψ' : DirichletCharacter ℂ 5} (h : ψ 2 = ψ' 2) : ψ = ψ' := by
  refine MulChar.ext' fun a => ?_
  by_cases ha : a = 0
  · rw [ha, MulChar.map_nonunit _ not_isUnit_zero, MulChar.map_nonunit _ not_isUnit_zero]
  · rw [zmod5_eq_pow_lg a ha, map_pow, map_pow, h]
end QuadraticFloor
