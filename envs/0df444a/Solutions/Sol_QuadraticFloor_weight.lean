-- Prove2me | solution 1 for QuadraticFloor.weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:21.581532+00:00
-- url     : https://prove2.me/submissions/89c15ce9-1fd2-4453-aa69-26b6c7994ec7

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution (ψ : DirichletCharacter ℂ 5) (B : ℤ) :
    (starRingEnd ℂ (ψ (B : ZMod 5))) ^ 2 = starRingEnd ℂ (ψ ((B : ZMod 5) ^ 2)) := by
  rw [map_pow, map_pow]
end QuadraticFloor
