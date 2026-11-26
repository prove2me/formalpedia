-- Prove2me | solution 1 for QuadraticFloor.psi_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:55:21.600478+00:00
-- url     : https://prove2.me/submissions/a8f6579a-9c1a-4dfb-b8c4-5856d63fd1fa

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass

set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
namespace QuadraticFloor
theorem _root_.solution {A : ℕ} (ψ : DirichletCharacter ℂ A) : ψ (-1) = 1 ∨ ψ (-1) = -1 :=
  ψ.even_or_odd
end QuadraticFloor
