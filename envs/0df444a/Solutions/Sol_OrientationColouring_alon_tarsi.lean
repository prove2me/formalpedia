-- Prove2me | solution 1 for OrientationColouring.alon_tarsi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:32:54.148225+00:00
-- url     : https://prove2.me/submissions/08f187b6-c851-41a0-a7f5-e40df0dd35e6

module
public import Mathlib
public import Definitions.Def_AlonTarsiLib_AlonTarsi
public import Definitions.Def_AlonTarsiChoosability_Solution
public import Theorems.Thm_AlonTarsi_alon_tarsi


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open OrientationColouring
open AlonTarsi
variable {V : Type*} [Fintype V] [DecidableEq V]
open Classical
namespace OrientationColouring
theorem _root_.solution {Color : Type*} (G : SimpleGraph V) (D : V → V → Prop)
    (hD : IsOrientation G D) (hEO : eulerianCount D 0 ≠ eulerianCount D 1)
    (L : V → Finset Color) (hL : ∀ v, #{w | D v w} < (L v).card) :
    ∃ f : V → Color, (∀ v, f v ∈ L v) ∧ ∀ u v, G.Adj u v → f u ≠ f v :=
  AlonTarsi.alon_tarsi G D hD hEO L hL
end OrientationColouring
