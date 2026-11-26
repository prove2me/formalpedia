-- Prove2me | solution 1 for SemigroupBetti.reachable_induction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:09:24.029248+00:00
-- url     : https://prove2.me/submissions/e5b3f591-4516-4eef-b24b-9f7d3eb1f41c

module
public import Definitions.Def_SemigroupBetti_Critical
public import Definitions.Def_SemigroupBetti_Partition

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
namespace SemigroupBetti
theorem _root_.solution {V : Type*} {Γ : SimpleGraph V} (P : V → Prop)
    (hstep : ∀ x y, P x → Γ.Adj x y → P y) {x y : V} (h : Γ.Reachable x y) (hx : P x) : P y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hx
  | cons ha _ ih => exact ih (hstep _ _ hx ha)
end SemigroupBetti
