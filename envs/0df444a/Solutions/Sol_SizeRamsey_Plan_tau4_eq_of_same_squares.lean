-- Prove2me | solution 1 for SizeRamsey.Plan.tau4_eq_of_same_squares
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:25:25.168414+00:00
-- url     : https://prove2.me/submissions/7b15f6aa-86da-486c-8295-771eac081c2b

module
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_Deletion
public import Theorems.Thm_SizeRamsey_Plan_tau4_le_of_restrict

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} {W : Type*}
namespace SizeRamsey.Plan
theorem _root_.solution [Fintype V] {G H : SimpleGraph V}
    (h : ∀ f, IsC4Map G f ↔ IsC4Map H f) : tau4 G = tau4 H :=
  le_antisymm (tau4_le_of_restrict id Function.injective_id fun f hf => (h f).mp hf)
    (tau4_le_of_restrict id Function.injective_id fun f hf => (h f).mpr hf)
end SizeRamsey.Plan
