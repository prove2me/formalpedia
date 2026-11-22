-- Prove2me | solution 1 for Pseudorandom.Adapted.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:59:17.100501+00:00
-- url     : https://prove2.me/submissions/6aac776a-e55c-441e-bbb7-5cca4e04e520

module
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Definitions.Def_GJKKL_Vendor_Freedman

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {α : Type*} [Fintype α] {n : ℕ}
omit [Fintype α]
namespace Pseudorandom
namespace Adapted
theorem _root_.solution {β : Type*} {k k' : ℕ} {F : (Fin n → α) → β} (h : Adapted k F)
    (hk : k ≤ k') : Adapted k' F :=
  fun ω ω' hω => h ω ω' fun i hi => hω i (lt_of_lt_of_le hi hk)
end Adapted
end Pseudorandom
