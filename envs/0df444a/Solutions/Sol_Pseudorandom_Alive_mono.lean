-- Prove2me | solution 1 for Pseudorandom.Alive.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:59:20.043634+00:00
-- url     : https://prove2.me/submissions/1cc9d45e-0c11-44e5-b784-1e6c7acf6ec4

module
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Definitions.Def_GJKKL_Vendor_Freedman

set_option autoImplicit true
@[expose] public section
public section
open Pseudorandom
open Finset
variable {α : Type*} [Fintype α] {n : ℕ}
variable {P : Fin n → α → ℝ} {X : ℕ → (Fin n → α) → ℝ} {G : ℕ → (Fin n → α) → Prop}
omit [Fintype α]
namespace Pseudorandom
namespace Alive
theorem _root_.solution {k k' : ℕ} {ω : Fin n → α} (h : Alive G k' ω) (hk : k ≤ k') :
    Alive G k ω := fun j hj => h j (hj.trans hk)
end Alive
end Pseudorandom
