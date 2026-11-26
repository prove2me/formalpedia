-- Prove2me | solution 1 for SemigroupBetti.mem_supp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:25:38.566502+00:00
-- url     : https://prove2.me/submissions/b8205474-7ea3-45f3-a8d6-8845190e6f47

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
namespace SemigroupBetti
theorem _root_.solution {z : Fin 4 → ℕ} {i : Fin 4} : i ∈ supp z ↔ 0 < z i := by
  simp [supp]
end SemigroupBetti
