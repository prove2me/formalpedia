-- Prove2me | solution 1 for SemigroupBetti.sharesVar_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:13.045328+00:00
-- url     : https://prove2.me/submissions/246c3622-0ac3-4f5c-a147-5e91ec0e206a

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
public import Theorems.Thm_SemigroupBetti_SharesVar_symm

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
namespace SemigroupBetti
theorem _root_.solution {z z' : Fin 4 → ℕ} : SharesVar z z' ↔ SharesVar z' z :=
  ⟨SharesVar.symm, SharesVar.symm⟩
end SemigroupBetti
