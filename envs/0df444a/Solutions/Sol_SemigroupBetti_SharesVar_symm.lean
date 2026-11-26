-- Prove2me | solution 1 for SemigroupBetti.SharesVar.symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:25:43.730577+00:00
-- url     : https://prove2.me/submissions/a9fd041b-19ed-4d9b-bd56-cdcab7785959

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
namespace SemigroupBetti
namespace SharesVar
theorem _root_.solution {z z' : Fin 4 → ℕ} (h : SharesVar z z') : SharesVar z' z := by
  obtain ⟨i, h1, h2⟩ := h; exact ⟨i, h2, h1⟩
end SharesVar
end SemigroupBetti
