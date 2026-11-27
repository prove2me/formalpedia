-- Prove2me | solution 1 for SizeRamsey.Plan.k33_square_avoids_vertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:26:13.440242+00:00
-- url     : https://prove2.me/submissions/dc8e70c2-f430-4f02-9a50-9b4d906c675c

module
public import Definitions.Def_SizeRamsey_Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Definitions.Def_SizeRamsey_FiniteChecks

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
namespace SizeRamsey.Plan
theorem _root_.solution (v : Fin 6) :
    ∃ f : Fin 4 → Fin 6,
      IsC4Map k33MinusEdge f ∧ ∀ i, f i ≠ v := by
  fin_cases v
  · exact ⟨![1,3,2,4], by decide⟩
  · exact ⟨![0,4,2,5], by decide⟩
  · exact ⟨![0,4,1,5], by decide⟩
  · exact ⟨![0,4,1,5], by decide⟩
  · exact ⟨![1,3,2,5], by decide⟩
  · exact ⟨![1,3,2,4], by decide⟩
end SizeRamsey.Plan
