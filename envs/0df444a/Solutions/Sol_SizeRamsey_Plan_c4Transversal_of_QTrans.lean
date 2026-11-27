-- Prove2me | solution 1 for SizeRamsey.Plan.c4Transversal_of_QTrans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:26:29.021656+00:00
-- url     : https://prove2.me/submissions/879b8cfd-2edc-44b1-99ba-81aedf424c39

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
theorem _root_.solution {V : Type*} {G : SimpleGraph V} {S : Finset V}
    (h : QTrans G S) : c4Transversal G S := by
  rintro f ⟨hinj, h01, h12, h23, h30⟩
  rcases h _ _ _ _ h01 h12 h23 h30 (hinj.ne (by decide)) (hinj.ne (by decide)) with
    h | h | h | h
  exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩]
end SizeRamsey.Plan
