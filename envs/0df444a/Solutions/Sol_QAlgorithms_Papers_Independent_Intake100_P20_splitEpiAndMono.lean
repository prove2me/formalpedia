-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P20.splitEpiAndMono
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-02T12:17:29.859545+00:00
-- url     : https://prove2.me/submissions/33863ab0-bf63-480f-b059-36588c3cfc1e

import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory
universe u v

theorem solution {C : Type u} [Category.{v} C] {A O : C}
    (s : A ⟶ O) (e : O ⟶ A) (h : e ≫ s = 𝟙 O) :
    Epi s ∧ Mono e := by
  constructor
  · constructor
    intro B a b hab
    have he := congrArg (fun k => e ≫ k) hab
    simpa only [← Category.assoc, h, Category.id_comp] using he
  · constructor
    intro B a b hab
    have hs := congrArg (fun k => k ≫ s) hab
    simpa only [Category.assoc, h, Category.comp_id] using hs

#print axioms solution
