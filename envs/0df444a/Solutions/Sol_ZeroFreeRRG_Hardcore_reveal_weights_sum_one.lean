-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.reveal_weights_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:08:18.386116+00:00
-- url     : https://prove2.me/submissions/0dd3a435-dfda-4f52-9ac8-d12a7a8a3929

import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (n : ℕ) (s : ℝ) :
    (∑ U : Finset (Fin n), revealProb s U) = 1 := by
  classical
  have hh := Finset.prod_add (fun _ : Fin n => s) (fun _ : Fin n => 1-s) Finset.univ
  simpa [revealProb, Finset.powerset_univ, Finset.card_sdiff, Finset.prod_const] using hh.symm
