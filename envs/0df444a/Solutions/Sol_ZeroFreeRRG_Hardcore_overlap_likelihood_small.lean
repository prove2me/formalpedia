-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.overlap_likelihood_small
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:55:42.158093+00:00
-- url     : https://prove2.me/submissions/b7822306-ac42-4d65-9cb6-b8a8eb60e7d0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
import Theorems.Thm_ZeroFreeRRG_Hardcore_cavity_laws_compact
import Theorems.Thm_ZeroFreeRRG_Hardcore_cavity_bethe_continuous
import Theorems.Thm_ZeroFreeRRG_Hardcore_cavity_perturbation_continuous
import Theorems.Thm_ZeroFreeRRG_Hardcore_overlap_likelihood_model_reduction
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d) (t : ℝ) (ht : m.PosParam t)
    (hC1 : Condition1 m d t) :
    ∀ ε : ℝ, 0 < ε → ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∃ N : ℕ,
      ∀ n ≥ N, Even (n*d) →
        (1:ℝ)/n * plantedPinnedE m t s d n (fun M σ U => pinnedLL m t M σ U) ≤ ε*s := by
  exact overlap_likelihood_model_reduction m hm d hd t ht hC1
    (cavity_laws_compact m t) (cavity_bethe_continuous m t d)
    (cavity_perturbation_continuous m t d)
