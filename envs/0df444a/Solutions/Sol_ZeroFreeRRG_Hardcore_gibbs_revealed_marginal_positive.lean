-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.gibbs_revealed_marginal_positive
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:12:40.907133+00:00
-- url     : https://prove2.me/submissions/4d8e5121-c5e7-473b-a2bd-efa7acb6c8d4

import Definitions.Def_ZeroFreeRRG_Hardcore_Moments
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (t : ℝ) (d n : ℕ) (M : Matching n d)
    (σ : Fin n → m.Spin) (U : Finset (Fin n))
    (hnonneg : ∀ σ', 0 ≤ gibbs m t M σ') (hσ : 0 < gibbs m t M σ) :
    0 < gibbsMarg m t M σ U := by
  classical
  unfold gibbsMarg
  apply Finset.sum_pos'
  · intro σ' hσ'
    exact hnonneg σ'
  · refine ⟨σ,?_,hσ⟩
    simp
