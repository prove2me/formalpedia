-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.gibbs_weights_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:08:18.227987+00:00
-- url     : https://prove2.me/submissions/2493e18a-26d1-42f7-8616-d97cee86590c

import Theorems.Thm_ZeroFreeRRG_Hardcore_normalized_partition_positive
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (hm : m.Valid) (t : ℝ) (ht : m.PosParam t)
    (d n : ℕ) (M : Matching n d) :
    (∑ σ : Fin n → m.Spin, gibbs m t M σ) = 1 := by
  classical
  simp only [gibbs, ← Finset.sum_div]
  change normZ m t M / normZ m t M = 1
  exact div_self (ne_of_gt (normalized_partition_positive m hm t ht d n M))
