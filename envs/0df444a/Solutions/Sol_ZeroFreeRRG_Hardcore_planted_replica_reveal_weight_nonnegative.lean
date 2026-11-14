-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.planted_replica_reveal_weight_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:08:18.241233+00:00
-- url     : https://prove2.me/submissions/9c4f44f1-1bc7-480d-9228-4a249e5ee6c9

import Theorems.Thm_ZeroFreeRRG_Hardcore_model_pi_positive_simplex
import Theorems.Thm_ZeroFreeRRG_Hardcore_model_edge_nonnegative
import Theorems.Thm_ZeroFreeRRG_Hardcore_planted_reveal_nonnegative
import Theorems.Thm_ZeroFreeRRG_Hardcore_normalized_partition_positive
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (hm : m.Valid) (t s : ℝ) (ht : m.PosParam t)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (d n : ℕ) :
    ∀ (M : Matching n d) (σ σ' : Fin n → m.Spin) (U : Finset (Fin n)),
      0 ≤ planted m t M σ * gibbs m t M σ' * revealProb s U := by
  classical
  have hπ : ∀ a, 0 ≤ m.pi t a := fun a => ((model_pi_positive_simplex m hm t ht).1 a).le
  have hP := model_edge_nonnegative m hm t ht
  have hM : ∀ a b, 0 ≤ m.M t a b := fun a b => div_nonneg (hP a b) (mul_nonneg (hπ a) (hπ b))
  intro M σ σ' U
  have hw : 0 ≤ weight m t M σ' := by
    unfold weight
    exact mul_nonneg (Finset.prod_nonneg fun v hv => hπ (σ' v))
      (Finset.prod_nonneg fun x hx => hM (σ' x.1) (σ' (M.1 x).1))
  have hg : 0 ≤ gibbs m t M σ' := div_nonneg hw (normalized_partition_positive m hm t ht d n M).le
  have hp := planted_reveal_nonnegative m t s d n hπ hP hs hs1 M σ U
  nlinarith
