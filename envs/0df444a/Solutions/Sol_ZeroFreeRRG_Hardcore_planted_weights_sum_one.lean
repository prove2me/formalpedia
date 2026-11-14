-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.planted_weights_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:19:58.485235+00:00
-- url     : https://prove2.me/submissions/30cd5bcf-6b2c-48a9-9963-f3b932159729

import Theorems.Thm_ZeroFreeRRG_Hardcore_normalized_partition_positive
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (hm : m.Valid) (t : ℝ) (ht : m.PosParam t) (d n : ℕ)
    [Nonempty (Matching n d)] :
    (∑ M : Matching n d, ∑ σ : Fin n → m.Spin, planted m t M σ) = 1 := by
  classical
  have hc : (Fintype.card (Matching n d) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hz (M : Matching n d) : 0 < normZ m t M := normalized_partition_positive m hm t ht d n M
  have hsum : 0 < ∑ M : Matching n d, normZ m t M := by
    apply Finset.sum_pos'
    · intro M hM
      exact (hz M).le
    · exact ⟨Classical.choice ‹Nonempty (Matching n d)›,Finset.mem_univ _,hz _⟩
  simp only [planted, ← Finset.sum_div]
  change (∑ M : Matching n d, normZ m t M) / ((Fintype.card (Matching n d) : ℝ) * an m d n t) = 1
  unfold an cmE
  field_simp
