-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.planted_graph_conditional_gibbs
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:19:58.388194+00:00
-- url     : https://prove2.me/submissions/d5e3f06b-5e3f-4899-ab3b-50a306f3994c

import Theorems.Thm_ZeroFreeRRG_Hardcore_normalized_partition_positive
import Mathlib
set_option autoImplicit false
open Set Filter MeasureTheory AFIsingKS ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution (m : Model) (hm : m.Valid) (t : ℝ) (ht : m.PosParam t)
    (d n : ℕ) (M : Matching n d) (σ : Fin n → m.Spin) :
    planted m t M σ = (∑ τ : Fin n → m.Spin, planted m t M τ) * gibbs m t M σ := by
  classical
  have hZ : normZ m t M ≠ 0 := ne_of_gt (normalized_partition_positive m hm t ht d n M)
  have hsum : (∑ τ : Fin n → m.Spin, planted m t M τ) =
      normZ m t M / ((Fintype.card (Matching n d) : ℝ) * an m d n t) := by
    simp only [planted, ← Finset.sum_div]
    rfl
  rw [hsum]
  unfold planted gibbs
  field_simp [hZ]
