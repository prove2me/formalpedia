-- Prove2me | solution 1 for TopkisRation.Myopic.ybar_N_finite
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T05:33:10.937058+00:00
-- url     : https://prove2.me/submissions/09f83797-1c8e-437e-b08c-4e814492a2cf

import Definitions.Def_TopkisRation_Myopic_MultiPeriod
import Theorems.Thm_TopkisRation_Myopic_order_up_to

open TopkisRation.Myopic

theorem solution {n : ℕ} (Q : MultiModel n) (hQ : Q.Standing)
    (hv : Q.v = Q.c (Q.N + 1)) (hN : 1 ≤ Q.N) :
    ∀ y : WithTop ℝ, IsMyopicLevel (Q.gmyopic Q.N) y → y ≠ ⊤ := by
  have hCN : ∀ y, Q.C (Q.N + 1) y = 0 := by
    intro y
    simp [MultiModel.C, MultiModel.Crev, hv]
  have hgN : ∀ z, Q.gtilde Q.N z = Q.gmyopic Q.N z := by
    intro z
    unfold MultiModel.gtilde MultiModel.gmyopic
    simp only [hCN, add_zero]
  obtain ⟨⟨x, hx0, hmin⟩, -⟩ := order_up_to Q hQ Q.N (Finset.mem_Icc.2 ⟨hN, le_rfl⟩)
  intro y hy
  rcases hy with ⟨-, hno⟩ | ⟨x', rfl, -⟩
  · exact absurd ⟨x, hx0, fun z hz => by rw [← hgN, ← hgN]; exact hmin z hz⟩ hno
  · exact WithTop.coe_ne_top
