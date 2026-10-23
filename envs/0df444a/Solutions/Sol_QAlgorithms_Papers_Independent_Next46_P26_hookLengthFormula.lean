-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P26.hookLengthFormula
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T15:04:56.449416+00:00
-- url     : https://prove2.me/submissions/87715885-d28f-4737-9f1f-e64b6551d0dd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P26_hookBranching
import Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P26_tableauBranching

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace X6N26H

open QAlgorithms.Papers.Independent.Next46.P26

theorem pred_card (lam mu : YoungDiagram) (h : mu ∈ oneBoxPredecessors lam) :
    mu.card + 1 = lam.card := by
  unfold oneBoxPredecessors at h
  rw [Finset.mem_image] at h
  obtain ⟨a, -, rfl⟩ := h
  exact (Finset.mem_filter.1 a.property).2.1

theorem empty_count (lam : YoungDiagram) (h : lam.card = 0) : tableauCount lam = 1 := by
  have hcells : lam.cells = ∅ := Finset.card_eq_zero.1 h
  unfold tableauCount
  rw [Fintype.card_eq_one_iff]
  have hfun : ∀ t : Fin lam.card → {z : ℕ × ℕ // z ∈ lam.cells}, t = fun i => (h ▸ i).elim0 := by
    intro t; funext i; exact (h ▸ i).elim0
  refine ⟨⟨fun i => (h ▸ i).elim0, ?_⟩, ?_⟩
  · refine ⟨fun i => (h ▸ i).elim0, ?_, fun i => (h ▸ i).elim0, fun i => (h ▸ i).elim0⟩
    rw [hcells]
    apply Finset.eq_empty_of_forall_notMem
    intro z hz
    obtain ⟨i, -, -⟩ := Finset.mem_image.1 hz
    exact (h ▸ i).elim0
  · intro t
    apply Subtype.ext
    exact hfun t.1

end X6N26H

open X6N26H QAlgorithms.Papers.Independent.Next46.P26 in
theorem solution (lam : YoungDiagram) :
    (tableauCount lam : ℚ) = (lam.card.factorial : ℚ) / hookProduct lam := by
  induction hN : lam.card using Nat.strong_induction_on generalizing lam with
  | _ N ih =>
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    have hcells : lam.cells = ∅ := Finset.card_eq_zero.1 hN
    rw [empty_count lam hN]
    simp [hookProduct, hcells]
  · have hne : lam.cells.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      have : lam.card = 0 := by simp [YoungDiagram.card, h]
      omega
    rw [tableauBranching lam hne, Nat.cast_sum, ← hN]
    rw [(hookBranching lam hne).1]
    refine Finset.sum_congr rfl fun mu hmu => ?_
    have hc := pred_card lam mu hmu
    rw [ih mu.card (by omega) mu rfl]
    rw [show lam.card - 1 = mu.card by omega]
