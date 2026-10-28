-- Prove2me | solution 1 for WalledBrauer.Blocks.lemma_8_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T01:49:16.234772+00:00
-- url     : https://prove2.me/submissions/8cc60859-0a25-4932-9a6c-66bb3a2f9fa2

import Mathlib
import Definitions.Def_WalledBrauer_Blocks_Partitions

namespace Aux_WB_81

open WalledBrauer.Blocks

lemma card_fiber (X : Finset (ℕ × ℕ)) (P : ℕ × ℕ → Prop) [DecidablePred P] :
    Fintype.card {d : X // P d.1} = (X.filter P).card := by
  rw [← Fintype.card_coe (X.filter P)]
  refine Fintype.card_congr
    { toFun := fun d => ⟨d.1.1, Finset.mem_filter.mpr ⟨d.1.2, d.2⟩⟩
      invFun := fun e => ⟨⟨e.1, (Finset.mem_filter.mp e.2).1⟩, (Finset.mem_filter.mp e.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

lemma pairs_iff (δ : ℤ) (X Y : Finset (ℕ × ℕ)) :
    PairsToNegDelta δ X Y ↔
      ∀ i, (X.filter fun d => content d = i).card = (Y.filter fun d => content d = -δ - i).card := by
  constructor
  · rintro ⟨f, hf⟩ i
    have hf' : ∀ d : X, content d.1 + content (f d).1 = -δ := fun d => by
      have := hf d; simpa using this
    refine Finset.card_bij' (fun a ha => (f ⟨a, (Finset.mem_filter.mp ha).1⟩).1)
      (fun b hb => (f.symm ⟨b, (Finset.mem_filter.mp hb).1⟩).1) ?_ ?_ ?_ ?_
    · intro a ha
      have h1 := (Finset.mem_filter.mp ha).2
      have h2 := hf' ⟨a, (Finset.mem_filter.mp ha).1⟩
      refine Finset.mem_filter.mpr ⟨(f _).2, ?_⟩
      simp only at h2
      omega
    · intro b hb
      have h1 := (Finset.mem_filter.mp hb).2
      have h2 := hf' (f.symm ⟨b, (Finset.mem_filter.mp hb).1⟩)
      rw [Equiv.apply_symm_apply] at h2
      refine Finset.mem_filter.mpr ⟨(f.symm _).2, ?_⟩
      simp only at h2
      omega
    · intro a ha; simp
    · intro b hb; simp
  · intro h
    have e : ∀ c : ℤ, {d : X // content d.1 = c} ≃ {e : Y // -δ - content e.1 = c} := by
      intro c
      refine Fintype.equivOfCardEq ?_
      rw [card_fiber X (fun d => content d = c), card_fiber Y (fun d => -δ - content d = c), h c]
      congr 1
      ext d; simp only [Finset.mem_filter]; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
    refine ⟨Equiv.ofFiberEquiv e, fun d => ?_⟩
    have := Equiv.ofFiberEquiv_map e d
    simp only [Int.cast_id]
    omega

lemma diag (lam mu : YoungDiagram) (i : ℤ) :
    (lam.cells.filter fun d => content d = i) ⊆ (mu.cells.filter fun d => content d = i) ∨
      (mu.cells.filter fun d => content d = i) ⊆ (lam.cells.filter fun d => content d = i) := by
  by_contra h
  push_neg at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨p, hp1, hp2⟩ := Finset.not_subset.mp h1
  obtain ⟨q, hq1, hq2⟩ := Finset.not_subset.mp h2
  simp only [Finset.mem_filter] at hp1 hp2 hq1 hq2
  unfold content at hp1 hq1
  rcases le_total p.1 q.1 with h | h
  · have hs : p.2 ≤ q.2 := by omega
    have : p ∈ mu.cells := by
      have := mu.up_left_mem h hs (show (q.1, q.2) ∈ mu from hq1.1)
      exact this
    exact hp2 ⟨this, hp1.2⟩
  · have hs : q.2 ≤ p.2 := by omega
    have : q ∈ lam.cells := by
      have := lam.up_left_mem h hs (show (p.1, p.2) ∈ lam from hp1.1)
      exact this
    exact hq2 ⟨this, hq1.2⟩

lemma diffs (lam mu : YoungDiagram) (i : ℤ) :
    (((lam.cells \ mu.cells).filter fun d => content d = i).card : ℤ) -
        ((mu.cells \ lam.cells).filter fun d => content d = i).card =
      (contentCount lam i : ℤ) - contentCount mu i ∧
    (((lam.cells \ mu.cells).filter fun d => content d = i).card = 0 ∨
      ((mu.cells \ lam.cells).filter fun d => content d = i).card = 0) := by
  set A := lam.cells.filter fun d => content d = i
  set B := mu.cells.filter fun d => content d = i
  have e1 : ((lam.cells \ mu.cells).filter fun d => content d = i) = A \ B := by
    ext d; simp [A, B]; tauto
  have e2 : ((mu.cells \ lam.cells).filter fun d => content d = i) = B \ A := by
    ext d; simp [A, B]; tauto
  rw [e1, e2]
  refine ⟨?_, ?_⟩
  · have h1 := Finset.card_sdiff_add_card_inter A B
    have h2 := Finset.card_sdiff_add_card_inter B A
    rw [Finset.inter_comm] at h2
    have hA : contentCount lam i = A.card := rfl
    have hB : contentCount mu i = B.card := rfl
    rw [hA, hB]
    omega
  · rcases diag lam mu i with h | h
    · left; rw [Finset.sdiff_eq_empty_iff_subset.mpr h]; rfl
    · right; rw [Finset.sdiff_eq_empty_iff_subset.mpr h]; rfl

end Aux_WB_81

open WalledBrauer.Blocks Aux_WB_81 in
theorem solution (δ : ℤ) (lamL lamR muL muR : YoungDiagram) :
    IsBalanced δ lamL lamR muL muR ↔
      ∀ i : ℤ, (contentCount lamL i : ℤ) - contentCount muL i =
        (contentCount lamR (-δ - i) : ℤ) - contentCount muR (-δ - i) := by
  unfold IsBalanced
  rw [pairs_iff, pairs_iff]
  constructor
  · rintro ⟨h1, h2⟩ i
    rw [← (diffs lamL muL i).1, ← (diffs lamR muR (-δ - i)).1, h1 i, h2 i]
  · intro h
    have key : ∀ i, ((lamL.cells \ muL.cells).filter fun d => content d = i).card =
          ((lamR.cells \ muR.cells).filter fun d => content d = -δ - i).card ∧
        ((muL.cells \ lamL.cells).filter fun d => content d = i).card =
          ((muR.cells \ lamR.cells).filter fun d => content d = -δ - i).card := by
      intro i
      have hi := h i
      obtain ⟨d1, z1⟩ := diffs lamL muL i
      obtain ⟨d2, z2⟩ := diffs lamR muR (-δ - i)
      rw [← d1, ← d2] at hi
      omega
    exact ⟨fun i => (key i).1, fun i => (key i).2⟩
