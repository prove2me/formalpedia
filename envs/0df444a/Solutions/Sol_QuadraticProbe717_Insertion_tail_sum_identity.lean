-- Prove2me | solution 1 for QuadraticProbe717.Insertion.tail_sum_identity
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T22:33:40.376522+00:00
-- url     : https://prove2.me/submissions/a64d39fd-5baa-4083-bb0a-cdad630fb755

import Definitions.Def_QuadraticProbe717_Insertion_laws
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
open QuadraticProbe717.Insertion

private lemma mem_probeOffsets (n : ℕ) [NeZero n] (π : Equiv.Perm (ZMod n)) (x : ZMod n) :
    x ∈ probeOffsets n π := by
  unfold probeOffsets
  simp only [List.mem_append]
  by_cases hx : x ∈ (List.range n).map (fun i => (i : ZMod n) ^ 2)
  · exact Or.inl hx
  · right
    rw [List.mem_filter]
    refine ⟨?_, by simpa using hx⟩
    rw [List.mem_ofFn]
    exact ⟨⟨(π.symm x).val, ZMod.val_lt _⟩, by simp⟩

/-- The probe list has `n` square offsets plus at most `n` further ones. -/
private lemma length_probeList (n : ℕ) [NeZero n] (π : Equiv.Perm (ZMod n)) (h : ZMod n) :
    (probeList n π h).length ≤ 2 * n := by
  unfold probeList probeOffsets
  simp only [List.length_map, List.length_append, List.length_range]
  rw [show 2 * n = n + n by ring]
  apply Nat.add_le_add
  · simp
  · exact (List.length_filter_le _ _).trans (by simp)

/-- An insertion never costs more than `2n` probes. -/
private lemma insertionCost_le (n : ℕ) [NeZero n] (π : Equiv.Perm (ZMod n))
    (A : Finset (ZMod n)) (h : ZMod n) : insertionCost n π A h ≤ 2 * n := by
  unfold insertionCost
  split_ifs with hA
  · exact le_rfl
  · obtain ⟨x, hx⟩ : ∃ x, x ∉ A := by
      by_contra hc
      push_neg at hc
      exact hA (Finset.eq_univ_iff_forall.mpr hc)
    have hmem : x ∈ probeList n π h := by
      unfold probeList
      rw [List.mem_map]
      exact ⟨x - h, mem_probeOffsets n π _, by ring⟩
    have hlt := List.findIdx_lt_length_of_exists (p := fun x => decide (x ∉ A))
      ⟨x, hmem, by simpa using hx⟩
    have := length_probeList n π h
    omega

theorem solution (n m : ℕ) [NeZero n] (π : Equiv.Perm (ZMod n)) :
    expectedCost n m π = ∑ k ∈ Finset.range (2 * n), fixedTail n m π k := by
  unfold expectedCost fixedTail
  rw [← Finset.sum_div, ← Finset.sum_div]
  congr 1
  -- each cost is the number of thresholds `k < 2n` it exceeds
  have hT : ∀ hs : Fin (m + 1) → ZMod n, (fixedTime n m π hs : ℝ)
      = ∑ k ∈ Finset.range (2 * n), if k < fixedTime n m π hs then (1 : ℝ) else 0 := by
    intro hs
    have hle : fixedTime n m π hs ≤ 2 * n := insertionCost_le n π _ _
    rw [← Finset.natCast_card_filter]
    congr 1
    have : (Finset.range (2 * n)).filter (fun k => k < fixedTime n m π hs)
        = Finset.range (fixedTime n m π hs) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [this, Finset.card_range]
  simp_rw [hT]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.natCast_card_filter]
