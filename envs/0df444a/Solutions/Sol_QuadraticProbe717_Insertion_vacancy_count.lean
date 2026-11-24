-- Prove2me | solution 1 for QuadraticProbe717.Insertion.vacancy_count
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T22:32:03.054646+00:00
-- url     : https://prove2.me/submissions/7a463389-df3c-4eae-96d0-ece4a0041035

import Definitions.Def_QuadraticProbe717_Insertion_laws
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
open QuadraticProbe717.Insertion

/-- Every residue occurs among the probe offsets: squares first, then the rest in `π`-order. -/
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
    refine ⟨⟨(π.symm x).val, ZMod.val_lt _⟩, ?_⟩
    simp

private lemma mem_probeList (n : ℕ) [NeZero n] (π : Equiv.Perm (ZMod n)) (h x : ZMod n) :
    x ∈ probeList n π h := by
  unfold probeList
  rw [List.mem_map]
  exact ⟨x - h, mem_probeOffsets n π _, by ring⟩

/-- One insertion along a list that visits every residue adds exactly one slot unless full. -/
private lemma card_insertAlong (n : ℕ) [NeZero n] (A : Finset (ZMod n)) (L : List (ZMod n))
    (hL : ∀ x, x ∈ L) : (insertAlong A L).card = min (A.card + 1) n := by
  have hcard : Fintype.card (ZMod n) = n := ZMod.card n
  have hle : A.card ≤ n := by
    have := Finset.card_le_univ A
    rwa [hcard] at this
  unfold insertAlong
  rcases hf : L.find? (fun x => decide (x ∉ A)) with _ | x
  · -- nothing outside A: A is everything
    have hall : ∀ x, x ∈ A := by
      intro x
      have := List.find?_eq_none.mp hf x (hL x)
      simpa using this
    have hA : A = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
    subst hA
    simp [Finset.card_univ, hcard]
  · have hx : x ∉ A := by simpa using List.find?_some hf
    dsimp only
    rw [Finset.card_insert_of_notMem hx]
    have : A.card < n := by
      have := Finset.card_lt_univ_of_notMem hx
      rwa [hcard] at this
    omega

private lemma card_foldl (n : ℕ) [NeZero n] (π : Equiv.Perm (ZMod n)) (hashes : List (ZMod n))
    (A : Finset (ZMod n)) (hA : A.card ≤ n) :
    (hashes.foldl (fun A h => insertAlong A (probeList n π h)) A).card
      = min (A.card + hashes.length) n := by
  induction hashes generalizing A with
  | nil => simp [Nat.min_eq_left hA]
  | cons h t ih =>
    simp only [List.foldl_cons, List.length_cons]
    have h1 := card_insertAlong n A (probeList n π h) (mem_probeList n π h)
    rw [ih _ (by omega), h1]
    omega

theorem solution (n : ℕ) [NeZero n] (π : Equiv.Perm (ZMod n))
    (hashes : List (ZMod n)) :
    vacantCount n (occupied n π hashes) = n - hashes.length := by
  unfold vacantCount occupied
  rw [card_foldl n π hashes ∅ (by simp)]
  simp only [Finset.card_empty, zero_add]
  omega
