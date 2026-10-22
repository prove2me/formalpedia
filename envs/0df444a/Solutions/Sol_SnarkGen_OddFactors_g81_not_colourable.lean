-- Prove2me | solution 1 for SnarkGen.OddFactors.g81_not_colourable
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:25:36.129897+00:00
-- url     : https://prove2.me/submissions/d63188f9-2417-4c70-b844-0651f3e00fdb

import Mathlib
import Definitions.Def_SnarkGen_OddFactors_G81
import Definitions.Def_SnarkGen_EdgeInsertion_Colourable

set_option autoImplicit false
open SnarkGen.OddFactors

/-- the 39 edges of `G81`, in a search order -/
def ordE : List (Fin 26 × Fin 26) :=
  [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 6), (2, 7), (4, 6), (4, 8), (3, 8), (3, 9), (5, 7), (5, 9), (6, 10), (7, 11), (8, 12), (9, 13), (10, 14), (10, 15), (11, 14), (11, 16), (14, 17), (12, 17), (13, 17), (12, 18), (13, 19), (15, 20), (15, 21), (16, 20), (16, 22), (18, 22), (18, 23), (19, 21), (19, 23), (20, 24), (23, 24), (21, 25), (22, 25), (24, 25)]

/-- for each position `k`, the earlier positions whose edge shares an endpoint with edge `k` -/
def prevE : List (List ℕ) :=
  [[], [0], [0, 1], [0], [0, 3], [1], [1, 5], [3, 5], [3, 7], [2, 8], [2, 9], [4, 6], [4, 10, 11], [5, 7], [6, 11], [8, 9], [10, 12], [13], [13, 17], [14, 17], [14, 19], [17, 19], [15, 21], [16, 21, 22], [15, 22], [16, 23], [18], [18, 26], [20, 26], [20, 28], [24, 29], [24, 30], [25, 27], [25, 31, 32], [26, 28], [31, 33, 34], [27, 32], [29, 30, 36], [34, 35, 36, 37]]

def ordAt (k : ℕ) : Fin 26 × Fin 26 := ordE.getD k (0, 0)

def sharesB (p q : Fin 26 × Fin 26) : Bool :=
  decide (p.1 = q.1 ∨ p.1 = q.2 ∨ p.2 = q.1 ∨ p.2 = q.2)

/-- sound data: previous positions are earlier, adjacent in `G81`'s line graph and distinct edges -/
def dataOK : Bool :=
  (List.range 39).all fun k =>
    decide (G81.Adj (ordAt k).1 (ordAt k).2) &&
    (prevE.getD k []).all fun j =>
      decide (j < k) && sharesB (ordAt j) (ordAt k) &&
        decide (s((ordAt j).1, (ordAt j).2) ≠ s((ordAt k).1, (ordAt k).2))

theorem prevE_len : prevE.length = 39 := by decide +kernel

theorem dataOK_true : dataOK = true := by decide +kernel

def prevOK (k c : ℕ) (a : List ℕ) : Bool :=
  (prevE.getD k []).all fun j => a.getD j 0 != c

def dfs : ℕ → ℕ → List ℕ → Bool
  | 0, _, _ => false
  | fuel + 1, k, a => (List.range 3).all fun c => !(prevOK k c a) || dfs fuel (k + 1) (a ++ [c])

theorem dfs_true : dfs 37 2 [0, 1] = true := by decide +kernel

theorem dfs_false (f : ℕ → ℕ) (hlt : ∀ k j, j ∈ prevE.getD k [] → j < k)
    (hf : ∀ k j, j ∈ prevE.getD k [] → f j ≠ f k) (hf3 : ∀ k, f k < 3) :
    ∀ fuel k, dfs fuel k ((List.range k).map f) = false := by
  intro fuel
  induction fuel with
  | zero => intro k; rfl
  | succ fuel ih =>
    intro k
    simp only [dfs]
    rw [Bool.eq_false_iff]
    intro h
    have h1 := (List.all_eq_true.1 h) (f k) (List.mem_range.2 (hf3 k))
    have hprev : prevOK k (f k) ((List.range k).map f) = true := by
      unfold prevOK
      rw [List.all_eq_true]
      intro j hj
      have hjk := hlt k j hj
      have : ((List.range k).map f).getD j 0 = f j := by
        have hj' : j < ((List.range k).map f).length := by simp [hjk]
        rw [List.getD_eq_getElem _ _ hj']
        simp
      rw [this]
      simpa using hf k j hj
    rw [hprev] at h1
    have h2 : dfs fuel (k + 1) (((List.range k).map f) ++ [f k]) = true := by simpa using h1
    have h3 : ((List.range k).map f) ++ [f k] = (List.range (k + 1)).map f := by
      rw [List.range_succ, List.map_append]; rfl
    rw [h3] at h2
    rw [ih (k + 1)] at h2
    exact absurd h2 (by simp)

theorem solution : ¬ SnarkGen.EdgeInsertion.Colourable G81 := by
  rintro ⟨C⟩
  have hD := dataOK_true
  unfold dataOK at hD
  rw [List.all_eq_true] at hD
  have hD' : ∀ k, k < 39 → G81.Adj (ordAt k).1 (ordAt k).2 ∧
      ∀ j ∈ prevE.getD k [], j < k ∧ sharesB (ordAt j) (ordAt k) = true ∧
        s((ordAt j).1, (ordAt j).2) ≠ s((ordAt k).1, (ordAt k).2) := by
    intro k hk
    have := hD k (List.mem_range.2 hk)
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at this
    refine ⟨this.1, fun j hj => ?_⟩
    have := this.2 j hj
    exact ⟨this.1.1, this.1.2, this.2⟩
  -- the colouring as a function on positions
  let g : ℕ → Fin 3 := fun k =>
    if h : k < 39 then C ⟨s((ordAt k).1, (ordAt k).2), (hD' k h).1⟩ else 0
  have hlt : ∀ k j, j ∈ prevE.getD k [] → j < k := by
    intro k j hj
    by_cases hk : k < 39
    · exact ((hD' k hk).2 j hj).1
    · have : prevE.getD k [] = [] :=
        List.getD_eq_default _ _ (by rw [prevE_len]; omega)
      rw [this] at hj; simp at hj
  have hg : ∀ k j, j ∈ prevE.getD k [] → g j ≠ g k := by
    intro k j hj
    by_cases hk : k < 39
    · have hjk := hlt k j hj
      have hj39 : j < 39 := by omega
      obtain ⟨hlt', hsh, hne⟩ := (hD' k hk).2 j hj
      simp only [g, dif_pos hk, dif_pos hj39]
      intro heq
      have hadj : G81.lineGraph.Adj ⟨s((ordAt j).1, (ordAt j).2), (hD' j hj39).1⟩
          ⟨s((ordAt k).1, (ordAt k).2), (hD' k hk).1⟩ := by
        rw [SimpleGraph.lineGraph_adj_iff_exists]
        refine ⟨fun h => hne (congrArg Subtype.val h), ?_⟩
        simp only [sharesB, decide_eq_true_eq] at hsh
        rcases hsh with h | h | h | h
        · exact ⟨(ordAt j).1, by simp, by simp [h]⟩
        · exact ⟨(ordAt j).1, by simp, by simp [h]⟩
        · exact ⟨(ordAt j).2, by simp, by simp [h]⟩
        · exact ⟨(ordAt j).2, by simp, by simp [h]⟩
      exact C.valid hadj heq
    · have : prevE.getD k [] = [] :=
        List.getD_eq_default _ _ (by rw [prevE_len]; omega)
      rw [this] at hj; simp at hj
  have h01 : g 0 ≠ g 1 := hg 1 0 (by decide +kernel)
  have hperm : ∀ a b : Fin 3, a ≠ b → ∃ σ : Equiv.Perm (Fin 3), σ a = 0 ∧ σ b = 1 := by decide
  obtain ⟨σ, hσ0, hσ1⟩ := hperm (g 0) (g 1) h01
  let f : ℕ → ℕ := fun k => (σ (g k)).val
  have hf : ∀ k j, j ∈ prevE.getD k [] → f j ≠ f k := by
    intro k j hj heq
    exact hg k j hj (σ.injective (Fin.ext heq))
  have hf3 : ∀ k, f k < 3 := fun k => (σ (g k)).is_lt
  have hstart : (List.range 2).map f = [0, 1] := by
    simp [List.range_succ, f, hσ0, hσ1]
  have := dfs_false f hlt hf hf3 37 2
  rw [hstart, dfs_true] at this
  exact absurd this (by simp)
