-- Prove2me | solution 1 for StrongPerfectGraph.Main.perfect_berge
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T06:15:15.348655+00:00
-- url     : https://prove2.me/submissions/d33c3916-78b9-4249-b399-7d576914a722

import Mathlib
import Theorems.Thm_StrongPerfectGraph_Main_complement_perfect
import Definitions.Def_StrongPerfectGraph_Main_IsBerge
import Definitions.Def_StrongPerfectGraph_Main_IsPerfect

open StrongPerfectGraph.Main

namespace SPGTPerfectBerge

lemma succ_mod_eq {i j n : ℕ} (hi : i < n) (hj : j < n) :
    (i + 1) % n = j ↔ (i + 1 = j ∨ (i + 1 = n ∧ j = 0)) := by
  rcases Nat.lt_or_ge (i + 1) n with h | h
  · rw [Nat.mod_eq_of_lt h]; omega
  · have : i + 1 = n := by omega
    rw [this, Nat.mod_self]; omega

/-- A perfect graph has no odd hole. -/
theorem hole_even {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : IsPerfect G)
    (c : List V) (hc : IsHole G c) : Even c.length := by
  classical
  obtain ⟨h4, hnd, hadj⟩ := hc
  set n := c.length with hn
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  set X : Set V := {v | v ∈ c} with hX
  have mem : ∀ i : Fin n, c.get i ∈ X := fun i => List.get_mem c i
  -- adjacency of two list positions, in arithmetic form
  have adjI : ∀ i j : Fin n, G.Adj (c.get i) (c.get j) ↔
      (i.val + 1 = j.val ∨ (i.val + 1 = n ∧ j.val = 0) ∨
        j.val + 1 = i.val ∨ (j.val + 1 = n ∧ i.val = 0)) := by
    intro i j
    rw [hadj i j, succ_mod_eq i.2 j.2, succ_mod_eq j.2 i.2]
    tauto
  -- every vertex of X is some list position
  have pos : ∀ x : X, ∃ i : Fin n, c.get i = x.1 := by
    intro x
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp x.2
    exact ⟨i, hi⟩
  -- clique number at most 2
  have hω : (G.induce X).cliqueNum ≤ 2 := by
    by_contra hlt
    push Not at hlt
    obtain ⟨s, hs⟩ := (G.induce X).exists_isNClique_cliqueNum
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (s := s) (n := 3)
      (by rw [hs.card_eq]; omega)
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp htc
    have hcl : (G.induce X).IsClique (({x, y, z} : Finset X) : Set X) :=
      hs.isClique.subset (by exact_mod_cast hts)
    have axy : G.Adj x.1 y.1 := by
      have := hcl (by simp) (by simp) hxy; simpa using this
    have axz : G.Adj x.1 z.1 := by
      have := hcl (by simp) (by simp) hxz; simpa using this
    have ayz : G.Adj y.1 z.1 := by
      have := hcl (by simp) (by simp) hyz; simpa using this
    obtain ⟨i, hi⟩ := pos x
    obtain ⟨j, hj⟩ := pos y
    obtain ⟨k, hk⟩ := pos z
    rw [← hi, ← hj] at axy
    rw [← hi, ← hk] at axz
    rw [← hj, ← hk] at ayz
    rw [adjI] at axy axz ayz
    have hij : i.val ≠ j.val := by
      intro h; apply hxy; apply Subtype.ext; rw [← hi, ← hj]; congr 1; exact Fin.ext h
    have hik : i.val ≠ k.val := by
      intro h; apply hxz; apply Subtype.ext; rw [← hi, ← hk]; congr 1; exact Fin.ext h
    have hjk : j.val ≠ k.val := by
      intro h; apply hyz; apply Subtype.ext; rw [← hj, ← hk]; congr 1; exact Fin.ext h
    have := i.2; have := j.2; have := k.2
    omega
  -- hence 2-colourable
  have hcol : (G.induce X).Colorable 2 := by
    rw [← SimpleGraph.chromaticNumber_le_iff_colorable, hG X]
    exact_mod_cast hω
  obtain ⟨C⟩ := hcol
  let f : ℕ → ℕ := fun i => if h : i < n then (C ⟨c.get ⟨i, h⟩, mem _⟩).val else 0
  have hf2 : ∀ i, f i < 2 := by
    intro i; simp only [f]; split_ifs
    · exact Fin.isLt _
    · omega
  have hstep : ∀ i, i + 1 < n → f i ≠ f (i + 1) := by
    intro i hi
    have hi' : i < n := by omega
    simp only [f, dif_pos hi, dif_pos hi']
    intro heq
    have hA : (G.induce X).Adj ⟨c.get ⟨i, hi'⟩, mem _⟩ ⟨c.get ⟨i + 1, hi⟩, mem _⟩ := by
      simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype]
      rw [adjI]; simp
    exact C.valid hA (Fin.ext heq)
  have hpar : ∀ i, i < n → (f i = f 0 ↔ Even i) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 := hstep i hi
      have h3 := hf2 i; have h4 := hf2 (i + 1); have h5 := hf2 0
      rw [Nat.even_add_one]
      constructor
      · intro h; intro he; exact h2 (by rw [h]; exact h1.mpr he)
      · intro hne
        have h6 : f i ≠ f 0 := fun h => hne (h1.mp h)
        omega
  have hlast : f (n - 1) = f 0 := (hpar (n - 1) (by omega)).mpr (by
    obtain ⟨k, hk⟩ := hodd; exact ⟨k, by omega⟩)
  have hn0 : 0 < n := by omega
  have hA : (G.induce X).Adj ⟨c.get ⟨n - 1, by omega⟩, mem _⟩ ⟨c.get ⟨0, hn0⟩, mem _⟩ := by
    simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype]
    rw [adjI]; simp; omega
  apply C.valid hA
  apply Fin.ext
  have := hlast
  simp only [f, dif_pos (show n - 1 < n by omega), dif_pos hn0] at this
  exact this

end SPGTPerfectBerge

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsPerfect G) : IsBerge G :=
  ⟨fun c hc => SPGTPerfectBerge.hole_even G hG c hc,
   fun c hc => SPGTPerfectBerge.hole_even Gᶜ (complement_perfect G hG) c hc⟩
