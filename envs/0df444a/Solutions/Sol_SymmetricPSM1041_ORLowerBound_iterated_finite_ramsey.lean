-- Prove2me | solution 1 for SymmetricPSM1041.ORLowerBound.iterated_finite_ramsey
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T14:32:22.915134+00:00
-- url     : https://prove2.me/submissions/c30f703f-dee9-40fb-9482-dcf36206d056

import Mathlib
import Theorems.Thm_AppliedComb_Ramsey_hypergraph_ramsey

open scoped BigOperators

private lemma ramseyOn (Color : Type*) [Fintype Color] [Nonempty Color]
    (s t : ℕ) (hs : 0 < s) (hst : s ≤ t) :
    ∃ R : ℕ, t ≤ R ∧ ∀ (X : Type*) [Fintype X],
      R ≤ Fintype.card X → (c : {S : Finset X // S.card = s} → Color) →
      ∃ H : Finset X, H.card = t ∧ ∃ a : Color,
        ∀ (S : Finset X) (hS : S.card = s), S ⊆ H → c ⟨S, hS⟩ = a := by
  classical
  let r := Fintype.card Color
  let targets : Fin r → ℕ := fun _ => t
  let R := AppliedComb.Ramsey.hypergraphRamseyNumber s r targets
  have hr : 0 < r := Fintype.card_pos
  have hleast := AppliedComb.Ramsey.hypergraph_ramsey r s hr hs targets (fun _ => hst)
  have hRpos : 0 < R := hleast.1.1
  refine ⟨max t R, le_max_left _ _, ?_⟩
  intro X _ hcard c
  let eX : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  let eC : Color ≃ Fin r := Fintype.equivFin Color
  let ϕ : {S : Finset (Fin (Fintype.card X)) // S.card = s} → Fin r :=
    fun S => eC (c ⟨S.1.map eX.symm.toEmbedding, by simpa using S.2⟩)
  obtain ⟨a, H, hHcard, hH⟩ := hleast.1.2 (Fintype.card X)
    (le_trans (le_max_right t R) hcard) ϕ
  let H' : Finset X := H.map eX.symm.toEmbedding
  refine ⟨H', by simpa [H'] using hHcard, eC.symm a, ?_⟩
  intro S hScard hSH
  let S' : Finset (Fin (Fintype.card X)) := S.map eX.toEmbedding
  have hS'card : S'.card = s := by simpa [S'] using hScard
  have hS'H : S' ⊆ H := by
    intro x hx
    obtain ⟨y, hyS, rfl⟩ := Finset.mem_map.1 hx
    have hyH' := hSH hyS
    obtain ⟨z, hzH, rfl⟩ := Finset.mem_map.1 hyH'
    simpa using hzH
  have hh := hH S' hS'card hS'H
  have hmap : S'.map eX.symm.toEmbedding = S := by
    ext x
    simp [S']
  have := congrArg eC.symm hh
  simpa [ϕ, hmap] using this

private lemma iteratedRamseyOn (Alphabet : Type*) [Fintype Alphabet] [Nonempty Alphabet]
    (m q : ℕ) (hm : 1 ≤ m) (hqm : q ≤ m) :
    ∃ N : ℕ, m ≤ N ∧ ∀ (X : Type*) [Fintype X], Fintype.card X ≥ N →
      ∀ c : (k : ℕ) → 1 ≤ k → k ≤ q →
        {S : Finset X // S.card = k} → (Fin k → Alphabet),
      ∃ H : Finset X, H.card = m ∧
        ∀ (k : ℕ) (hk : 1 ≤ k) (hkq : k ≤ q), ∃ word : Fin k → Alphabet,
          ∀ (S : Finset X) (hS : S.card = k), S ⊆ H →
            c k hk hkq ⟨S, hS⟩ = word := by
  classical
  induction q with
  | zero =>
      refine ⟨m, le_rfl, ?_⟩
      intro X _ hcard c
      obtain ⟨H, -, hHcard⟩ := Finset.exists_subset_card_eq
        (s := (Finset.univ : Finset X)) (n := m) (by simpa using hcard)
      refine ⟨H, hHcard, ?_⟩
      intro k hk hk0
      omega
  | succ q ih =>
      have hq : q ≤ m := by omega
      obtain ⟨N₀, hmN₀, hN₀⟩ := ih hq
      let Color := Fin (q + 1) → Alphabet
      obtain ⟨N, hN₀N, hN⟩ := ramseyOn Color (q + 1) N₀ (by omega)
        (le_trans (by omega) hmN₀)
      refine ⟨N, hmN₀.trans hN₀N, ?_⟩
      intro X _ hcard c
      obtain ⟨G, hGcard, wordTop, hGhom⟩ := hN X hcard
        (fun S => c (q + 1) (by omega) (by omega) S)
      let cG : (k : ℕ) → 1 ≤ k → k ≤ q →
          {S : Finset G // S.card = k} → (Fin k → Alphabet) :=
        fun k hk hkq S => c k hk (by omega)
          ⟨S.1.map (Function.Embedding.subtype _), by simpa using S.2⟩
      have hGlarge : Fintype.card G ≥ N₀ := by simpa [hGcard]
      obtain ⟨H, hHcard, hHhom⟩ := hN₀ G hGlarge cG
      let H' : Finset X := H.map (Function.Embedding.subtype _)
      refine ⟨H', by simpa [H'] using hHcard, ?_⟩
      intro k hk hksucc
      by_cases hkq : k ≤ q
      · obtain ⟨word, hword⟩ := hHhom k hk hkq
        refine ⟨word, ?_⟩
        intro S hScard hSH'
        have hH'G : H' ⊆ G := by
          intro x hx
          exact Finset.property_of_mem_map_subtype H hx
        have hSG : S ⊆ G := hSH'.trans hH'G
        let SG : Finset G := S.subtype (· ∈ G)
        have hSGmap : SG.map (Function.Embedding.subtype _) = S :=
          Finset.subtype_map_of_mem (fun x hx => hSG hx)
        have hSGcard : SG.card = k := by
          rw [← hScard, ← hSGmap, Finset.card_map]
        have hSGH : SG ⊆ H := by
          intro x hx
          have hxS : (x : X) ∈ S := Finset.mem_subtype.1 hx
          have hxH' := hSH' hxS
          obtain ⟨y, hyH, hyx⟩ := Finset.mem_map.1 hxH'
          apply Subtype.ext at hyx
          simpa [hyx] using hyH
        simpa [cG, hSGmap] using hword SG hSGcard hSGH
      · have hkeq : k = q + 1 := by omega
        subst k
        refine ⟨wordTop, ?_⟩
        intro S hScard hSH'
        apply hGhom S hScard
        intro x hx
        exact Finset.property_of_mem_map_subtype H (hSH' hx)

theorem solution (Alphabet : Type*) [Fintype Alphabet] (m : ℕ) (hm : 1 ≤ m) :
    ∃ N : ℕ, m ≤ N ∧
      ∀ c : (k : ℕ) → 1 ≤ k → k ≤ m →
        {S : Finset (Fin N) // S.card = k} → (Fin k → Alphabet),
      ∃ H : Finset (Fin N), H.card = m ∧
        ∀ (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m), ∃ word : Fin k → Alphabet,
          ∀ (S : Finset (Fin N)) (hS : S.card = k), S ⊆ H →
            c k hk hkm ⟨S, hS⟩ = word := by
  classical
  by_cases hA : Nonempty Alphabet
  · letI : Nonempty Alphabet := hA
    obtain ⟨N, hmN, hN⟩ := iteratedRamseyOn Alphabet m m hm le_rfl
    refine ⟨N, hmN, ?_⟩
    intro c
    simpa using hN (Fin N) (by simp) c
  · push_neg at hA
    refine ⟨m, le_rfl, ?_⟩
    intro c
    have hnonempty : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    letI : Nonempty (Fin m) := hnonempty
    exact False.elim (hA.false (c 1 (by omega) hm
      ⟨{⟨0, hm⟩}, by simp⟩ 0))
