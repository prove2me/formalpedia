-- Prove2me | solution 1 for OPG37271.k33_exact_six
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-07T16:12:15.068633+00:00
-- url     : https://prove2.me/submissions/28279ac2-7a6b-4383-afef-c7838ac9b1e7

import Mathlib
import Definitions.Def_opg37271_star_edge_coloring

open SimpleGraph Finset

namespace K33

abbrev V := Fin 3 ⊕ Fin 3
abbrev G : SimpleGraph V := completeBipartiteGraph (Fin 3) (Fin 3)

instance instAdjDec (v w : V) : Decidable (G.Adj v w) :=
  inferInstanceAs (Decidable (v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft))

lemma adjLR (i j : Fin 3) : G.Adj (Sum.inl i) (Sum.inr j) := Or.inl ⟨rfl, rfl⟩
lemma adjRL (i j : Fin 3) : G.Adj (Sum.inr j) (Sum.inl i) := Or.inr ⟨rfl, rfl⟩

/-! ### Six colours suffice -/

def Mtab : Fin 3 → Fin 3 → Fin 6 := ![![0, 1, 2], ![1, 3, 4], ![2, 4, 5]]

def gcol : V → V → Fin 6
  | Sum.inl i, Sum.inr j => Mtab i j
  | Sum.inr j, Sum.inl i => Mtab i j
  | _, _ => 0

lemma gcol_symm : ∀ a b : V, gcol a b = gcol b a := by decide

def fcol : Sym2 V → Fin 6 := Sym2.lift ⟨gcol, fun a b => gcol_symm a b⟩

def ccol : OPG37271.EdgeColoring G (Fin 6) := fun e => fcol e.1

lemma ccol_get (x y : V) (h : G.Adj x y) : ccol.get x y h = gcol x y :=
  Sym2.lift_mk _ x y

lemma proper_aux : ∀ v u w : V, G.Adj v u → G.Adj v w → u ≠ w → gcol v u ≠ gcol v w := by decide

set_option synthInstance.maxSize 4000 in
lemma noP4_aux : ∀ v0 v1 v2 v3 v4 : V,
    (v0 ≠ v1 ∧ v0 ≠ v2 ∧ v0 ≠ v3 ∧ v0 ≠ v4 ∧ v1 ≠ v2 ∧ v1 ≠ v3 ∧ v1 ≠ v4 ∧
      v2 ≠ v3 ∧ v2 ≠ v4 ∧ v3 ≠ v4) →
    (G.Adj v0 v1 ∧ G.Adj v1 v2 ∧ G.Adj v2 v3 ∧ G.Adj v3 v4) →
    ¬ (gcol v0 v1 = gcol v2 v3 ∧ gcol v1 v2 = gcol v3 v4) := by decide

set_option synthInstance.maxSize 4000 in
lemma noC4_aux : ∀ v0 v1 v2 v3 : V,
    (v0 ≠ v1 ∧ v0 ≠ v2 ∧ v0 ≠ v3 ∧ v1 ≠ v2 ∧ v1 ≠ v3 ∧ v2 ≠ v3) →
    (G.Adj v0 v1 ∧ G.Adj v1 v2 ∧ G.Adj v2 v3 ∧ G.Adj v3 v0) →
    ¬ (gcol v0 v1 = gcol v2 v3 ∧ gcol v1 v2 = gcol v3 v0) := by decide

lemma star6 : OPG37271.IsStarEdgeColoring ccol := by
  refine ⟨?_, ?_, ?_⟩
  · intro v u w hvu hvw huw
    rw [ccol_get, ccol_get]
    exact proper_aux v u w hvu hvw huw
  · rintro ⟨v0, v1, v2, v3, v4, hnd, h01, h12, h23, h34, e1, e2⟩
    rw [ccol_get, ccol_get] at e1
    rw [ccol_get, ccol_get] at e2
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, not_or,
      List.mem_singleton, and_true, or_false] at hnd
    exact noP4_aux v0 v1 v2 v3 v4 (by tauto) ⟨h01, h12, h23, h34⟩ ⟨e1, e2⟩
  · rintro ⟨v0, v1, v2, v3, hnd, h01, h12, h23, h30, e1, e2⟩
    rw [ccol_get, ccol_get] at e1
    rw [ccol_get, ccol_get] at e2
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, not_or,
      List.mem_singleton, and_true, or_false] at hnd
    exact noC4_aux v0 v1 v2 v3 (by tauto) ⟨h01, h12, h23, h30⟩ ⟨e1, e2⟩

lemma has_six : OPG37271.HasStarEdgeColoring G 6 := ⟨ccol, star6⟩

/-! ### Five colours do not suffice -/

def MOf (a b c d e f g h i : Fin 5) : Fin 3 → Fin 3 → Fin 5
  | 0, 0 => a | 0, 1 => b | 0, 2 => c
  | 1, 0 => d | 1, 1 => e | 1, 2 => f
  | 2, 0 => g | 2, 1 => h | 2, 2 => i

/-- A proper `5`-colouring of the nine edges always contains a bichromatic
four-cycle or a bichromatic path with four edges. -/
abbrev BAD (M : Fin 3 → Fin 3 → Fin 5) : Prop :=
  (∃ i k j l : Fin 3, i ≠ k ∧ j ≠ l ∧ M i j = M k l ∧ M k j = M i l) ∨
  (∃ a c e b d : Fin 3, a ≠ c ∧ c ≠ e ∧ a ≠ e ∧ b ≠ d ∧ M a b = M c d ∧ M c b = M e d) ∨
  (∃ a c e b d : Fin 3, a ≠ c ∧ c ≠ e ∧ a ≠ e ∧ b ≠ d ∧ M b a = M d c ∧ M b c = M d e)

lemma bad_of_inj {σ : Fin 5 → Fin 5} (hσ : Function.Injective σ)
    {M : Fin 3 → Fin 3 → Fin 5} (h : BAD (fun i j => σ (M i j))) : BAD M := by
  rcases h with ⟨i, k, j, l, h1, h2, h3, h4⟩ | ⟨a, c, e, b, d, h1, h2, h3, h4, h5, h6⟩ |
      ⟨a, c, e, b, d, h1, h2, h3, h4, h5, h6⟩
  · exact Or.inl ⟨i, k, j, l, h1, h2, hσ h3, hσ h4⟩
  · exact Or.inr (Or.inl ⟨a, c, e, b, d, h1, h2, h3, h4, hσ h5, hσ h6⟩)
  · exact Or.inr (Or.inr ⟨a, c, e, b, d, h1, h2, h3, h4, hσ h5, hσ h6⟩)

/-- Any three distinct colours can be moved to `0, 1, 2` by a permutation. -/
lemma exists_norm (a b c : Fin 5) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ σ : Fin 5 → Fin 5, Function.Injective σ ∧ σ a = 0 ∧ σ b = 1 ∧ σ c = 2 := by
  classical
  let τ0 : Equiv.Perm (Fin 5) := Equiv.swap a 0
  have hτ0a : τ0 a = 0 := Equiv.swap_apply_left a 0
  have hx1 : τ0 b ≠ 0 := by
    rw [← hτ0a]
    exact fun hh => hab (τ0.injective hh.symm)
  let τ1 : Equiv.Perm (Fin 5) := Equiv.swap (τ0 b) 1
  have hτ1b : τ1 (τ0 b) = 1 := Equiv.swap_apply_left _ 1
  have hτ10 : τ1 0 = 0 := Equiv.swap_apply_of_ne_of_ne (Ne.symm hx1) (by decide)
  have hx2a : τ1 (τ0 c) ≠ 0 := by
    rw [← hτ10, ← hτ0a]
    exact fun hh => hac (τ0.injective (τ1.injective hh.symm))
  have hx2b : τ1 (τ0 c) ≠ 1 := by
    rw [← hτ1b]
    exact fun hh => hbc (τ0.injective (τ1.injective hh)).symm
  let τ2 : Equiv.Perm (Fin 5) := Equiv.swap (τ1 (τ0 c)) 2
  refine ⟨fun z => τ2 (τ1 (τ0 z)), ?_, ?_, ?_, ?_⟩
  · exact fun x y hh => τ0.injective (τ1.injective (τ2.injective hh))
  · simp only [hτ0a, hτ10]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hx2a) (by decide)
  · simp only [hτ1b]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hx2b) (by decide)
  · exact Equiv.swap_apply_left _ 2

set_option maxRecDepth 40000 in
set_option synthInstance.maxSize 4000 in
lemma key0 : ∀ d e f : Fin 5,
    (d ≠ e ∧ d ≠ f ∧ e ≠ f ∧ (0 : Fin 5) ≠ d ∧ (1 : Fin 5) ≠ e ∧ (2 : Fin 5) ≠ f) →
    ∀ g h i : Fin 5,
    (g ≠ h ∧ g ≠ i ∧ h ≠ i ∧ (0 : Fin 5) ≠ g ∧ (1 : Fin 5) ≠ h ∧ (2 : Fin 5) ≠ i ∧
      d ≠ g ∧ e ≠ h ∧ f ≠ i) →
    BAD (MOf 0 1 2 d e f g h i) := by decide +kernel

lemma key (M : Fin 3 → Fin 3 → Fin 5)
    (hrow : ∀ i j k : Fin 3, j ≠ k → M i j ≠ M i k)
    (hcol : ∀ i j k : Fin 3, i ≠ k → M i j ≠ M k j) : BAD M := by
  obtain ⟨σ, hinj, e0, e1, e2⟩ := exists_norm (M 0 0) (M 0 1) (M 0 2)
    (hrow 0 0 1 (by decide)) (hrow 0 0 2 (by decide)) (hrow 0 1 2 (by decide))
  refine bad_of_inj hinj ?_
  have hr : ∀ i j k : Fin 3, j ≠ k → σ (M i j) ≠ σ (M i k) :=
    fun i j k hjk hh => hrow i j k hjk (hinj hh)
  have hc : ∀ i j k : Fin 3, i ≠ k → σ (M i j) ≠ σ (M k j) :=
    fun i j k hik hh => hcol i j k hik (hinj hh)
  have hEq : MOf 0 1 2 (σ (M 1 0)) (σ (M 1 1)) (σ (M 1 2))
      (σ (M 2 0)) (σ (M 2 1)) (σ (M 2 2)) = fun i j => σ (M i j) := by
    funext i j
    match i, j with
    | 0, 0 => exact e0.symm
    | 0, 1 => exact e1.symm
    | 0, 2 => exact e2.symm
    | 1, 0 => rfl
    | 1, 1 => rfl
    | 1, 2 => rfl
    | 2, 0 => rfl
    | 2, 1 => rfl
    | 2, 2 => rfl
  rw [← hEq]
  refine key0 _ _ _ ⟨hr 1 0 1 (by decide), hr 1 0 2 (by decide), hr 1 1 2 (by decide),
      ?_, ?_, ?_⟩ _ _ _ ⟨hr 2 0 1 (by decide), hr 2 0 2 (by decide), hr 2 1 2 (by decide),
      ?_, ?_, ?_, hc 1 0 2 (by decide), hc 1 1 2 (by decide), hc 1 2 2 (by decide)⟩
  · rw [← e0]; exact hc 0 0 1 (by decide)
  · rw [← e1]; exact hc 0 1 1 (by decide)
  · rw [← e2]; exact hc 0 2 1 (by decide)
  · rw [← e0]; exact hc 0 0 2 (by decide)
  · rw [← e1]; exact hc 0 1 2 (by decide)
  · rw [← e2]; exact hc 0 2 2 (by decide)

lemma no_five : ¬ OPG37271.HasStarEdgeColoring G 5 := by
  rintro ⟨c, hp, hnp, hnc⟩
  set M : Fin 3 → Fin 3 → Fin 5 :=
    fun i j => c.get (Sum.inl i) (Sum.inr j) (adjLR i j) with hMdef
  have hswap : ∀ i j : Fin 3, c.get (Sum.inr j) (Sum.inl i) (adjRL i j) = M i j := by
    intro i j
    rw [hMdef]
    exact SimpleGraph.EdgeLabeling.get_comm _ _ _
  have hrow : ∀ i j k : Fin 3, j ≠ k → M i j ≠ M i k := by
    intro i j k hjk
    exact hp (Sum.inl i) (Sum.inr j) (Sum.inr k) (adjLR i j) (adjLR i k) (by simpa using hjk)
  have hcol : ∀ i j k : Fin 3, i ≠ k → M i j ≠ M k j := by
    intro i j k hik
    have h := hp (Sum.inr j) (Sum.inl i) (Sum.inl k) (adjRL i j) (adjRL k j) (by simpa using hik)
    rwa [hswap, hswap] at h
  have hbad : BAD M := key M hrow hcol
  rcases hbad with ⟨i, k, j, l, hik, hjl, h1, h2⟩ | ⟨a, cc, e, b, d, hac, hce, hae, hbd, h1, h2⟩ |
      ⟨a, cc, e, b, d, hac, hce, hae, hbd, h1, h2⟩
  · refine hnc ⟨Sum.inl i, Sum.inr j, Sum.inl k, Sum.inr l, ?_,
      adjLR i j, adjRL k j, adjLR k l, adjRL i l, ?_, ?_⟩
    · simp [hik, hjl]
    · exact h1
    · rw [hswap, hswap]; exact h2
  · refine hnp ⟨Sum.inl a, Sum.inr b, Sum.inl cc, Sum.inr d, Sum.inl e, ?_,
      adjLR a b, adjRL cc b, adjLR cc d, adjRL e d, ?_, ?_⟩
    · simp [hac, hce, hae, hbd, Ne.symm hac, Ne.symm hce, Ne.symm hae, Ne.symm hbd]
    · exact h1
    · rw [hswap, hswap]; exact h2
  · refine hnp ⟨Sum.inr a, Sum.inl b, Sum.inr cc, Sum.inl d, Sum.inr e, ?_,
      adjRL b a, adjLR b cc, adjRL d cc, adjLR d e, ?_, ?_⟩
    · simp [hac, hce, hae, hbd, Ne.symm hac, Ne.symm hce, Ne.symm hae, Ne.symm hbd]
    · rw [hswap, hswap]; exact h1
    · exact h2

end K33

theorem solution :
    OPG37271.HasStarEdgeColoring (completeBipartiteGraph (Fin 3) (Fin 3)) 6 ∧
    ¬ OPG37271.HasStarEdgeColoring (completeBipartiteGraph (Fin 3) (Fin 3)) 5 :=
  ⟨K33.has_six, K33.no_five⟩
