-- Prove2me | solution 1 for TuranMatching.Clique.extremal_graphs_admissible
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:43:41.053075+00:00
-- url     : https://prove2.me/submissions/af9f1f69-1c93-4c66-95f1-2664e3333c85

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting

set_option autoImplicit false
open Finset SimpleGraph

namespace TMCAux

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma card_le_matchingNumber (G : SimpleGraph V) (E : Finset (Sym2 V))
    (hE : ∀ e ∈ E, e ∈ G.edgeSet)
    (hd : ∀ e ∈ E, ∀ e' ∈ E, ∀ v, v ∈ e → v ∈ e' → e = e') :
    E.card ≤ TuranMatching.Clique.matchingNumber G := by
  let M : G.Subgraph :=
    { verts := {v | ∃ e ∈ E, v ∈ e}
      Adj := fun a b => s(a, b) ∈ E
      adj_sub := fun {a b} h => hE _ h
      edge_vert := fun {a b} h => ⟨_, h, Sym2.mem_mk_left a b⟩
      symm := ⟨fun a b (h : s(a, b) ∈ E) => by rwa [Sym2.eq_swap]⟩ }
  have hM : M.IsMatching := by
    intro v hv
    obtain ⟨e, he, hve⟩ := hv
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hve
    refine ⟨w, he, fun w' (hw' : s(v, w') ∈ E) => ?_⟩
    exact Sym2.congr_right.mp (hd _ hw' _ he v (Sym2.mem_mk_left _ _) (Sym2.mem_mk_left _ _))
  have hedge : M.edgeSet = (↑E : Set (Sym2 V)) := by
    ext e
    induction e using Sym2.ind with
    | h a b => exact Iff.rfl
  have hbdd : BddAbove {m | ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = m} := by
    refine ⟨(Set.univ : Set (Sym2 V)).ncard, ?_⟩
    rintro m ⟨M', -, rfl⟩
    exact Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
  calc E.card = (↑E : Set (Sym2 V)).ncard := (Set.ncard_coe_finset E).symm
    _ = M.edgeSet.ncard := by rw [hedge]
    _ ≤ _ := le_csSup hbdd ⟨M, hM, rfl⟩

end TMCAux

namespace TMCAux

lemma bigClass_lt (k s : ℕ) (hk : 2 ≤ k) {n : ℕ} (v : Fin n) :
    TuranMatching.Clique.bigClass k s v < k := by
  unfold TuranMatching.Clique.bigClass
  split_ifs
  · have : (v : ℕ) % (k - 1) < k - 1 := Nat.mod_lt _ (by omega)
    omega
  · omega

lemma adj_lt_ge (n k s : ℕ) (hk : 2 ≤ k) (v w : Fin n) (hv : (v : ℕ) < s) (hw : s ≤ (w : ℕ)) :
    (TuranMatching.Clique.bigGraph n k s).Adj v w := by
  show TuranMatching.Clique.bigClass k s v ≠ TuranMatching.Clique.bigClass k s w
  simp only [TuranMatching.Clique.bigClass, hv, if_true, not_lt.mpr hw, if_false]
  have : (v : ℕ) % (k - 1) < k - 1 := Nat.mod_lt _ (by omega)
  omega

lemma not_adj_ge (n k s : ℕ) (v w : Fin n) (hv : s ≤ (v : ℕ)) (hw : s ≤ (w : ℕ)) :
    ¬ (TuranMatching.Clique.bigGraph n k s).Adj v w := by
  show ¬ (TuranMatching.Clique.bigClass k s v ≠ TuranMatching.Clique.bigClass k s w)
  simp [TuranMatching.Clique.bigClass, not_lt.mpr hv, not_lt.mpr hw]

lemma colorable (n k s : ℕ) (hk : 2 ≤ k) : (TuranMatching.Clique.bigGraph n k s).Colorable k := by
  refine ⟨Coloring.mk (fun v => (⟨TuranMatching.Clique.bigClass k s v, bigClass_lt k s hk v⟩ : Fin k)) ?_⟩
  intro v w h hc
  exact h (by simpa using congrArg Fin.val hc)

lemma free (n k s : ℕ) (hk : 2 ≤ k) (W : Type) (H : SimpleGraph W)
    (hH : H.chromaticNumber = ((k + 1 : ℕ) : ℕ∞)) : H.Free (TuranMatching.Clique.bigGraph n k s) := by
  rintro ⟨f⟩
  obtain ⟨C⟩ := colorable n k s hk
  have hcol : H.Colorable k := ⟨C.comp f.toHom⟩
  have := hcol.chromaticNumber_le
  rw [hH] at this
  have h2 : (k + 1 : ℕ) ≤ k := by exact_mod_cast this
  omega

lemma matching_ge (n k s : ℕ) (hk : 2 ≤ k) (hn : 2 * s ≤ n) :
    s ≤ TuranMatching.Clique.matchingNumber (TuranMatching.Clique.bigGraph n k s) := by
  classical
  let a : Fin s → Fin n := fun i => ⟨i, by omega⟩
  let b : Fin s → Fin n := fun i => ⟨s + i, by omega⟩
  have hinj : Function.Injective (fun i : Fin s => s(a i, b i)) := by
    intro i j h
    simp only at h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h, -⟩ | ⟨h, -⟩
    · exact Fin.ext (by simpa [a] using congrArg Fin.val h)
    · have := congrArg Fin.val h
      simp only [a, b] at this
      omega
  have := card_le_matchingNumber (TuranMatching.Clique.bigGraph n k s)
    (Finset.univ.image (fun i : Fin s => s(a i, b i)))
    (by
      intro e he
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp he
      exact adj_lt_ge n k s hk _ _ i.2 (by simp [b]))
    (by
      intro e he e' he' v hv hv'
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp he'
      rw [Sym2.mem_iff] at hv hv'
      have hi := i.2
      have hj := j.2
      rcases hv with rfl | rfl <;> rcases hv' with h | h <;>
        have h' := congrArg Fin.val h <;> simp only [a, b] at h' ⊢
      · rw [Fin.ext (show (i : ℕ) = j by omega)]
      · omega
      · omega
      · rw [Fin.ext (show (i : ℕ) = j by omega)])
  rwa [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at this

lemma matching_le (n k s : ℕ) (hn : 2 * s ≤ n) :
    TuranMatching.Clique.matchingNumber (TuranMatching.Clique.bigGraph n k s) ≤ s := by
  classical
  unfold TuranMatching.Clique.matchingNumber
  apply csSup_le'
  rintro m ⟨M, hM, rfl⟩
  let g : Fin s → Fin n := fun i => ⟨i.1, by have := i.2; omega⟩
  let T : Finset (Fin n) := (Finset.univ : Finset (Fin s)).image g
  have hT : T.card ≤ s := by
    calc T.card ≤ (Finset.univ : Finset (Fin s)).card := Finset.card_image_le
      _ = s := by simp
  let f : Sym2 (Fin n) → Fin n := Sym2.lift ⟨fun a b => min a b, fun a b => min_comm a b⟩
  have hf : ∀ c d : Fin n, M.Adj c d → ∃ c' d' : Fin n, s(c, d) = s(c', d') ∧ f s(c, d) = c' ∧ M.Adj c' d' := by
    intro c d h
    rcases le_total c d with hcd | hcd
    · exact ⟨c, d, rfl, by simp [f, hcd], h⟩
    · exact ⟨d, c, Sym2.eq_swap, by simp [f, hcd], h.symm⟩
  calc M.edgeSet.ncard ≤ (↑T : Set (Fin n)).ncard := by
        apply Set.ncard_le_ncard_of_injOn f
        · intro e he
          induction e using Sym2.ind with
          | h c d =>
            have hadj : M.Adj c d := he
            have hG := M.adj_sub hadj
            have hlt : (min c d : ℕ) < s := by
              by_contra hcon
              push_neg at hcon
              exact TMCAux.not_adj_ge n k s c d (le_trans hcon (by simp)) (le_trans hcon (by simp)) hG
            simp only [Finset.mem_coe, T, Finset.mem_image, Finset.mem_univ, true_and]
            refine ⟨⟨(min c d : ℕ), hlt⟩, ?_⟩
            simp [f, g, Fin.ext_iff]
        · intro e he e' he' hee
          induction e using Sym2.ind with
          | h c d =>
          induction e' using Sym2.ind with
          | h c₂ d₂ =>
            obtain ⟨c', d', h1, h2, h3⟩ := hf c d he
            obtain ⟨c₂', d₂', h1', h2', h3'⟩ := hf c₂ d₂ he'
            have hcc : c' = c₂' := by rw [← h2, ← h2']; exact hee
            subst hcc
            have := hM.eq_of_adj_left h3 h3'
            rw [h1, h1', this]
    _ = T.card := Set.ncard_coe_finset T
    _ ≤ s := hT

end TMCAux
open TuranMatching.Clique

theorem tmk_matching_small (n m : ℕ) (G : SimpleGraph (Fin n))
    (hG : ∀ v w, G.Adj v w → (v : ℕ) < m ∧ (w : ℕ) < m) :
    matchingNumber G ≤ m / 2 := by
  classical
  unfold matchingNumber
  apply csSup_le'
  rintro c ⟨M, hM, rfl⟩
  have hfin : M.edgeSet.Finite := Set.toFinite _
  let E : Finset (Sym2 (Fin n)) := hfin.toFinset
  have hE : ∀ e ∈ E, e ∈ M.edgeSet := fun e he => hfin.mem_toFinset.1 he
  have hdisj : ∀ e ∈ E, ∀ e' ∈ E, ∀ v, v ∈ e → v ∈ e' → e = e' := by
    intro e he e' he' v hv hv'
    have he1 := hE e he
    have he2 := hE e' he'
    obtain ⟨a, rfl⟩ := Sym2.mem_iff_exists.mp hv
    obtain ⟨b, rfl⟩ := Sym2.mem_iff_exists.mp hv'
    have h1 : M.Adj v a := he1
    have h2 : M.Adj v b := he2
    rw [hM.eq_of_adj_left h1 h2]
  have hcard : ∀ e ∈ E, (Sym2.toFinset e).card = 2 := by
    intro e he
    apply Sym2.card_toFinset_of_not_isDiag
    have := hE e he
    exact M.edgeSet_subset this |> G.not_isDiag_of_mem_edgeSet
  have hdj : (E : Set (Sym2 (Fin n))).PairwiseDisjoint (fun e => Sym2.toFinset e) := by
    intro e he e' he' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro v hv hv'
    apply hne
    exact hdisj e he e' he' v (by simpa using hv) (by simpa using hv')
  have hU : (E.biUnion (fun e => Sym2.toFinset e)).card = 2 * E.card := by
    rw [Finset.card_biUnion hdj, Finset.sum_congr rfl hcard]
    simp [mul_comm]
  have hsub : E.biUnion (fun e => Sym2.toFinset e) ⊆ Finset.univ.filter (fun v : Fin n => (v : ℕ) < m) := by
    intro v hv
    rw [Finset.mem_biUnion] at hv
    obtain ⟨e, he, hve⟩ := hv
    have hmem : v ∈ e := by simpa using hve
    have h1 := hE e he
    revert hmem h1
    induction e using Sym2.ind with
    | h a b =>
      intro hmem h1
      have hadj : M.Adj a b := h1
      have := hG a b (M.adj_sub hadj)
      rw [Sym2.mem_iff] at hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hmem with rfl | rfl
      · exact this.1
      · exact this.2
  have hle : (Finset.univ.filter (fun v : Fin n => (v : ℕ) < m)).card ≤ m := by
    calc _ ≤ (Finset.range m).card := by
          apply Finset.card_le_card_of_injOn (fun v : Fin n => (v : ℕ))
          · intro v hv
            simpa using (Finset.mem_filter.1 hv).2
          · intro v _ w _ h
            exact Fin.ext h
      _ = m := Finset.card_range m
  have h2 : 2 * E.card ≤ m := by
    rw [← hU]; exact (Finset.card_le_card hsub).trans hle
  have : M.edgeSet.ncard = E.card := by
    rw [Set.ncard_eq_toFinset_card _ hfin]
  rw [this]
  omega

theorem tmk_admissible (n k s : ℕ) (hk : 2 ≤ k) (hn : 2 * s + 1 ≤ n) :
    Admissible k s (bigGraph n k s) ∧
    ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), Admissible k s G ∧
        #G.edgeFinset = turanNum (2 * s + 1) k := by
  classical
  refine ⟨⟨(TMCAux.colorable n k s hk).cliqueFree (by omega), ?_⟩, ?_⟩
  · exact TMCAux.matching_le n k s (by omega)
  · let f : Fin (2 * s + 1) ↪ Fin n := Fin.castLEEmb hn
    refine ⟨(turanGraph (2 * s + 1) k).map f, inferInstance, ⟨?_, ?_⟩, ?_⟩
    · rw [cliqueFree_map_iff]
      exact turanGraph_cliqueFree (by omega)
    · have := tmk_matching_small n (2 * s + 1) ((turanGraph (2 * s + 1) k).map f) (by
        intro v w h
        rw [SimpleGraph.map_adj] at h
        obtain ⟨a, b, _, rfl, rfl⟩ := h
        exact ⟨a.2, b.2⟩)
      have h2 : (2 * s + 1) / 2 = s := by omega
      omega
    · unfold turanNum
      convert SimpleGraph.card_edgeFinset_map f (turanGraph (2 * s + 1) k)

theorem solution (n k s : ℕ) (hk : 2 ≤ k) (hn : 2 * s + 1 ≤ n) :
    Admissible k s (bigGraph n k s) ∧
    ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), Admissible k s G ∧
        #G.edgeFinset = turanNum (2 * s + 1) k :=
  tmk_admissible n k s hk hn
