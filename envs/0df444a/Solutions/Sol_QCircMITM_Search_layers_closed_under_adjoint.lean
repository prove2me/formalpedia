-- Prove2me | solution 1 for QCircMITM.Search.layers_closed_under_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T21:38:31.184177+00:00
-- url     : https://prove2.me/submissions/4578ce38-050b-463c-bfed-451b6a95eb2c

import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QCircMITM_Search_Layers

open QAlgorithms QCircMITM.Search

lemma star_lprod {n : ℕ} (l : List (Matrix (Qubits n) (Qubits n) ℂ)) :
    star l.prod = (l.map star).reverse.prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.prod_cons, star_mul, ih]

lemma embed_star {k n : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    star (embedOp M w) = embedOp (star M) w := by
  ext y z
  simp only [embedOp, Matrix.star_apply, Matrix.of_apply]
  by_cases h : ∀ a : Fin n, a ∉ Set.range w → z a = y a
  · have h' : ∀ a : Fin n, a ∉ Set.range w → y a = z a := fun a ha => (h a ha).symm
    rw [if_pos h, if_pos h']
  · have h' : ¬ ∀ a : Fin n, a ∉ Set.range w → y a = z a := fun h2 => h fun a ha => (h2 a ha).symm
    rw [if_neg h, if_neg h', star_zero]

lemma sum_glue {k n : ℕ} (w : Fin k ↪ Fin n) (y : Qubits n) (F : Qubits k → ℂ) :
    ∑ x : Qubits n, (if ∀ a : Fin n, a ∉ Set.range w → y a = x a then F (x ∘ w) else 0) =
      ∑ u : Qubits k, F u := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun x => x ∘ w) (fun u => Function.extend w u y) ?_ ?_ ?_ ?_ ?_
  · intro x _; simp
  · intro u _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro a ha
    rw [Function.extend_apply']
    rintro ⟨b, rfl⟩; exact ha ⟨b, rfl⟩
  · intro x hx
    have hx' : ∀ a : Fin n, a ∉ Set.range w → y a = x a := by simpa using hx
    funext a
    by_cases ha : a ∈ Set.range w
    · obtain ⟨b, rfl⟩ := ha
      exact w.injective.extend_apply _ _ _
    · rw [Function.extend_apply' _ _ _ (fun ⟨b, hb⟩ => ha ⟨b, hb⟩)]
      exact hx' a ha
  · intro u _
    funext b
    exact w.injective.extend_apply _ _ _
  · intro x _; rfl

lemma embed_mul {k n : ℕ} (A B : Matrix (Qubits k) (Qubits k) ℂ) (w : Fin k ↪ Fin n) :
    embedOp A w * embedOp B w = embedOp (A * B) w := by
  ext y z
  simp only [Matrix.mul_apply, embedOp, Matrix.of_apply]
  by_cases hyz : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · rw [if_pos hyz]
    have : ∀ x : Qubits n,
        (if ∀ a : Fin n, a ∉ Set.range w → y a = x a then A (y ∘ w) (x ∘ w) else 0) *
          (if ∀ a : Fin n, a ∉ Set.range w → x a = z a then B (x ∘ w) (z ∘ w) else 0) =
        if ∀ a : Fin n, a ∉ Set.range w → y a = x a then
          (fun u => A (y ∘ w) u * B u (z ∘ w)) (x ∘ w) else 0 := by
      intro x
      by_cases h1 : ∀ a : Fin n, a ∉ Set.range w → y a = x a
      · have h2 : ∀ a : Fin n, a ∉ Set.range w → x a = z a :=
          fun a ha => (h1 a ha).symm.trans (hyz a ha)
        rw [if_pos h1, if_pos h2, if_pos h1]
      · rw [if_neg h1, if_neg h1, zero_mul]
    rw [Finset.sum_congr rfl (fun x _ => this x)]
    convert sum_glue w y (fun u => A (y ∘ w) u * B u (z ∘ w)) using 1
  · rw [if_neg hyz]
    apply Finset.sum_eq_zero
    intro x _
    by_cases h1 : ∀ a : Fin n, a ∉ Set.range w → y a = x a
    · have h2 : ¬ ∀ a : Fin n, a ∉ Set.range w → x a = z a :=
        fun h2 => hyz fun a ha => (h1 a ha).trans (h2 a ha)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

lemma embed_one {k n : ℕ} (w : Fin k ↪ Fin n) :
    embedOp (1 : Matrix (Qubits k) (Qubits k) ℂ) w = 1 := by
  ext y z
  simp only [embedOp, Matrix.of_apply, Matrix.one_apply]
  by_cases hyz : y = z
  · subst hyz; simp
  · rw [if_neg hyz]
    split_ifs with h1 h2
    · exfalso; apply hyz; funext a
      by_cases ha : a ∈ Set.range w
      · obtain ⟨b, rfl⟩ := ha
        exact congrFun h2 b
      · exact h1 a ha
    · rfl
    · rfl

theorem solution {G : Set QAlgorithms.Gate} {n : ℕ}
    (hG : QAlgorithms.ClosedUnderInverse G)
    {M : Matrix (QAlgorithms.Qubits n) (QAlgorithms.Qubits n) ℂ} (hM : M ∈ depthOneSet G n) :
    star M ∈ depthOneSet G n ∧
      ((∀ g ∈ G, g.IsUnitary) → M ∈ Matrix.unitaryGroup (QAlgorithms.Qubits n) ℂ) := by
  obtain ⟨c, hne, hpw, rfl⟩ := hM
  constructor
  · let adj : GateApp G n → GateApp G n := fun g =>
      ⟨⟨g.gate.arity, star g.gate.mat⟩, hG _ g.mem, g.wires⟩
    refine ⟨c.reverse.map adj, ?_, ?_, ?_⟩
    · simpa using hne
    · rw [List.pairwise_map, List.pairwise_reverse]
      exact hpw.imp fun h => h.symm
    · unfold Circuit.unitary
      simp only [star_lprod, List.map_reverse, List.reverse_reverse, List.map_map]
      congr 1
      apply List.map_congr_left
      intro g _
      simp only [Function.comp_apply, adj]
      exact embed_star _ _
  · intro hU
    unfold Circuit.unitary
    apply Submonoid.list_prod_mem
    intro x hx
    rw [List.mem_reverse, List.mem_map] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    rw [Matrix.mem_unitaryGroup_iff, embed_star, embed_mul]
    have := hU g.gate g.mem
    rw [Gate.IsUnitary, Matrix.mem_unitaryGroup_iff] at this
    rw [this, embed_one]
