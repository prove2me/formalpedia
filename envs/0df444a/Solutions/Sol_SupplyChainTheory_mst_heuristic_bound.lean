-- Prove2me | solution 1 for SupplyChainTheory.mst_heuristic_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T20:49:36.726986+00:00
-- url     : https://prove2.me/submissions/928f8f24-0416-460a-a392-cedf3a817690

import Mathlib
import Definitions.Def_SupplyChainTheory_tsp
import Theorems.Thm_SupplyChainTheory_mst_lower_bound

open Classical SupplyChainTheory

private lemma rot_castSucc {m : ℕ} (i : Fin m) : finRotate (m + 1) i.castSucc = i.succ :=
  finRotate_of_lt i.isLt

/-- A tour is its Hamiltonian path plus the closing edge. -/
private lemma tourLength_eq_path {m : ℕ} (c : Fin (m + 1) → Fin (m + 1) → ℝ)
    (τ : Equiv.Perm (Fin (m + 1))) :
    tourLength c τ = ∑ i : Fin m, c (τ i.castSucc) (τ i.succ) + c (τ (Fin.last m)) (τ 0) := by
  rw [tourLength, Fin.sum_univ_castSucc, finRotate_last]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [rot_castSucc]

/-! ### Chains of triangle inequalities -/

/-- One segment: `c(h a, h b) ≤ ∑_{a ≤ i < b} c(h i, h (i+1))`. -/
private lemma segment_le {α : Type*} (c : α → α → ℝ) (hrefl : ∀ x, c x x = 0)
    (htri : ∀ x y z, c x z ≤ c x y + c y z) (h : ℕ → α) (a : ℕ) :
    ∀ b, a ≤ b → c (h a) (h b) ≤ ∑ i ∈ Finset.Ico a b, c (h i) (h (i + 1)) := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => simp [hrefl]
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab]
    linarith [htri (h a) (h b) (h (b + 1))]

private lemma mono_chain (q : ℕ → ℕ) (K : ℕ) (hq : ∀ j < K, q j ≤ q (j + 1)) : q 0 ≤ q K := by
  induction K with
  | zero => exact le_refl _
  | succ K ih => exact (ih (fun j hj => hq j (by omega))).trans (hq K (by omega))

/-- Visiting the points `h (q 0), h (q 1), …, h (q K)` directly is no longer than following
`h` step by step from `q 0` to `q K`. -/
private lemma chain_le {α : Type*} (c : α → α → ℝ) (hrefl : ∀ x, c x x = 0)
    (htri : ∀ x y z, c x z ≤ c x y + c y z) (h : ℕ → α) (q : ℕ → ℕ) (K : ℕ)
    (hq : ∀ j < K, q j ≤ q (j + 1)) :
    ∑ j ∈ Finset.range K, c (h (q j)) (h (q (j + 1)))
      ≤ ∑ i ∈ Finset.Ico (q 0) (q K), c (h i) (h (i + 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ← Finset.sum_Ico_consecutive _
      (mono_chain q K (fun j hj => hq j (by omega))) (hq K (by omega))]
    have := segment_le c hrefl htri h (q K) (q (K + 1)) (hq K (by omega))
    linarith [ih (fun j hj => hq j (by omega))]
/-! ### Shortcutting a closed walk does not lengthen it -/

/-- The length of a walk, `∑ᵢ c(wᵢ, wᵢ₊₁)`. -/
private noncomputable def walkLen {V : Type*} {G : SimpleGraph V} (c : V → V → ℝ) {u v : V}
    (W : G.Walk u v) : ℝ :=
  ∑ i ∈ Finset.range W.length, c (W.getVert i) (W.getVert (i + 1))

/-- Under symmetric distances the length of a walk is the total cost of its edge list. -/
private lemma walkLen_eq_edges {n : ℕ} {G : SimpleGraph (Fin n)} (c : Fin n → Fin n → ℝ)
    (hsymm : ∀ i j, c i j = c j i) {u v : Fin n} (W : G.Walk u v) :
    walkLen c W = (W.edges.map (edgeCost c)).sum := by
  induction W with
  | nil => simp [walkLen]
  | cons h p ih =>
    rw [walkLen, SimpleGraph.Walk.length_cons, Finset.sum_range_succ', SimpleGraph.Walk.edges_cons,
      List.map_cons, List.sum_cons, ← ih, walkLen]
    simp only [SimpleGraph.Walk.getVert_cons_succ, SimpleGraph.Walk.getVert_zero, edgeCost,
      Sym2.lift_mk]
    rename_i x y z
    rw [hsymm y x]; ring

/-- **Shortcutting.** If `τ` visits the nodes in order of first appearance along a closed walk
through every node, the tour `τ` is no longer than the walk. -/
private lemma shortcut_le {m : ℕ} {G : SimpleGraph (Fin (m + 1))} (c : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hc : IsMetric c) {v : Fin (m + 1)} (W : G.Walk v v) (τ : Equiv.Perm (Fin (m + 1)))
    (hτ : IsShortcut W.support τ) : tourLength c τ ≤ walkLen c W := by
  obtain ⟨hall, hord⟩ := hτ
  set L := W.length with hL
  set g : ℕ → Fin (m + 1) := fun i => W.getVert i with hg
  -- First-appearance positions of the tour nodes along the walk.
  set p : Fin (m + 1) → ℕ := fun k => W.support.idxOf (τ k) with hp
  have hp_le : ∀ k, p k ≤ L := by
    intro k
    show W.support.idxOf (τ k) ≤ W.length
    have := List.idxOf_lt_length_of_mem (hall (τ k))
    rw [SimpleGraph.Walk.length_support] at this
    omega
  have hgp : ∀ k, g (p k) = τ k := by
    intro k
    simp only [hg, hp]
    rw [SimpleGraph.Walk.getVert_eq_support_getElem _ (hp_le k), List.getElem_idxOf]
  -- The tour starts at the start of the walk.
  have hidx0 : W.support.idxOf v = 0 := by
    cases W with
    | nil => simp
    | cons h q => simp [SimpleGraph.Walk.support_cons]
  have hτ0 : τ 0 = v := by
    by_contra hne
    have h1 : τ.symm (τ 0) < τ.symm v := by
      rw [Equiv.symm_apply_apply]
      exact lt_of_le_of_ne (Fin.zero_le _) (fun h => hne (by rw [h, Equiv.apply_symm_apply]))
    have := (hord _ _).mp h1
    rw [hidx0] at this; omega
  have hp0 : p 0 = 0 := by simp only [hp, hτ0, hidx0]
  -- Positions strictly increase along the tour.
  have hpmono : ∀ i : Fin m, p i.castSucc < p i.succ := by
    intro i
    apply (hord _ _).mp
    simp only [Equiv.symm_apply_apply]
    exact Fin.castSucc_lt_succ
  -- The chain of visited positions `p 0, …, p m`, closed off by the walk's end `L`.
  set q : ℕ → ℕ := fun j => if h : j < m + 1 then p ⟨j, h⟩ else L with hq
  have hqmono : ∀ j < m + 1, q j ≤ q (j + 1) := by
    intro j hj
    simp only [hq, dif_pos hj]
    by_cases hj' : j + 1 < m + 1
    · rw [dif_pos hj']
      exact (hpmono ⟨j, by omega⟩).le
    · rw [dif_neg hj']; exact hp_le _
  have hchain := chain_le c hc.refl (fun x y z => hc.triangle x z y) g q (m + 1) hqmono
  have hq0 : q 0 = 0 := by simp [hq, hp0]
  have hqlast : q (m + 1) = L := by simp [hq]
  rw [hq0, hqlast] at hchain
  -- The chain is exactly the tour.
  have htour : tourLength c τ = ∑ j ∈ Finset.range (m + 1), c (g (q j)) (g (q (j + 1))) := by
    rw [tourLength_eq_path, Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range]
    congr 1
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [hq, dif_pos (show (i : ℕ) < m + 1 by omega),
        dif_pos (show (i : ℕ) + 1 < m + 1 by omega), hgp]
      rfl
    · have e1 : q m = p (Fin.last m) := by simp only [hq, dif_pos (show m < m + 1 by omega)]; rfl
      rw [e1, hqlast, hgp, hτ0]
      simp only [hg, hL, SimpleGraph.Walk.getVert_length]
  rw [htour]
  rw [walkLen]
  rw [← Finset.range_eq_Ico] at hchain
  exact hchain

theorem solution {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetric c) (hn : 1 ≤ n)
    (T : SimpleGraph (Fin n)) (hT : IsMST c T) (v : Fin n) (W : T.Walk v v)
    (hW : ∀ e ∈ T.edgeSet, W.edges.count e = 2) (τ : Equiv.Perm (Fin n))
    (hτ : IsShortcut W.support τ) :
    tourLength c τ ≤ 2 * optTourLength c := by
  have hmst := mst_lower_bound c hc hn T hT
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- The doubled-tree walk uses every tree edge exactly twice and nothing else.
  have hwalk : walkLen c W = 2 * graphWeight c T := by
    rw [walkLen_eq_edges c hc.symm, Finset.sum_list_map_count]
    have hset : W.edges.toFinset = T.edgeFinset := by
      ext e
      rw [List.mem_toFinset, SimpleGraph.mem_edgeFinset]
      constructor
      · exact fun h => W.edges_subset_edgeSet h
      · intro h
        have := hW e h
        exact List.count_pos_iff.mp (by omega)
    rw [hset, graphWeight, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e he => ?_)
    rw [hW e (SimpleGraph.mem_edgeFinset.mp he), nsmul_eq_mul]
    norm_num
  have := shortcut_le c hc W τ hτ
  linarith
