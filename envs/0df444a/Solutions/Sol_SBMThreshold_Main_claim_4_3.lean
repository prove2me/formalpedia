-- Prove2me | solution 1 for SBMThreshold.Main.claim_4_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:33:35.834248+00:00
-- url     : https://prove2.me/submissions/2021ef9d-1658-4d41-8f58-495c03cb188b

import Mathlib
import Definitions.Def_SBMThreshold_Main_Setting
import Definitions.Def_SBMThreshold_Main_Paths
set_option autoImplicit false
open Filter Topology Finset
open scoped Classical
open SBMThreshold.Main

lemma sbm_new_no_edge {n k : ℕ} (γ : Fin (k + 1) → Fin n) (i : Fin k) (hi : IsNewStep γ i) :
    ∀ j : Fin k, j < i → stepEdge γ j ≠ stepEdge γ i := by
  intro j hj he
  have h1 := hi j.castSucc (by rw [Fin.le_def]; simp; exact hj.le)
  have h2 := hi j.succ (by rw [Fin.le_def]; simp; exact hj)
  unfold stepEdge at he
  rw [Sym2.eq_iff] at he
  rcases he with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact h2 e2
  · exact h1 e1

lemma sbm_vertices {n k : ℕ} (γ : Fin (k + 1) → Fin n) :
    pathVertices γ = insert (γ 0) ((univ.filter (IsNewStep γ)).image (fun i => γ i.succ)) := by
  ext v
  simp only [pathVertices, mem_image, mem_univ, true_and, mem_insert, mem_filter]
  constructor
  · rintro ⟨j, rfl⟩
    have key : ∀ m : ℕ, ∀ j : Fin (k + 1), j.val = m →
        γ j = γ 0 ∨ ∃ i : Fin k, IsNewStep γ i ∧ γ i.succ = γ j := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro j hjm
        by_cases h : ∃ j' : Fin (k + 1), j' < j ∧ γ j' = γ j
        · obtain ⟨j', hj'lt, hj'eq⟩ := h
          have := ih j'.val (by rw [← hjm]; exact hj'lt) j' rfl
          rcases this with h0 | ⟨i, hi, hie⟩
          · left; rw [← hj'eq]; exact h0
          · right; exact ⟨i, hi, hie.trans hj'eq⟩
        · push Not at h
          by_cases hj0 : j = 0
          · left; rw [hj0]
          · right
            have hjpos : 0 < j.val := by
              rcases Nat.eq_zero_or_pos j.val with h0 | h0
              · exact absurd (Fin.ext h0) hj0
              · exact h0
            have hjk : j.val - 1 < k := by have := j.isLt; omega
            refine ⟨⟨j.val - 1, hjk⟩, ?_, ?_⟩
            · intro j'' hj''
              have : j'' < j := by
                rw [Fin.lt_def]; rw [Fin.le_def] at hj''; simp at hj''; omega
              have hs : (⟨j.val - 1, hjk⟩ : Fin k).succ = j := by
                ext; simp; omega
              rw [hs]
              exact h j'' this
            · congr 1; ext; simp; omega
    exact key _ j rfl
  · rintro (h | ⟨i, _, hi⟩)
    · exact ⟨0, h.symm⟩
    · exact ⟨i.succ, hi⟩

lemma sbm_edges {n k : ℕ} (γ : Fin (k + 1) → Fin n) :
    pathEdges γ = (univ.filter (fun i : Fin k => ∀ j, j < i → stepEdge γ j ≠ stepEdge γ i)).image
      (stepEdge γ) := by
  ext e
  simp only [pathEdges, mem_image, mem_univ, true_and, mem_filter]
  constructor
  · rintro ⟨i, rfl⟩
    have key : ∀ m : ℕ, ∀ i : Fin k, i.val = m →
        ∃ i' : Fin k, (∀ j, j < i' → stepEdge γ j ≠ stepEdge γ i') ∧ stepEdge γ i' = stepEdge γ i := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro i hi
        by_cases h : ∃ j : Fin k, j < i ∧ stepEdge γ j = stepEdge γ i
        · obtain ⟨j, hjlt, hje⟩ := h
          obtain ⟨i', h1, h2⟩ := ih j.val (by rw [← hi]; exact hjlt) j rfl
          exact ⟨i', h1, h2.trans hje⟩
        · push Not at h
          exact ⟨i, h, rfl⟩
    exact key _ i rfl
  · rintro ⟨i, _, rfl⟩
    exact ⟨i, rfl⟩

theorem solution {n k : ℕ} (γ : Fin (k + 1) → Fin n) (hγ : IsPath γ) :
    (pathVertices γ).card = kNew γ + 1 ∧ (pathEdges γ).card = kNew γ + kRet γ := by
  constructor
  · rw [sbm_vertices, card_insert_of_notMem, card_image_of_injOn]
    · rfl
    · intro i hi i' hi' hii
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hi hi'
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact hi' i.succ (by rw [Fin.le_def]; simp; exact hlt) hii
      · exact hi i'.succ (by rw [Fin.le_def]; simp; exact hlt) hii.symm
    · simp only [mem_image, mem_filter, mem_univ, true_and, not_exists, not_and]
      intro i hi h0
      exact hi 0 (Fin.zero_le _) h0.symm
  · rw [sbm_edges, card_image_of_injOn]
    · unfold kNew kRet
      rw [← card_union_of_disjoint]
      · congr 1
        ext i
        simp only [mem_filter, mem_univ, true_and, mem_union]
        constructor
        · intro h
          by_cases hn : IsNewStep γ i
          · left; exact hn
          · right
            refine ⟨hn, ?_⟩
            rintro ⟨_, j, hj, hje⟩
            exact h j hj hje
        · rintro (hn | ⟨hn, hno⟩)
          · exact sbm_new_no_edge γ i hn
          · intro j hj hje
            exact hno ⟨hn, j, hj, hje⟩
      · rw [disjoint_left]
        intro i hi hi'
        simp only [mem_filter, mem_univ, true_and] at hi hi'
        exact hi'.1 hi
    · intro i hi i' hi' hii
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hi hi'
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact hi' i hlt hii
      · exact hi i' hlt hii.symm
