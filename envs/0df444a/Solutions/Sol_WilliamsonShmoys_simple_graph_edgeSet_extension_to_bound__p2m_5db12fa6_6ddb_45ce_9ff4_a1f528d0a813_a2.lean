-- Prove2me | solution 1 for WilliamsonShmoys.simple_graph_edgeSet_extension_to_bound__p2m_5db12fa6_6ddb_45ce_9ff4_a1f528d0a813_a2
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T15:05:20.468821+00:00
-- url     : https://prove2.me/submissions/73bf0d63-226c-4f48-b6b9-f2aeb059635d

import Mathlib

set_option autoImplicit false

/-- Any graph whose edge count is below the planar bound can be extended to a graph with exactly
that many edges. -/
theorem solution {V : Type} [Fintype V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hbound : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧ K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  classical
  let n := Fintype.card V
  let t := 3 * n - 6
  let S := {e : Sym2 V // ¬ e.IsDiag}
  have hS_card : Fintype.card S = n.choose 2 := Sym2.card_subtype_not_diag
  let s : Finset S := Finset.univ.filter (fun e : S => (e : Sym2 V) ∈ H.edgeSet)
  have hs_card : s.card = H.edgeSet.ncard := by
    have hinj : Function.Injective (fun e : S => (e : Sym2 V)) := Subtype.val_injective
    have himage : s.image (fun e : S => (e : Sym2 V)) = H.edgeSet.toFinset := by
      ext e
      constructor
      · intro he
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
        exact Set.mem_toFinset.mpr (Finset.mem_filter.mp hx).2
      · intro he
        have he' : e ∈ H.edgeSet := Set.mem_toFinset.mp he
        refine Finset.mem_image.mpr ⟨⟨e, H.not_isDiag_of_mem_edgeSet he'⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he'⟩
    rw [← Finset.card_image_of_injective s hinj, himage,
      ← Set.ncard_eq_toFinset_card']
  have hs_le : s.card ≤ t := by
    rw [hs_card]
    exact hbound
  have hchoose_succ : ∀ k : Nat, (k + 1).choose 2 = k.choose 2 + k := by
    intro k
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    change k + k.choose 2 = k.choose 2 + k
    omega
  have hineq : ∀ k : Nat, 3 ≤ k → 3 * k - 6 ≤ k.choose 2 := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      rw [hchoose_succ]
      omega
  have ht_le : t ≤ Fintype.card S := by
    rw [hS_card]
    exact hineq n hV
  obtain ⟨T, hsT, hTcard⟩ := Finset.exists_superset_card_eq (s := s) (n := t) hs_le ht_le
  let U : Set (Sym2 V) := ↑(T.image (fun e : S => (e : Sym2 V)))
  let K : SimpleGraph V := SimpleGraph.fromEdgeSet U
  refine ⟨K, ?_, ?_⟩
  · intro e he
    have hnon : ¬ e.IsDiag := H.not_isDiag_of_mem_edgeSet he
    let x : S := ⟨e, hnon⟩
    have hx_s : x ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
    have hx_T : x ∈ T := hsT hx_s
    have heU : e ∈ U := Finset.mem_image_of_mem (fun e : S => (e : Sym2 V)) hx_T
    change e ∈ K.edgeSet
    change e ∈ (SimpleGraph.fromEdgeSet U).edgeSet
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨heU, by simpa using hnon⟩
  · show K.edgeSet.ncard = t
    have hdiag : Disjoint U Sym2.diagSet := by
      rw [Set.disjoint_left]
      intro e he
      change e ∈ T.image (fun e : S => (e : Sym2 V)) at he
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp he
      simpa using x.2
    have hKU : K.edgeSet = U := by
      rw [SimpleGraph.edgeSet_fromEdgeSet, sdiff_eq_left.mpr hdiag]
    rw [hKU]
    dsimp only [U]
    rw [Set.ncard_coe_finset, Finset.card_image_of_injective T Subtype.val_injective]
    exact hTcard
