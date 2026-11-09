-- Prove2me | solution 1 for TenChallenges.challenge_08_r2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T22:45:08.369206+00:00
-- url     : https://prove2.me/submissions/97562116-31cd-4133-9241-33f703ecf3d5

import Definitions.Def_TenChallenges_Challenge_08
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Tactic.FinCases

namespace Aux_TC08_R2

open Finset

variable {V : Type*} [DecidableEq V] (H : FinHypergraph V)

lemma exists_min_vertex_cover (hunif : H.IsUniform 2) :
    ∃ C : Finset V, H.IsVertexCover C ∧ C.card = H.coverNumber ∧
      ∀ C' : Finset V, H.IsVertexCover C' → C.card ≤ C'.card := by
  have hV_cov : H.IsVertexCover H.vertices := by
    refine ⟨Subset.refl _, fun e he => ?_⟩
    have hcard : e.card = 2 := hunif e he
    have hne : e.Nonempty := card_pos.mp (by omega)
    obtain ⟨v, hv⟩ := hne
    exact ⟨v, H.edges_subset_vertices e he hv, hv⟩
  let S : Set ℕ := {n | ∃ C : Finset V, H.IsVertexCover C ∧ C.card = n}
  have hS_ne : S.Nonempty := ⟨H.vertices.card, H.vertices, hV_cov, rfl⟩
  have hmem : sInf S ∈ S := Nat.sInf_mem hS_ne
  obtain ⟨C, hC_cov, hC_card⟩ := hmem
  refine ⟨C, hC_cov, hC_card, fun C' hC' => ?_⟩
  rw [hC_card]
  exact Nat.sInf_le ⟨C', hC', rfl⟩

lemma pair_eq_of_mem_parts {P0 P1 : Finset V} (hdisj : Disjoint P0 P1)
    {e : Finset V} (hcard : e.card = 2) {u w : V}
    (hu0 : u ∈ P0) (hw1 : w ∈ P1) (hue : u ∈ e) (hwe : w ∈ e) :
    e = {u, w} := by
  have huw : u ≠ w := fun h => disjoint_left.mp hdisj hu0 (h ▸ hw1)
  have hsub : ({u, w} : Finset V) ⊆ e := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hcard_pair : ({u, w} : Finset V).card = 2 := card_pair huw
  exact (eq_of_subset_of_card_le hsub (by omega)).symm

lemma edge_decomp {parts : Fin 2 → Finset V}
    (hdisj : ∀ i j : Fin 2, i ≠ j → Disjoint (parts i) (parts j))
    (hedge_part : ∀ e ∈ H.edges, ∀ i : Fin 2, (parts i ∩ e).card = 1)
    (hunif : H.IsUniform 2) {e : Finset V} (he : e ∈ H.edges) :
    ∃ u ∈ parts 0, ∃ w ∈ parts 1, e = {u, w} := by
  obtain ⟨u, hu⟩ := card_eq_one.mp (hedge_part e he 0)
  obtain ⟨w, hw⟩ := card_eq_one.mp (hedge_part e he 1)
  have hu_mem : u ∈ parts 0 ∩ e := hu ▸ mem_singleton_self u
  have hw_mem : w ∈ parts 1 ∩ e := hw ▸ mem_singleton_self w
  rcases mem_inter.mp hu_mem with ⟨hu0, hue⟩
  rcases mem_inter.mp hw_mem with ⟨hw1, hwe⟩
  refine ⟨u, hu0, w, hw1, ?_⟩
  exact pair_eq_of_mem_parts (hdisj 0 1 (by decide)) (hunif e he) hu0 hw1 hue hwe

lemma pair_not_disjoint_iff {P0 P1 : Finset V} (hdisj : Disjoint P0 P1)
    {a₁ b₁ a₂ b₂ : V} (ha₁ : a₁ ∈ P0) (hb₁ : b₁ ∈ P1) (ha₂ : a₂ ∈ P0) (hb₂ : b₂ ∈ P1) :
    ¬ Disjoint ({a₁, b₁} : Finset V) {a₂, b₂} → a₁ = a₂ ∨ b₁ = b₂ := by
  rw [not_disjoint_iff]
  rintro ⟨v, hv1, hv2⟩
  simp only [mem_insert, mem_singleton] at hv1 hv2
  rcases hv1 with rfl | rfl <;> rcases hv2 with rfl | rfl
  · exact Or.inl rfl
  · exact absurd hb₂ (disjoint_left.mp hdisj ha₁)
  · exact absurd hb₁ (disjoint_left.mp hdisj ha₂)
  · exact Or.inr rfl

end Aux_TC08_R2

open Aux_TC08_R2 Finset TenChallenges in
/-- König's theorem: Ryser's inequality at `r = 2`. -/
theorem solution : statement_08 2 := by
  intro V _ H _ hunif hpart
  classical
  obtain ⟨C, hC_cov, hC_card, hC_min⟩ := exists_min_vertex_cover H hunif
  obtain ⟨parts, hverts, hdisj, hedge_part⟩ := hpart
  let P0 : Finset V := parts 0
  let P1 : Finset V := parts 1
  have hdisj01 : Disjoint P0 P1 := hdisj 0 1 (by decide)
  have hP0_sub : P0 ⊆ H.vertices := fun v hv => (hverts v).mpr ⟨0, hv⟩
  have hP1_sub : P1 ⊆ H.vertices := fun v hv => (hverts v).mpr ⟨1, hv⟩
  have hV_union : ∀ v ∈ H.vertices, v ∈ P0 ∨ v ∈ P1 := by
    intro v hv
    obtain ⟨i, hi⟩ := (hverts v).mp hv
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  let C0 : Finset V := C ∩ P0
  let C1 : Finset V := C ∩ P1
  have hdisj_C01 : Disjoint C0 C1 :=
    disjoint_of_subset_right inter_subset_right (disjoint_of_subset_left inter_subset_right hdisj01)
  have hC_union : C = C0 ∪ C1 := by
    ext v
    simp only [C0, C1, mem_union, mem_inter]
    constructor
    · intro hv
      rcases hV_union v (hC_cov.1 hv) with hv0 | hv1
      · exact Or.inl ⟨hv, hv0⟩
      · exact Or.inr ⟨hv, hv1⟩
    · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
  have hC_card_sum : C.card = C0.card + C1.card := by
    rw [hC_union, card_union_of_disjoint hdisj_C01]
  -- Define bipartite neighborhoods from C0 to P1 \ C1 and from C1 to P0 \ C0
  let edgesFin : Finset (Finset V) :=
    H.vertices.powerset.filter (fun e => e ∈ H.edges)
  have hmem_edgesFin : ∀ e : Finset V, e ∈ edgesFin ↔ e ∈ H.edges := by
    intro e
    simp only [edgesFin, mem_filter, mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨H.edges_subset_vertices e h, h⟩⟩
  let N0 : C0 → Finset V := fun x =>
    (P1 \ C1).filter (fun y => ({x.1, y} : Finset V) ∈ edgesFin)
  have hHall0 : ∀ s : Finset C0, s.card ≤ (s.biUnion N0).card := by
    intro s
    let S : Finset V := s.image Subtype.val
    have hS_sub_C0 : S ⊆ C0 := by
      intro x hx
      obtain ⟨x', _, rfl⟩ := mem_image.mp hx
      exact x'.2
    have hS_sub_C : S ⊆ C := hS_sub_C0.trans inter_subset_left
    have hS_card : S.card = s.card := card_image_of_injective s Subtype.val_injective
    let T : Finset V := s.biUnion N0
    have hT_sub_P1 : T ⊆ P1 \ C1 := by
      intro y hy
      obtain ⟨x, _, hyx⟩ := mem_biUnion.mp hy
      exact (mem_filter.mp hyx).1
    let C' : Finset V := (C \ S) ∪ T
    have hC'_cov : H.IsVertexCover C' := by
      refine ⟨?_, ?_⟩
      · intro v hv
        rcases mem_union.mp hv with hvCS | hvT
        · exact hC_cov.1 (sdiff_subset hvCS)
        · exact hP1_sub (sdiff_subset (hT_sub_P1 hvT))
      · intro e he
        obtain ⟨u, hu0, w, hw1, rfl⟩ := edge_decomp H hdisj hedge_part hunif he
        obtain ⟨v, hvC, hve⟩ := hC_cov.2 {u, w} he
        simp only [mem_insert, mem_singleton] at hve
        by_cases hwC : w ∈ C
        · refine ⟨w, mem_union_left _ (mem_sdiff.mpr ⟨hwC, ?_⟩), by simp⟩
          intro hwS
          have hw0 : w ∈ P0 := (mem_inter.mp (hS_sub_C0 hwS)).2
          exact disjoint_left.mp hdisj01 hw0 hw1
        · have huC : u ∈ C := by
            rcases hve with rfl | rfl
            · exact hvC
            · exact absurd hvC hwC
          by_cases huS : u ∈ S
          · obtain ⟨x, hx_s, hxu⟩ := mem_image.mp huS
            have hw1' : w ∈ P1 \ C1 := mem_sdiff.mpr ⟨hw1, fun hwC1 => hwC (mem_inter.mp hwC1).1⟩
            have hwN0 : w ∈ N0 x := by
              refine mem_filter.mpr ⟨hw1', ?_⟩
              rw [hxu, hmem_edgesFin]
              exact he
            exact ⟨w, mem_union_right _ (mem_biUnion.mpr ⟨x, hx_s, hwN0⟩), by simp⟩
          · exact ⟨u, mem_union_left _ (mem_sdiff.mpr ⟨huC, huS⟩), by simp⟩
    have hmin_le : C.card ≤ C'.card := hC_min C' hC'_cov
    have hCS : (C \ S).card + S.card = C.card := card_sdiff_add_card_eq_card hS_sub_C
    have hC'_le : C'.card ≤ (C \ S).card + T.card := card_union_le _ _
    change s.card ≤ T.card
    omega
  obtain ⟨f0, hf0_inj, hf0_mem⟩ := (all_card_le_biUnion_card_iff_existsInjective' N0).mp hHall0
  -- Symmetrically for C1
  let N1 : C1 → Finset V := fun y =>
    (P0 \ C0).filter (fun x => ({x, y.1} : Finset V) ∈ edgesFin)
  have hHall1 : ∀ s : Finset C1, s.card ≤ (s.biUnion N1).card := by
    intro s
    let S : Finset V := s.image Subtype.val
    have hS_sub_C1 : S ⊆ C1 := by
      intro y hy
      obtain ⟨y', _, rfl⟩ := mem_image.mp hy
      exact y'.2
    have hS_sub_C : S ⊆ C := hS_sub_C1.trans inter_subset_left
    have hS_card : S.card = s.card := card_image_of_injective s Subtype.val_injective
    let T : Finset V := s.biUnion N1
    have hT_sub_P0 : T ⊆ P0 \ C0 := by
      intro x hx
      obtain ⟨y, _, hxy⟩ := mem_biUnion.mp hx
      exact (mem_filter.mp hxy).1
    let C' : Finset V := (C \ S) ∪ T
    have hC'_cov : H.IsVertexCover C' := by
      refine ⟨?_, ?_⟩
      · intro v hv
        rcases mem_union.mp hv with hvCS | hvT
        · exact hC_cov.1 (sdiff_subset hvCS)
        · exact hP0_sub (sdiff_subset (hT_sub_P0 hvT))
      · intro e he
        obtain ⟨u, hu0, w, hw1, rfl⟩ := edge_decomp H hdisj hedge_part hunif he
        obtain ⟨v, hvC, hve⟩ := hC_cov.2 {u, w} he
        simp only [mem_insert, mem_singleton] at hve
        by_cases huC : u ∈ C
        · refine ⟨u, mem_union_left _ (mem_sdiff.mpr ⟨huC, ?_⟩), by simp⟩
          intro huS
          have hu1 : u ∈ P1 := (mem_inter.mp (hS_sub_C1 huS)).2
          exact disjoint_left.mp hdisj01 hu0 hu1
        · have hwC : w ∈ C := by
            rcases hve with rfl | rfl
            · exact absurd hvC huC
            · exact hvC
          by_cases hwS : w ∈ S
          · obtain ⟨y, hy_s, hyw⟩ := mem_image.mp hwS
            have hu0' : u ∈ P0 \ C0 := mem_sdiff.mpr ⟨hu0, fun huC0 => huC (mem_inter.mp huC0).1⟩
            have huN1 : u ∈ N1 y := by
              refine mem_filter.mpr ⟨hu0', ?_⟩
              rw [hyw, hmem_edgesFin]
              exact he
            exact ⟨u, mem_union_right _ (mem_biUnion.mpr ⟨y, hy_s, huN1⟩), by simp⟩
          · exact ⟨w, mem_union_left _ (mem_sdiff.mpr ⟨hwC, hwS⟩), by simp⟩
    have hmin_le : C.card ≤ C'.card := hC_min C' hC'_cov
    have hCS : (C \ S).card + S.card = C.card := card_sdiff_add_card_eq_card hS_sub_C
    have hC'_le : C'.card ≤ (C \ S).card + T.card := card_union_le _ _
    change s.card ≤ T.card
    omega
  obtain ⟨f1, hf1_inj, hf1_mem⟩ := (all_card_le_biUnion_card_iff_existsInjective' N1).mp hHall1
  -- Properties of f0 and f1
  have hf0_P1 : ∀ x : C0, f0 x ∈ P1 ∧ f0 x ∉ C1 ∧ ({x.1, f0 x} : Finset V) ∈ H.edges := by
    intro x
    rcases mem_filter.mp (hf0_mem x) with ⟨h1, h2⟩
    rcases mem_sdiff.mp h1 with ⟨hp1, hnc1⟩
    exact ⟨hp1, hnc1, (hmem_edgesFin _).mp h2⟩
  have hf1_P0 : ∀ y : C1, f1 y ∈ P0 ∧ f1 y ∉ C0 ∧ ({f1 y, y.1} : Finset V) ∈ H.edges := by
    intro y
    rcases mem_filter.mp (hf1_mem y) with ⟨h1, h2⟩
    rcases mem_sdiff.mp h1 with ⟨hp0, hnc0⟩
    exact ⟨hp0, hnc0, (hmem_edgesFin _).mp h2⟩
  let g0 : C0 → Finset V := fun x => {x.1, f0 x}
  let g1 : C1 → Finset V := fun y => {f1 y, y.1}
  have hg0_disj : ∀ x₁ x₂ : C0, ¬ Disjoint (g0 x₁) (g0 x₂) → x₁ = x₂ := by
    intro x₁ x₂ hnd
    have h := pair_not_disjoint_iff hdisj01
      (mem_inter.mp x₁.2).2 (hf0_P1 x₁).1 (mem_inter.mp x₂.2).2 (hf0_P1 x₂).1 hnd
    rcases h with h | h
    · exact Subtype.ext h
    · exact hf0_inj h
  have hg1_disj : ∀ y₁ y₂ : C1, ¬ Disjoint (g1 y₁) (g1 y₂) → y₁ = y₂ := by
    intro y₁ y₂ hnd
    have h := pair_not_disjoint_iff hdisj01
      (hf1_P0 y₁).1 (mem_inter.mp y₁.2).2 (hf1_P0 y₂).1 (mem_inter.mp y₂.2).2 hnd
    rcases h with h | h
    · exact hf1_inj h
    · exact Subtype.ext h
  have hg01_disj : ∀ (x : C0) (y : C1), Disjoint (g0 x) (g1 y) := by
    intro x y
    by_contra hnd
    have h := pair_not_disjoint_iff hdisj01
      (mem_inter.mp x.2).2 (hf0_P1 x).1 (hf1_P0 y).1 (mem_inter.mp y.2).2 hnd
    rcases h with h | h
    · exact (hf1_P0 y).2.1 (h ▸ x.2)
    · exact (hf0_P1 x).2.1 (h ▸ y.2)
  have hg0_inj : Function.Injective g0 := by
    intro x₁ x₂ heq
    apply hg0_disj x₁ x₂
    rw [heq, not_disjoint_iff]
    exact ⟨x₂.1, by simp [g0], by simp [g0]⟩
  have hg1_inj : Function.Injective g1 := by
    intro y₁ y₂ heq
    apply hg1_disj y₁ y₂
    rw [heq, not_disjoint_iff]
    exact ⟨y₂.1, by simp [g1], by simp [g1]⟩
  let M0 : Finset (Finset V) := univ.image g0
  let M1 : Finset (Finset V) := univ.image g1
  let M : Finset (Finset V) := M0 ∪ M1
  have hM01_disj : Disjoint M0 M1 := by
    rw [disjoint_left]
    intro e he0 he1
    obtain ⟨x, _, rfl⟩ := mem_image.mp he0
    obtain ⟨y, _, heq⟩ := mem_image.mp he1
    have hd := hg01_disj x y
    rw [heq] at hd
    exact disjoint_left.mp hd (by simp [g0] : x.1 ∈ g0 x) (by simp [g0] : x.1 ∈ g0 x)
  have hM_card : M.card = C.card := by
    have h0 : M0.card = C0.card := by
      rw [card_image_of_injective _ hg0_inj, card_univ, Fintype.card_coe]
    have h1 : M1.card = C1.card := by
      rw [card_image_of_injective _ hg1_inj, card_univ, Fintype.card_coe]
    rw [card_union_of_disjoint hM01_disj, h0, h1, hC_card_sum]
  have hM_match : H.IsMatching M := by
    refine ⟨?_, ?_⟩
    · intro e he
      rcases mem_union.mp he with he0 | he1
      · obtain ⟨x, _, rfl⟩ := mem_image.mp he0
        exact (hf0_P1 x).2.2
      · obtain ⟨y, _, rfl⟩ := mem_image.mp he1
        exact (hf1_P0 y).2.2
    · intro e₁ he₁ e₂ he₂ hne
      rcases mem_union.mp he₁ with he₁0 | he₁1 <;> rcases mem_union.mp he₂ with he₂0 | he₂1
      · obtain ⟨x₁, _, rfl⟩ := mem_image.mp he₁0
        obtain ⟨x₂, _, rfl⟩ := mem_image.mp he₂0
        by_contra hnd
        exact hne (congrArg g0 (hg0_disj x₁ x₂ hnd))
      · obtain ⟨x₁, _, rfl⟩ := mem_image.mp he₁0
        obtain ⟨y₂, _, rfl⟩ := mem_image.mp he₂1
        exact hg01_disj x₁ y₂
      · obtain ⟨y₁, _, rfl⟩ := mem_image.mp he₁1
        obtain ⟨x₂, _, rfl⟩ := mem_image.mp he₂0
        exact (hg01_disj x₂ y₁).symm
      · obtain ⟨y₁, _, rfl⟩ := mem_image.mp he₁1
        obtain ⟨y₂, _, rfl⟩ := mem_image.mp he₂1
        by_contra hnd
        exact hne (congrArg g1 (hg1_disj y₁ y₂ hnd))
  have hb : BddAbove {n | ∃ M' : Finset (Finset V), H.IsMatching M' ∧ M'.card = n} := by
    refine ⟨H.vertices.powerset.card, ?_⟩
    rintro n ⟨M', hM', rfl⟩
    apply card_le_card
    intro e he
    exact mem_powerset.mpr (H.edges_subset_vertices e (hM'.1 e he))
  have hle_match : M.card ≤ H.matchingNumber := by
    exact le_csSup hb ⟨M, hM_match, rfl⟩
  rw [← hC_card, ← hM_card]
  omega
