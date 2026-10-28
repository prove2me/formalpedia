-- Prove2me | solution 1 for PathsTreesFlowers.Invariance.max_matching_erase_6_6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T09:49:35.624006+00:00
-- url     : https://prove2.me/submissions/688bcf67-657c-46f2-a8ef-a46b6c935459

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Sym2
import Mathlib.Order.Partition.Finpartition
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Invariance_Basic
import Definitions.Def_PathsTreesFlowers_Invariance_Shrink
import Definitions.Def_PathsTreesFlowers_Invariance_Config
import Theorems.Thm_PathsTreesFlowers_Invariance_lemma_4_2
import Theorems.Thm_PathsTreesFlowers_Invariance_outer_adjacent_6_4

namespace SolPathsTreesFlowersMaxMatchingErase66

set_option linter.unusedSectionVars false

open EdmondsMatching65.Polyhedron (IsMatching)
open PathsTreesFlowers.Invariance

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ### Part 1: Double counting and `IsBlossomSet` internal matching bound -/

lemma sum_card_filter_ends (G : EdmondsMatching65.Polyhedron.Graph V E) (S : Finset V) (F : Finset E) :
    ∑ v ∈ S, (F.filter (fun e => v ∈ G.ends e)).card =
      ∑ e ∈ F, (S.filter (fun v => v ∈ G.ends e)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

lemma card_filter_ends_eq_two_of_mem_sym2 {G : EdmondsMatching65.Polyhedron.Graph V E}
    {S : Finset V} {e : E} (he : G.ends e ∈ S.sym2) :
    (S.filter (fun v => v ∈ G.ends e)).card = 2 := by
  rcases Sym2.exists.mp ⟨G.ends e, rfl⟩ with ⟨a, b, hab⟩
  have hne : a ≠ b := by
    rintro rfl
    exact G.loopless e (hab ▸ Sym2.mk_isDiag_iff.mpr rfl)
  rw [hab, Finset.mk_mem_sym2_iff] at he
  have hfilt : S.filter (fun v => v ∈ G.ends e) = {a, b} := by
    ext v
    simp only [Finset.mem_filter, hab, Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun h => h.2, fun h => ⟨by rcases h with rfl | rfl; exacts [he.1, he.2], h⟩⟩
  rw [hfilt, Finset.card_pair hne]

lemma card_filter_matching_le_one {G : EdmondsMatching65.Polyhedron.Graph V E}
    {N : Finset E} (hN : IsMatching G N) (v : V) :
    (N.filter (fun e => v ∈ G.ends e)).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun e₁ he₁ e₂ he₂ => ?_
  simp only [Finset.mem_filter] at he₁ he₂
  by_contra hne
  exact hN e₁ he₁.1 e₂ he₂.1 hne v he₁.2 he₂.2

lemma two_mul_card_filter_sym2_le {G : EdmondsMatching65.Polyhedron.Graph V E}
    {N : Finset E} (hN : IsMatching G N) (S : Finset V) :
    2 * (N.filter (fun e => G.ends e ∈ S.sym2)).card ≤ S.card := by
  set NS := N.filter (fun e => G.ends e ∈ S.sym2)
  have hNS : IsMatching G NS := fun e he f hf =>
    hN e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1
  have hsum_e : ∑ e ∈ NS, (S.filter (fun v => v ∈ G.ends e)).card = 2 * NS.card := by
    calc ∑ e ∈ NS, (S.filter (fun v => v ∈ G.ends e)).card
        = ∑ _e ∈ NS, 2 := Finset.sum_congr rfl fun e he =>
          card_filter_ends_eq_two_of_mem_sym2 (Finset.mem_filter.mp he).2
      _ = 2 * NS.card := by simp [Nat.mul_comm]
  have hsum_v : ∑ v ∈ S, (NS.filter (fun e => v ∈ G.ends e)).card ≤ S.card := by
    calc ∑ v ∈ S, (NS.filter (fun e => v ∈ G.ends e)).card
        ≤ ∑ _v ∈ S, 1 := Finset.sum_le_sum fun v _ => card_filter_matching_le_one hNS v
      _ = S.card := by simp
  linarith [sum_card_filter_ends G S NS]

lemma blossomSet_card_le_two_mul_add_one {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} {U : Finset V} (hU : PathsTreesFlowers.Duality.IsBlossomSet G M U) :
    U.card ≤ 2 * (M.filter (fun e => G.ends e ∈ U.sym2)).card + 1 := by
  induction hU with
  | single v => simp
  | circuit k Uf ef hk _hUf hdisj hef hMf ih =>
    set W := (Finset.range (2 * k + 1)).biUnion Uf
    have hW_card : W.card ≤ ∑ i ∈ Finset.range (2 * k + 1), (Uf i).card := Finset.card_biUnion_le
    have hsum_ih : ∑ i ∈ Finset.range (2 * k + 1), (Uf i).card ≤
        ∑ i ∈ Finset.range (2 * k + 1), (2 * (M.filter (fun e => G.ends e ∈ (Uf i).sym2)).card + 1) :=
      Finset.sum_le_sum fun i hi => ih i (Finset.mem_range.mp hi)
    have hsum_rw : ∑ i ∈ Finset.range (2 * k + 1), (2 * (M.filter (fun e => G.ends e ∈ (Uf i).sym2)).card + 1) =
        (∑ i ∈ Finset.range (2 * k + 1), (M.filter (fun e => G.ends e ∈ (Uf i).sym2)).card) +
          (∑ i ∈ Finset.range (2 * k + 1), (M.filter (fun e => G.ends e ∈ (Uf i).sym2)).card) + (2 * k + 1) := by
      simp_rw [Nat.two_mul, Finset.sum_add_distrib]
      simp
    set A := (Finset.range (2 * k + 1)).biUnion (fun i => M.filter (fun e => G.ends e ∈ (Uf i).sym2))
    set B := (Finset.range k).image (fun j => ef (2 * j + 1))
    have hA_card : A.card = ∑ i ∈ Finset.range (2 * k + 1), (M.filter (fun e => G.ends e ∈ (Uf i).sym2)).card := by
      refine Finset.card_biUnion fun i hi j hj hij => ?_
      rw [Function.onFun, Finset.disjoint_left]
      intro e hei hej
      rcases Sym2.exists.mp ⟨G.ends e, rfl⟩ with ⟨a, b, hab⟩
      have hai : a ∈ Uf i := by
        have := (Finset.mem_filter.mp hei).2
        rw [hab, Finset.mk_mem_sym2_iff] at this
        exact this.1
      have haj : a ∈ Uf j := by
        have := (Finset.mem_filter.mp hej).2
        rw [hab, Finset.mk_mem_sym2_iff] at this
        exact this.1
      exact Finset.disjoint_left.mp (hdisj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hij) hai haj
    have hB_card : B.card = k := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro j₁ hj₁ j₂ hj₂ heq
      have hj₁_lt : j₁ < k := Finset.mem_range.mp hj₁
      have hj₂_lt : j₂ < k := Finset.mem_range.mp hj₂
      by_contra hne
      obtain ⟨a₁, ha₁, b₁, hb₁, hends₁⟩ := hef (2 * j₁ + 1) (by omega)
      obtain ⟨a₂, ha₂, b₂, hb₂, hends₂⟩ := hef (2 * j₂ + 1) (by omega)
      have h_eq_ends : s(a₁, b₁) = s(a₂, b₂) := hends₁.symm.trans ((congrArg G.ends heq).trans hends₂)
      have ha₁_mem : a₁ ∈ (s(a₂, b₂) : Sym2 V) := h_eq_ends ▸ Sym2.mem_mk_left a₁ b₁
      rw [Sym2.mem_iff] at ha₁_mem
      have hmod₂ : (2 * j₂ + 1 + 1) % (2 * k + 1) = (2 * j₂ + 2) % (2 * k + 1) := rfl
      rcases ha₁_mem with rfl | rfl
      · exact Finset.disjoint_left.mp
          (hdisj (2 * j₁ + 1) (by omega) (2 * j₂ + 1) (by omega) (by omega)) ha₁ ha₂
      · have hne_idx : 2 * j₁ + 1 ≠ (2 * j₂ + 1 + 1) % (2 * k + 1) := by
          by_cases hlt : 2 * j₂ + 2 < 2 * k + 1
          · rw [show 2 * j₂ + 1 + 1 = 2 * j₂ + 2 by omega, Nat.mod_eq_of_lt hlt]; omega
          · have heq_k : 2 * j₂ + 1 + 1 = 2 * k + 1 := by omega
            rw [heq_k, Nat.mod_self]; omega
        exact Finset.disjoint_left.mp
          (hdisj (2 * j₁ + 1) (by omega) ((2 * j₂ + 1 + 1) % (2 * k + 1)) (Nat.mod_lt _ (by omega)) hne_idx)
          ha₁ hb₂
    have hAB_disj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro e heA heB
      rcases Finset.mem_biUnion.mp heA with ⟨i, hi, hei⟩
      rcases Finset.mem_image.mp heB with ⟨j, hj, rfl⟩
      have hi_lt : i < 2 * k + 1 := Finset.mem_range.mp hi
      have hj_lt : j < k := Finset.mem_range.mp hj
      obtain ⟨a, ha, b, hb, hends⟩ := hef (2 * j + 1) (by omega)
      have he_Ui := (Finset.mem_filter.mp hei).2
      rw [hends, Finset.mk_mem_sym2_iff] at he_Ui
      have hi_eq₁ : i = 2 * j + 1 := by
        by_contra hne
        exact Finset.disjoint_left.mp (hdisj i hi_lt (2 * j + 1) (by omega) hne) he_Ui.1 ha
      have hi_eq₂ : i = (2 * j + 1 + 1) % (2 * k + 1) := by
        by_contra hne
        exact Finset.disjoint_left.mp
          (hdisj i hi_lt ((2 * j + 1 + 1) % (2 * k + 1)) (Nat.mod_lt _ (by omega)) hne) he_Ui.2 hb
      by_cases hlt : 2 * j + 2 < 2 * k + 1
      · rw [show 2 * j + 1 + 1 = 2 * j + 2 by omega, Nat.mod_eq_of_lt hlt] at hi_eq₂
        omega
      · have heq_k : 2 * j + 1 + 1 = 2 * k + 1 := by omega
        rw [heq_k, Nat.mod_self] at hi_eq₂
        omega
    have hAB_sub : A ∪ B ⊆ M.filter (fun e => G.ends e ∈ W.sym2) := by
      intro e he
      rcases Finset.mem_union.mp he with heA | heB
      · rcases Finset.mem_biUnion.mp heA with ⟨i, hi, hei⟩
        have hei' := Finset.mem_filter.mp hei
        refine Finset.mem_filter.mpr ⟨hei'.1, ?_⟩
        rw [Finset.mem_sym2_iff] at hei' ⊢
        intro x hx
        exact Finset.mem_biUnion.mpr ⟨i, hi, hei'.2 x hx⟩
      · rcases Finset.mem_image.mp heB with ⟨j, hj, rfl⟩
        have hj_lt : j < k := Finset.mem_range.mp hj
        have heM : ef (2 * j + 1) ∈ M := (hMf (2 * j + 1) (by omega)).mpr ⟨j, rfl⟩
        obtain ⟨a, ha, b, hb, hends⟩ := hef (2 * j + 1) (by omega)
        refine Finset.mem_filter.mpr ⟨heM, ?_⟩
        rw [hends, Finset.mk_mem_sym2_iff]
        exact ⟨Finset.mem_biUnion.mpr ⟨2 * j + 1, Finset.mem_range.mpr (by omega), ha⟩,
          Finset.mem_biUnion.mpr ⟨(2 * j + 1 + 1) % (2 * k + 1),
            Finset.mem_range.mpr (Nat.mod_lt _ (by omega)), hb⟩⟩
    have hcard_le : A.card + B.card ≤ (M.filter (fun e => G.ends e ∈ W.sym2)).card := by
      rw [← Finset.card_union_of_disjoint hAB_disj]
      exact Finset.card_le_card hAB_sub
    omega

lemma card_filter_sym2_le_of_blossomSet {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} {U : Finset V} (hU : PathsTreesFlowers.Duality.IsBlossomSet G M U)
    {N : Finset E} (hN : IsMatching G N) :
    (N.filter (fun e => G.ends e ∈ U.sym2)).card ≤ (M.filter (fun e => G.ends e ∈ U.sym2)).card := by
  have h1 := two_mul_card_filter_sym2_le hN U
  have h2 := blossomSet_card_le_two_mul_add_one hU
  omega

/-! ### Part 2: Partition & vertex classification for `Config60 G M` -/

lemma not_mem_outer_of_mem_inner {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (C : Config60 G M) {v : V} {i j : Fin C.n}
    (hi : partOf C.P v ∈ (C.J i).inner) (hj : partOf C.P v ∈ (C.J j).outer) : False := by
  by_cases hij : i = j
  · subst hij
    exact Finset.disjoint_left.mp (C.J i).disjoint_inner_outer hi hj
  · have hvi : partOf C.P v ∈ (C.J i).verts := by
      rw [(C.J i).verts_eq]; exact Finset.mem_union_left _ hi
    have hvj : partOf C.P v ∈ (C.J j).verts := by
      rw [(C.J j).verts_eq]; exact Finset.mem_union_right _ hj
    exact Finset.disjoint_left.mp (C.disjoint i j hij) hvi hvj

lemma disjoint_outerSet_innerSet {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (C : Config60 G M) {v : V} (ho : v ∈ outerSet C) (hi : v ∈ innerSet C) :
    False := by
  rcases hi with ⟨i, hi⟩
  rcases ho with ⟨_, j, hj⟩ | hcard
  · exact not_mem_outer_of_mem_inner C hi hj
  · obtain ⟨j, hj⟩ := C.pseudo_outer (C.P.part v) (C.P.part_mem.2 (Finset.mem_univ v)) hcard
    exact not_mem_outer_of_mem_inner C hi hj

lemma outerSet_congr {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (C : Config60 G M) {u v : V} (h : C.P.part v = C.P.part u)
    (hu : u ∈ outerSet C) : v ∈ outerSet C := by
  have hpart : partOf C.P v = partOf C.P u := Subtype.ext h
  rcases hu with ⟨hcard, i, hi⟩ | hcard
  · exact Or.inl ⟨h ▸ hcard, i, hpart ▸ hi⟩
  · exact Or.inr (h ▸ hcard)

lemma part_card_eq_one_of_not_mem_outerSet {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (C : Config60 G M) {v : V} (hv : v ∉ outerSet C) :
    (C.P.part v).card = 1 := by
  have hpos : 0 < (C.P.part v).card := Finset.card_pos.mpr ⟨v, C.P.mem_part (Finset.mem_univ v)⟩
  have hle : (C.P.part v).card ≤ 1 := by
    by_contra hgt
    exact hv (Or.inr (by omega))
  omega

lemma eq_of_part_eq_of_not_mem_outerSet {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (C : Config60 G M) {u v : V} (hv : v ∉ outerSet C)
    (h : C.P.part u = C.P.part v) : u = v := by
  have hcard := part_card_eq_one_of_not_mem_outerSet C hv
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
  have hvx : v = x := Finset.mem_singleton.mp (hx ▸ C.P.mem_part (Finset.mem_univ v))
  have hux : u = x := Finset.mem_singleton.mp (hx ▸ h ▸ C.P.mem_part (Finset.mem_univ u))
  exact hux.trans hvx.symm

lemma eq_of_partOf_eq_of_not_mem_outerSet {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (C : Config60 G M) {u v : V} (hv : v ∉ outerSet C)
    (h : partOf C.P u = partOf C.P v) : u = v :=
  eq_of_part_eq_of_not_mem_outerSet C hv (congrArg Subtype.val h)

lemma mem_outerSet_of_mem_tree_outer {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (C : Config60 G M) {v : V} {i : Fin C.n}
    (hv : partOf C.P v ∈ (C.J i).outer) : v ∈ outerSet C := by
  have hpos : 0 < (C.P.part v).card := Finset.card_pos.mpr ⟨v, C.P.mem_part (Finset.mem_univ v)⟩
  by_cases h1 : (C.P.part v).card = 1
  · exact Or.inl ⟨h1, i, hv⟩
  · exact Or.inr (by omega)

/-! ### Part 3: Matching of `innerSet C` and neutral vertices in `M` -/

lemma exists_M_edge_to_outer_of_mem_innerSet {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (C : Config60 G M) {w : V} (hw : w ∈ innerSet C) :
    ∃ e ∈ M, ∃ b ∈ outerSet C, G.ends e = s(w, b) := by
  have hw_not_out : w ∉ outerSet C := fun ho => disjoint_outerSet_innerSet C ho hw
  rcases hw with ⟨i, hwi⟩
  obtain ⟨r, hpl⟩ := C.planted i
  obtain ⟨v_out, hv_out, hexp_iff⟩ := (lemma_4_2 (shrink G C.P) (C.J i)).2.2
    (shrinkMatching G C.P M ∩ (C.J i).edges) hpl.max_in
  have hw_verts : partOf C.P w ∈ (C.J i).verts := by
    rw [(C.J i).verts_eq]; exact Finset.mem_union_left _ hwi
  have hw_ne_v : partOf C.P w ≠ v_out := fun h =>
    Finset.disjoint_left.mp (C.J i).disjoint_inner_outer hwi (h ▸ hv_out)
  have hnot_exp : ¬ PathsTreesFlowers.Duality.IsExposed (shrink G C.P)
      (shrinkMatching G C.P M ∩ (C.J i).edges) (partOf C.P w) :=
    fun hexp => hw_ne_v ((hexp_iff (partOf C.P w) hw_verts).mp hexp)
  simp only [PathsTreesFlowers.Duality.IsExposed, not_forall, not_not] at hnot_exp
  rcases hnot_exp with ⟨e_sh, he_sh, hwe_sh⟩
  have he_M : e_sh.1 ∈ M := Finset.mem_subtype.mp (Finset.mem_inter.mp he_sh).1
  have he_J : e_sh ∈ (C.J i).edges := (Finset.mem_inter.mp he_sh).2
  obtain ⟨u_in, hu_in, o_out, ho_out, hends_sh⟩ := (C.J i).edge_inner_outer e_sh he_J
  have hw_eq_u : partOf C.P w = u_in := by
    rw [hends_sh, Sym2.mem_iff] at hwe_sh
    rcases hwe_sh with rfl | h_eq
    · rfl
    · exact False.elim (Finset.disjoint_left.mp (C.J i).disjoint_inner_outer hwi (h_eq ▸ ho_out))
  subst hw_eq_u
  rcases Sym2.exists.mp ⟨G.ends e_sh.1, rfl⟩ with ⟨a, b, hab⟩
  have hmap_ends : (shrink G C.P).ends e_sh = s(partOf C.P a, partOf C.P b) := by
    change (G.ends e_sh.1).map (partOf C.P) = _
    rw [hab, Sym2.map_mk]
  have hpair_eq : s(partOf C.P a, partOf C.P b) = s(partOf C.P w, o_out) :=
    hmap_ends.symm.trans hends_sh
  rw [Sym2.eq_iff] at hpair_eq
  rcases hpair_eq with ⟨ha_w, hb_o⟩ | ⟨ha_o, hb_w⟩
  · have haw : a = w := eq_of_partOf_eq_of_not_mem_outerSet C hw_not_out ha_w
    have hb_out : b ∈ outerSet C := mem_outerSet_of_mem_tree_outer C (hb_o ▸ ho_out)
    exact ⟨e_sh.1, he_M, b, hb_out, haw ▸ hab⟩
  · have hbw : b = w := eq_of_partOf_eq_of_not_mem_outerSet C hw_not_out hb_w
    have ha_out : a ∈ outerSet C := mem_outerSet_of_mem_tree_outer C (ha_o ▸ ho_out)
    exact ⟨e_sh.1, he_M, a, ha_out, (hbw ▸ hab).trans Sym2.eq_swap⟩

lemma other_end_mem_outerSet_of_mem_M_of_mem_innerSet {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (C : Config60 G M) {e : E} (heM : e ∈ M) {w u : V}
    (hw : w ∈ innerSet C) (hends : G.ends e = s(w, u)) : u ∈ outerSet C := by
  obtain ⟨f, hfM, b, hb_out, hends_f⟩ := exists_M_edge_to_outer_of_mem_innerSet C hw
  have hwf : w ∈ G.ends f := by rw [hends_f]; simp
  have hwe : w ∈ G.ends e := by rw [hends]; simp
  have hef : e = f := by
    by_contra hne
    exact C.hM.1 e heM f hfM hne w hwe hwf
  subst hef
  have heq : s(w, u) = s(w, b) := hends.symm.trans hends_f
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨_, rfl⟩ | ⟨rfl, _⟩
  · exact hb_out
  · exact False.elim (disjoint_outerSet_innerSet C hb_out hw)

lemma exists_M_edge_to_R_of_not_mem_outer_inner {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (C : Config60 G M) {w : V} (hwo : w ∉ outerSet C) (hwi : w ∉ innerSet C) :
    ∃ e ∈ M, ∃ u : V, u ∉ outerSet C ∧ u ∉ innerSet C ∧ G.ends e = s(w, u) := by
  have hnot_verts : ∀ i : Fin C.n, partOf C.P w ∉ (C.J i).verts := by
    intro i hmem
    rw [(C.J i).verts_eq] at hmem
    rcases Finset.mem_union.mp hmem with hin | hout
    · exact hwi ⟨i, hin⟩
    · exact hwo (mem_outerSet_of_mem_tree_outer C hout)
  have hnot_exp : ¬ PathsTreesFlowers.Duality.IsExposed (shrink G C.P)
      (shrinkMatching G C.P M) (partOf C.P w) := by
    intro hexp
    obtain ⟨i, hi⟩ := C.dense (partOf C.P w) hexp
    exact hnot_verts i hi
  simp only [PathsTreesFlowers.Duality.IsExposed, not_forall, not_not] at hnot_exp
  rcases hnot_exp with ⟨e_sh, he_sh, hwe_sh⟩
  have heM : e_sh.1 ∈ M := Finset.mem_subtype.mp he_sh
  rcases Sym2.exists.mp ⟨G.ends e_sh.1, rfl⟩ with ⟨a, b, hab⟩
  change partOf C.P w ∈ (G.ends e_sh.1).map (partOf C.P) at hwe_sh
  rw [hab, Sym2.map_mk, Sym2.mem_iff] at hwe_sh
  have h_case : ∃ u : V, G.ends e_sh.1 = s(w, u) := by
    rcases hwe_sh with hw_a | hw_b
    · have haw : a = w := eq_of_partOf_eq_of_not_mem_outerSet C hwo hw_a.symm
      exact ⟨b, haw ▸ hab⟩
    · have hbw : b = w := eq_of_partOf_eq_of_not_mem_outerSet C hwo hw_b.symm
      exact ⟨a, (hbw ▸ hab).trans Sym2.eq_swap⟩
  rcases h_case with ⟨u, hends⟩
  have hu_not_out : u ∉ outerSet C := by
    intro huo
    rcases (outer_adjacent_6_4 G M C).1 u huo e_sh.1 w (hends.trans Sym2.eq_swap) with hwi' | hpart
    · exact hwi hwi'
    · exact hwo (outerSet_congr C hpart huo)
  have hu_not_in : u ∉ innerSet C := by
    intro hui
    exact hwo (other_end_mem_outerSet_of_mem_M_of_mem_innerSet C heM hui (hends.trans Sym2.eq_swap))
  exact ⟨e_sh.1, heM, u, hu_not_out, hu_not_in, hends⟩

/-! ### Part 4: 3-way edge partition `(E_O, E_I, E_R)` and cardinality comparison -/

noncomputable def ISet {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}
    (C : Config60 G M) : Finset V :=
  haveI : DecidablePred (fun x => x ∈ innerSet C) := Classical.decPred _
  Finset.univ.filter (fun x => x ∈ innerSet C)

noncomputable def RSet {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}
    (C : Config60 G M) : Finset V :=
  haveI : DecidablePred (fun x => x ∉ outerSet C ∧ x ∉ innerSet C) := Classical.decPred _
  Finset.univ.filter (fun x => x ∉ outerSet C ∧ x ∉ innerSet C)

noncomputable def EO {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}
    (C : Config60 G M) (N : Finset E) : Finset E :=
  C.P.parts.biUnion (fun U => N.filter (fun e => G.ends e ∈ U.sym2))

noncomputable def EI {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}
    (C : Config60 G M) (N : Finset E) : Finset E :=
  N.filter (fun e => ∃ w ∈ ISet C, w ∈ G.ends e)

noncomputable def ER {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}
    (C : Config60 G M) (N : Finset E) : Finset E :=
  N.filter (fun e => G.ends e ∈ (RSet C).sym2)

lemma mem_ISet_iff {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}
    (C : Config60 G M) {x : V} : x ∈ ISet C ↔ x ∈ innerSet C := by
  simp [ISet]

lemma mem_RSet_iff {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}
    (C : Config60 G M) {x : V} : x ∈ RSet C ↔ x ∉ outerSet C ∧ x ∉ innerSet C := by
  simp [RSet]

lemma mem_outerSet_of_mem_EO {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}
    (C : Config60 G M) {N : Finset E} {e : E} (he : e ∈ EO C N) {x : V} (hx : x ∈ G.ends e) :
    x ∈ outerSet C := by
  rcases Finset.mem_biUnion.mp he with ⟨U, hU, heU⟩
  rcases Sym2.exists.mp ⟨G.ends e, rfl⟩ with ⟨a, b, hab⟩
  have hne : a ≠ b := by
    rintro rfl
    exact G.loopless e (hab ▸ Sym2.mk_isDiag_iff.mpr rfl)
  have hab_U := (Finset.mem_filter.mp heU).2
  rw [hab, Finset.mk_mem_sym2_iff] at hab_U
  have hxU : x ∈ U := by
    rw [hab, Sym2.mem_iff] at hx
    rcases hx with rfl | rfl <;> [exact hab_U.1; exact hab_U.2]
  have hpart : C.P.part x = U := C.P.part_eq_of_mem hU hxU
  have hcard : 1 < (C.P.part x).card := by
    rw [hpart]
    exact Finset.one_lt_card.mpr ⟨a, hab_U.1, b, hab_U.2, hne⟩
  exact Or.inr hcard

lemma card_partition_EO_EI_ER {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}
    (C : Config60 G M) (N : Finset E) :
    N.card = (EO C N).card + (EI C N).card + (ER C N).card := by
  have hdisj_OI : Disjoint (EO C N) (EI C N) := by
    rw [Finset.disjoint_left]
    intro e heO heI
    rcases (Finset.mem_filter.mp heI).2 with ⟨w, hwI, hwe⟩
    exact disjoint_outerSet_innerSet C (mem_outerSet_of_mem_EO C heO hwe) ((mem_ISet_iff C).mp hwI)
  have hdisj_O_IR : Disjoint (EO C N ∪ EI C N) (ER C N) := by
    rw [Finset.disjoint_left]
    intro e heOI heR
    have heR' := (Finset.mem_filter.mp heR).2
    rw [Finset.mem_sym2_iff] at heR'
    rcases Finset.mem_union.mp heOI with heO | heI
    · rcases Sym2.exists.mp ⟨G.ends e, rfl⟩ with ⟨a, b, hab⟩
      have ha_e : a ∈ G.ends e := by rw [hab]; simp
      have ha_out := mem_outerSet_of_mem_EO C heO ha_e
      have ha_R := ((mem_RSet_iff C).mp (heR' a ha_e)).1
      exact ha_R ha_out
    · rcases (Finset.mem_filter.mp heI).2 with ⟨w, hwI, hwe⟩
      have hw_R := ((mem_RSet_iff C).mp (heR' w hwe)).2
      exact hw_R ((mem_ISet_iff C).mp hwI)
  have hunion : EO C N ∪ EI C N ∪ ER C N = N := by
    ext e
    simp only [Finset.mem_union]
    constructor
    · rintro ((heO | heI) | heR)
      · rcases Finset.mem_biUnion.mp heO with ⟨_, _, he⟩
        exact (Finset.mem_filter.mp he).1
      · exact (Finset.mem_filter.mp heI).1
      · exact (Finset.mem_filter.mp heR).1
    · intro heN
      rcases Sym2.exists.mp ⟨G.ends e, rfl⟩ with ⟨a, b, hab⟩
      by_cases haI : a ∈ innerSet C
      · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨heN, a, (mem_ISet_iff C).mpr haI, by rw [hab]; simp⟩))
      · by_cases hbI : b ∈ innerSet C
        · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨heN, b, (mem_ISet_iff C).mpr hbI, by rw [hab]; simp⟩))
        · by_cases haO : a ∈ outerSet C
          · rcases (outer_adjacent_6_4 G M C).1 a haO e b hab with hbI' | hpart
            · exact False.elim (hbI hbI')
            · refine Or.inl (Or.inl (Finset.mem_biUnion.mpr ⟨C.P.part a, C.P.part_mem.2 (Finset.mem_univ a), ?_⟩))
              refine Finset.mem_filter.mpr ⟨heN, ?_⟩
              rw [hab, Finset.mk_mem_sym2_iff]
              exact ⟨C.P.mem_part (Finset.mem_univ a), hpart ▸ C.P.mem_part (Finset.mem_univ b)⟩
          · by_cases hbO : b ∈ outerSet C
            · rcases (outer_adjacent_6_4 G M C).1 b hbO e a (hab.trans Sym2.eq_swap) with haI' | hpart
              · exact False.elim (haI haI')
              · refine Or.inl (Or.inl (Finset.mem_biUnion.mpr ⟨C.P.part b, C.P.part_mem.2 (Finset.mem_univ b), ?_⟩))
                refine Finset.mem_filter.mpr ⟨heN, ?_⟩
                rw [hab, Finset.mk_mem_sym2_iff]
                exact ⟨hpart ▸ C.P.mem_part (Finset.mem_univ a), C.P.mem_part (Finset.mem_univ b)⟩
            · refine Or.inr (Finset.mem_filter.mpr ⟨heN, ?_⟩)
              rw [hab, Finset.mk_mem_sym2_iff, mem_RSet_iff, mem_RSet_iff]
              exact ⟨⟨haO, haI⟩, ⟨hbO, hbI⟩⟩
  calc N.card = (EO C N ∪ EI C N ∪ ER C N).card := by rw [hunion]
    _ = (EO C N).card + (EI C N).card + (ER C N).card := by
      rw [Finset.card_union_of_disjoint hdisj_O_IR, Finset.card_union_of_disjoint hdisj_OI]

lemma card_EO_eq_sum {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}
    (C : Config60 G M) (N : Finset E) :
    (EO C N).card = ∑ U ∈ C.P.parts, (N.filter (fun e => G.ends e ∈ U.sym2)).card := by
  refine Finset.card_biUnion fun U₁ hU₁ U₂ hU₂ hne => ?_
  rw [Function.onFun, Finset.disjoint_left]
  intro e he₁ he₂
  rcases Sym2.exists.mp ⟨G.ends e, rfl⟩ with ⟨a, b, hab⟩
  have ha₁ : a ∈ U₁ := by
    have := (Finset.mem_filter.mp he₁).2; rw [hab, Finset.mk_mem_sym2_iff] at this; exact this.1
  have ha₂ : a ∈ U₂ := by
    have := (Finset.mem_filter.mp he₂).2; rw [hab, Finset.mk_mem_sym2_iff] at this; exact this.1
  exact hne (C.P.eq_of_mem_parts hU₁ hU₂ ha₁ ha₂)

lemma card_EO_le {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}
    (C : Config60 G M) {N : Finset E} (hN : IsMatching G N) :
    (EO C N).card ≤ (EO C M).card := by
  rw [card_EO_eq_sum C N, card_EO_eq_sum C M]
  exact Finset.sum_le_sum fun U hU => card_filter_sym2_le_of_blossomSet (C.blossom U hU) hN

lemma card_EI_M_eq_ISet {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}
    (C : Config60 G M) :
    (EI C M).card = (ISet C).card := by
  have hM_EI : IsMatching G (EI C M) := fun e he f hf =>
    C.hM.1 e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1
  have hsum_v : ∑ w ∈ ISet C, ((EI C M).filter (fun e => w ∈ G.ends e)).card = (ISet C).card := by
    calc ∑ w ∈ ISet C, ((EI C M).filter (fun e => w ∈ G.ends e)).card
        = ∑ _w ∈ ISet C, 1 := by
          refine Finset.sum_congr rfl fun w hw => ?_
          have hle := card_filter_matching_le_one hM_EI w
          obtain ⟨e, heM, b, _, hends⟩ := exists_M_edge_to_outer_of_mem_innerSet C ((mem_ISet_iff C).mp hw)
          have hwe : w ∈ G.ends e := by rw [hends]; simp
          have he_EI : e ∈ EI C M := Finset.mem_filter.mpr ⟨heM, w, hw, hwe⟩
          have hge : 1 ≤ ((EI C M).filter (fun f => w ∈ G.ends f)).card :=
            Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he_EI, hwe⟩⟩
          omega
      _ = (ISet C).card := by simp
  have hsum_e : ∑ e ∈ EI C M, ((ISet C).filter (fun w => w ∈ G.ends e)).card = (EI C M).card := by
    calc ∑ e ∈ EI C M, ((ISet C).filter (fun w => w ∈ G.ends e)).card
        = ∑ _e ∈ EI C M, 1 := by
          refine Finset.sum_congr rfl fun e he => ?_
          have heM : e ∈ M := (Finset.mem_filter.mp he).1
          rcases (Finset.mem_filter.mp he).2 with ⟨w, hwI, hwe⟩
          rcases Sym2.exists.mp ⟨G.ends e, rfl⟩ with ⟨a, b, hab⟩
          have hw_ab : w = a ∨ w = b := by simpa [hab] using hwe
          have h_ends_w : ∃ u : V, G.ends e = s(w, u) := by
            rcases hw_ab with rfl | rfl
            · exact ⟨b, hab⟩
            · exact ⟨a, hab.trans Sym2.eq_swap⟩
          rcases h_ends_w with ⟨u, hends⟩
          have hu_out := other_end_mem_outerSet_of_mem_M_of_mem_innerSet C heM ((mem_ISet_iff C).mp hwI) hends
          have hfilt : (ISet C).filter (fun x => x ∈ G.ends e) = {w} := by
            ext x
            simp only [Finset.mem_filter, hends, Sym2.mem_iff, Finset.mem_singleton]
            constructor
            · rintro ⟨hxI, rfl | rfl⟩
              · rfl
              · exact False.elim (disjoint_outerSet_innerSet C hu_out ((mem_ISet_iff C).mp hxI))
            · rintro rfl
              exact ⟨hwI, Or.inl rfl⟩
          rw [hfilt, Finset.card_singleton]
      _ = (EI C M).card := by simp
  linarith [sum_card_filter_ends G (ISet C) (EI C M)]

lemma two_mul_card_ER_M_eq_RSet {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}
    (C : Config60 G M) :
    2 * (ER C M).card = (RSet C).card := by
  have hM_ER : IsMatching G (ER C M) := fun e he f hf =>
    C.hM.1 e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1
  have hsum_v : ∑ w ∈ RSet C, ((ER C M).filter (fun e => w ∈ G.ends e)).card = (RSet C).card := by
    calc ∑ w ∈ RSet C, ((ER C M).filter (fun e => w ∈ G.ends e)).card
        = ∑ _w ∈ RSet C, 1 := by
          refine Finset.sum_congr rfl fun w hw => ?_
          have hle := card_filter_matching_le_one hM_ER w
          have hw' := (mem_RSet_iff C).mp hw
          obtain ⟨e, heM, u, huo, hui, hends⟩ := exists_M_edge_to_R_of_not_mem_outer_inner C hw'.1 hw'.2
          have hwe : w ∈ G.ends e := by rw [hends]; simp
          have he_ER : e ∈ ER C M := by
            refine Finset.mem_filter.mpr ⟨heM, ?_⟩
            rw [hends, Finset.mk_mem_sym2_iff, mem_RSet_iff, mem_RSet_iff]
            exact ⟨hw', ⟨huo, hui⟩⟩
          have hge : 1 ≤ ((ER C M).filter (fun f => w ∈ G.ends f)).card :=
            Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he_ER, hwe⟩⟩
          omega
      _ = (RSet C).card := by simp
  have hsum_e : ∑ e ∈ ER C M, ((RSet C).filter (fun w => w ∈ G.ends e)).card = 2 * (ER C M).card := by
    calc ∑ e ∈ ER C M, ((RSet C).filter (fun w => w ∈ G.ends e)).card
        = ∑ _e ∈ ER C M, 2 := Finset.sum_congr rfl fun e he =>
          card_filter_ends_eq_two_of_mem_sym2 (Finset.mem_filter.mp he).2
      _ = 2 * (ER C M).card := by simp [Nat.mul_comm]
  linarith [sum_card_filter_ends G (RSet C) (ER C M)]

lemma card_EI_le_erase_of_sub {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}
    (C : Config60 G M) {v : V} {N : Finset E}
    (hN_sub : N ⊆ (induced G (Finset.univ.erase v)).edges) (hN : IsMatching G N) :
    (EI C N).card ≤ ((ISet C).erase v).card := by
  have hN_EI : IsMatching G (EI C N) := fun e he f hf =>
    hN e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1
  have hsub : EI C N ⊆ ((ISet C).erase v).biUnion (fun w => (EI C N).filter (fun e => w ∈ G.ends e)) := by
    intro e he
    have heN : e ∈ N := (Finset.mem_filter.mp he).1
    rcases (Finset.mem_filter.mp he).2 with ⟨w, hwI, hwe⟩
    have hw_ne_v : w ≠ v := by
      have hmem := (induced G (Finset.univ.erase v)).ends_mem e (hN_sub heN) w hwe
      exact (Finset.mem_erase.mp hmem).1
    exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_erase.mpr ⟨hw_ne_v, hwI⟩, Finset.mem_filter.mpr ⟨he, hwe⟩⟩
  calc (EI C N).card
      ≤ (((ISet C).erase v).biUnion (fun w => (EI C N).filter (fun e => w ∈ G.ends e))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ w ∈ (ISet C).erase v, ((EI C N).filter (fun e => w ∈ G.ends e)).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ (ISet C).erase v, 1 := Finset.sum_le_sum fun w _ => card_filter_matching_le_one hN_EI w
    _ = ((ISet C).erase v).card := by simp

lemma two_mul_card_ER_le_erase_of_sub {G : EdmondsMatching65.Polyhedron.Graph V E} {M : Finset E}
    (C : Config60 G M) {v : V} {N : Finset E}
    (hN_sub : N ⊆ (induced G (Finset.univ.erase v)).edges) (hN : IsMatching G N) :
    2 * (ER C N).card ≤ ((RSet C).erase v).card := by
  have hsub : ER C N ⊆ N.filter (fun e => G.ends e ∈ ((RSet C).erase v).sym2) := by
    intro e he
    have heN : e ∈ N := (Finset.mem_filter.mp he).1
    have heR : G.ends e ∈ (RSet C).sym2 := (Finset.mem_filter.mp he).2
    refine Finset.mem_filter.mpr ⟨heN, ?_⟩
    rw [Finset.mem_sym2_iff] at heR ⊢
    intro x hx
    have hx_er := (induced G (Finset.univ.erase v)).ends_mem e (hN_sub heN) x hx
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx_er).1, heR x hx⟩
  calc 2 * (ER C N).card
      ≤ 2 * (N.filter (fun e => G.ends e ∈ ((RSet C).erase v).sym2)).card :=
        Nat.mul_le_mul_left 2 (Finset.card_le_card hsub)
    _ ≤ ((RSet C).erase v).card := two_mul_card_filter_sym2_le hN ((RSet C).erase v)

end SolPathsTreesFlowersMaxMatchingErase66

open PathsTreesFlowers.Invariance
open SolPathsTreesFlowersMaxMatchingErase66

/-- 6.6, p. 465: a non-outer vertex `v` meets an edge `e` of `M`, and for such an edge `M − e` is
a maximum matching of `G − v` (the subgraph induced on the vertices other than `v`). -/
theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (C : Config60 G M) (v : V) (hv : v ∉ outerSet C) :
    (∃ e ∈ M, v ∈ G.ends e) ∧
    ∀ e ∈ M, v ∈ G.ends e → IsMaxMatchingIn G (induced G (Finset.univ.erase v)) (M.erase e) := by
  refine ⟨?_, ?_⟩
  · by_cases hvi : v ∈ innerSet C
    · obtain ⟨e, heM, b, _, hends⟩ := exists_M_edge_to_outer_of_mem_innerSet C hvi
      exact ⟨e, heM, by rw [hends]; simp⟩
    · obtain ⟨e, heM, u, _, _, hends⟩ := exists_M_edge_to_R_of_not_mem_outer_inner C hv hvi
      exact ⟨e, heM, by rw [hends]; simp⟩
  · intro e heM hve
    refine ⟨?_, ?_, ?_⟩
    · intro f hf
      have hf_ne_e : f ≠ e := (Finset.mem_erase.mp hf).1
      have hfM : f ∈ M := (Finset.mem_erase.mp hf).2
      simp only [induced, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sym2_iff,
        Finset.mem_erase]
      intro x hxf
      refine ⟨?_, trivial⟩
      rintro rfl
      exact C.hM.1 f hfM e heM hf_ne_e x hxf hve
    · intro f₁ hf₁ f₂ hf₂
      exact C.hM.1 f₁ (Finset.mem_erase.mp hf₁).2 f₂ (Finset.mem_erase.mp hf₂).2
    · intro M' hM'_sub hM'_match
      have hM'_part := card_partition_EO_EI_ER C M'
      have hM_part := card_partition_EO_EI_ER C M
      have hEO_le := card_EO_le C hM'_match
      have hEI_M := card_EI_M_eq_ISet C
      have hER_M := two_mul_card_ER_M_eq_RSet C
      have hEI_M' := card_EI_le_erase_of_sub C hM'_sub hM'_match
      have hER_M' := two_mul_card_ER_le_erase_of_sub C hM'_sub hM'_match
      have hcard_erase : (M.erase e).card + 1 = M.card := Finset.card_erase_add_one heM
      have h_strict : 2 * ((ISet C).erase v).card + ((RSet C).erase v).card + 1 ≤
          2 * (ISet C).card + (RSet C).card := by
        by_cases hvi : v ∈ innerSet C
        · have hvI : v ∈ ISet C := (mem_ISet_iff C).mpr hvi
          have hpos : 1 ≤ (ISet C).card := Finset.card_pos.mpr ⟨v, hvI⟩
          have herI : ((ISet C).erase v).card = (ISet C).card - 1 := Finset.card_erase_of_mem hvI
          have herR : ((RSet C).erase v).card ≤ (RSet C).card := Finset.card_erase_le
          omega
        · have hvR : v ∈ RSet C := (mem_RSet_iff C).mpr ⟨hv, hvi⟩
          have hpos : 1 ≤ (RSet C).card := Finset.card_pos.mpr ⟨v, hvR⟩
          have herI : ((ISet C).erase v).card ≤ (ISet C).card := Finset.card_erase_le
          have herR : ((RSet C).erase v).card = (RSet C).card - 1 := Finset.card_erase_of_mem hvR
          omega
      omega
