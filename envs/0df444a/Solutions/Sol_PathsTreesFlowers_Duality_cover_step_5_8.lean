-- Prove2me | solution 1 for PathsTreesFlowers.Duality.cover_step_5_8
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T10:13:37.545545+00:00
-- url     : https://prove2.me/submissions/f5682396-7183-4ac0-9071-fbf9a1343760

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Rotate
import Mathlib.Data.List.MinMax
import Mathlib.Order.Partition.Finpartition
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Duality_Basic
import Definitions.Def_PathsTreesFlowers_Duality_Shrink
import Definitions.Def_PathsTreesFlowers_Duality_OddSetCover
import Definitions.Def_PathsTreesFlowers_Duality_HungarianConfig
import Theorems.Thm_PathsTreesFlowers_Duality_lemma_4_2

namespace SolPathsTreesFlowersCoverStep58

set_option linter.unusedSectionVars false

open EdmondsMatching65.Polyhedron (IsMatching)
open PathsTreesFlowers.Duality

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ### Part 1: Double counting and `IsBlossomSet` properties -/

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
    {M : Finset E} {U : Finset V} (hU : IsBlossomSet G M U) :
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

lemma blossomSet_odd {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} {U : Finset V} (hU : IsBlossomSet G M U) :
    Odd U.card := by
  induction hU with
  | single v => exact ⟨0, by simp⟩
  | circuit k Uf _ef _hk _hUf hdisj _hef _hMf ih =>
    have hcard : ((Finset.range (2 * k + 1)).biUnion Uf).card =
        ∑ i ∈ Finset.range (2 * k + 1), (Uf i).card := by
      refine Finset.card_biUnion fun i hi j hj hij => ?_
      exact hdisj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hij
    have h_eq : ∀ i ∈ Finset.range (2 * k + 1), (Uf i).card = 2 * ((Uf i).card / 2) + 1 := by
      intro i hi
      rcases ih i (Finset.mem_range.mp hi) with ⟨r, hr⟩
      omega
    rw [hcard, Finset.sum_congr rfl h_eq]
    have hsum_rw : ∑ i ∈ Finset.range (2 * k + 1), (2 * ((Uf i).card / 2) + 1) =
        (∑ i ∈ Finset.range (2 * k + 1), (Uf i).card / 2) +
          (∑ i ∈ Finset.range (2 * k + 1), (Uf i).card / 2) + (2 * k + 1) := by
      simp_rw [Nat.two_mul, Finset.sum_add_distrib]
      simp
    rw [hsum_rw]
    exact ⟨(∑ i ∈ Finset.range (2 * k + 1), (Uf i).card / 2) + k, by omega⟩

lemma blossomSet_card_eq_two_mul_add_one {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (hM : IsMatching G M) {U : Finset V} (hU : IsBlossomSet G M U) :
    U.card = 2 * (M.filter (fun e => G.ends e ∈ U.sym2)).card + 1 := by
  have h1 := two_mul_card_filter_sym2_le hM U
  have h2 := blossomSet_card_le_two_mul_add_one hU
  rcases blossomSet_odd hU with ⟨r, hr⟩
  omega

lemma exposedIn_card_eq_one_of_blossomSet {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (hM : IsMatching G M) {U : Finset V} (hU : IsBlossomSet G M U) :
    (exposedIn G U M).card = 1 := by
  set MS := M.filter (fun e => G.ends e ∈ U.sym2)
  have hMS : IsMatching G MS := fun e he f hf =>
    hM e (Finset.mem_filter.mp he).1 f (Finset.mem_filter.mp hf).1
  have hU_card : U.card = 2 * MS.card + 1 := blossomSet_card_eq_two_mul_add_one hM hU
  have hsum_e : ∑ e ∈ MS, (U.filter (fun v => v ∈ G.ends e)).card = 2 * MS.card := by
    calc ∑ e ∈ MS, (U.filter (fun v => v ∈ G.ends e)).card
        = ∑ _e ∈ MS, 2 := Finset.sum_congr rfl fun e he =>
          card_filter_ends_eq_two_of_mem_sym2 (Finset.mem_filter.mp he).2
      _ = 2 * MS.card := by simp [Nat.mul_comm]
  have h_deg : ∀ v ∈ U, (MS.filter (fun e => v ∈ G.ends e)).card =
      if v ∉ exposedIn G U M then 1 else 0 := by
    intro v hvU
    by_cases hv : v ∈ exposedIn G U M
    · rw [if_neg (not_not.mpr hv), Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro e he
      rcases Finset.mem_filter.mp he with ⟨heM, heU⟩
      exact (Finset.mem_filter.mp hv).2 e heM heU
    · rw [if_pos hv]
      have hle := card_filter_matching_le_one hMS v
      have hpos : 0 < (MS.filter (fun e => v ∈ G.ends e)).card := by
        rw [Finset.card_pos]
        simp only [exposedIn, Finset.mem_filter, hvU, true_and, not_forall, not_not] at hv
        rcases hv with ⟨e, heM, heU, hve⟩
        exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨heM, heU⟩, hve⟩⟩
      omega
  have hsum_v : ∑ v ∈ U, (MS.filter (fun e => v ∈ G.ends e)).card =
      (U.filter (fun v => v ∉ exposedIn G U M)).card := by
    rw [Finset.sum_congr rfl h_deg, ← Finset.sum_filter, ← Finset.card_eq_sum_ones]
  have hexp_filt : U.filter (fun v => v ∈ exposedIn G U M) = exposedIn G U M := by
    ext v; simp [exposedIn]
  have hcard_split := Finset.card_filter_add_card_filter_not (s := U) (p := fun v => v ∈ exposedIn G U M)
  rw [hexp_filt] at hcard_split
  have hcomm := sum_card_filter_ends G U MS
  omega

lemma mem_exposedIn_of_mem_M_of_not_mem_sym2 {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (hM : IsMatching G M) {U : Finset V} {e : E} (heM : e ∈ M)
    (hnot : G.ends e ∉ U.sym2) {v : V} (hvU : v ∈ U) (hve : v ∈ G.ends e) :
    v ∈ exposedIn G U M := by
  refine Finset.mem_filter.mpr ⟨hvU, fun f hfM hfU hvf => ?_⟩
  have hef : e ≠ f := fun h => hnot (h ▸ hfU)
  exact hM e heM f hfM hef v hve hvf

/-! ### Part 2: Partition and `HungarianConfig` properties -/

lemma toPart_eq_iff (P : Finpartition (Finset.univ : Finset V)) (v : V)
    (p : {U : Finset V // U ∈ P.parts}) :
    toPart P v = p ↔ v ∈ p.1 := by
  constructor
  · intro h
    rw [← congrArg Subtype.val h]
    exact P.mem_part (Finset.mem_univ v)
  · intro hv
    exact Subtype.ext (P.eq_of_mem_parts (P.part_mem.2 (Finset.mem_univ v)) p.2
      (P.mem_part (Finset.mem_univ v)) hv)

lemma card_eq_one_of_not_mem_outer {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (C : HungarianConfig G M) {p : {U : Finset V // U ∈ C.P.parts}}
    (hp : p ∉ C.J.outer) : p.1.card = 1 := by
  have hpos : 0 < p.1.card := Finset.card_pos.mpr (C.P.nonempty_of_mem_parts p.2)
  have hle : p.1.card ≤ 1 := by
    by_contra hgt
    exact hp (C.pseudo_outer p.1 p.2 (by omega))
  omega

lemma card_eq_one_of_mem_inner {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (C : HungarianConfig G M) {p : {U : Finset V // U ∈ C.P.parts}}
    (hp : p ∈ C.J.inner) : p.1.card = 1 :=
  card_eq_one_of_not_mem_outer C (Finset.disjoint_left.mp C.J.disjoint hp)

lemma mem_SJ_iff {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (C : HungarianConfig G M) (U : Finset V) :
    U ∈ C.SJ ↔ ∃ hU : U ∈ C.P.parts,
      (⟨U, hU⟩ : {W : Finset V // W ∈ C.P.parts}) ∈ C.J.inner ∨
        ((⟨U, hU⟩ : {W : Finset V // W ∈ C.P.parts}) ∈ C.J.outer ∧ 2 ≤ U.card) := by
  simp only [HungarianConfig.SJ, Finset.mem_image, Finset.mem_union, Finset.mem_filter,
    Subtype.exists]
  constructor
  · rintro ⟨W, hW, h, rfl⟩
    exact ⟨hW, h⟩
  · rintro ⟨hU, h⟩
    exact ⟨U, hU, h, rfl⟩

lemma mem_verts_of_mem_SJ {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (C : HungarianConfig G M) {U : Finset V} (hU_SJ : U ∈ C.SJ) :
    ∃ hU : U ∈ C.P.parts, (⟨U, hU⟩ : {W : Finset V // W ∈ C.P.parts}) ∈ C.J.verts := by
  rcases (mem_SJ_iff C U).mp hU_SJ with ⟨hU, h | ⟨h, _⟩⟩
  · exact ⟨hU, Finset.mem_union_left _ h⟩
  · exact ⟨hU, Finset.mem_union_right _ h⟩

lemma not_mem_X_of_mem_SJ {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (C : HungarianConfig G M) {U : Finset V} (hU_SJ : U ∈ C.SJ)
    {v : V} (hv : v ∈ U) : v ∉ C.X := by
  rcases mem_verts_of_mem_SJ C hU_SJ with ⟨hU, hp_verts⟩
  simp only [HungarianConfig.X, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
  rwa [(toPart_eq_iff C.P v ⟨U, hU⟩).mpr hv]

/-! ### Part 3: Shrunken matching and `C.J` properties -/

lemma not_mem_sym2_of_not_insidePart {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {e : E} (he : ¬ InsidePart G P e)
    (p : {U : Finset V // U ∈ P.parts}) : G.ends e ∉ p.1.sym2 :=
  fun h => he ⟨p.1, p.2, h⟩

lemma exists_mem_part_and_ends_of_mem_shrink_ends {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {e : {e : E // ¬ InsidePart G P e}}
    {p : {U : Finset V // U ∈ P.parts}} (hp : p ∈ (shrink G P).ends e) :
    ∃ v ∈ p.1, v ∈ G.ends e.1 := by
  change p ∈ (G.ends e.1).map (toPart P) at hp
  rcases Sym2.mem_map.mp hp with ⟨v, hve, hvp⟩
  exact ⟨v, (toPart_eq_iff P v p).mp hvp, hve⟩

lemma mem_shrink_ends_of_mem_part_and_ends {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {e : {e : E // ¬ InsidePart G P e}}
    {p : {U : Finset V // U ∈ P.parts}} {v : V} (hvp : v ∈ p.1) (hve : v ∈ G.ends e.1) :
    p ∈ (shrink G P).ends e := by
  change p ∈ (G.ends e.1).map (toPart P)
  exact Sym2.mem_map.mpr ⟨v, hve, (toPart_eq_iff P v p).mpr hvp⟩

lemma isMatching_shrinkMatching {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (hM : IsMatching G M) (C : HungarianConfig G M) :
    IsMatching (shrink G C.P) (shrinkMatching G C.P M) := by
  intro e₁ he₁ e₂ he₂ hne p hp₁ hp₂
  have he₁M : e₁.1 ∈ M := Finset.mem_subtype.mp he₁
  have he₂M : e₂.1 ∈ M := Finset.mem_subtype.mp he₂
  obtain ⟨v₁, hv₁p, hv₁e⟩ := exists_mem_part_and_ends_of_mem_shrink_ends hp₁
  obtain ⟨v₂, hv₂p, hv₂e⟩ := exists_mem_part_and_ends_of_mem_shrink_ends hp₂
  have hv₁_exp := mem_exposedIn_of_mem_M_of_not_mem_sym2 hM he₁M
    (not_mem_sym2_of_not_insidePart e₁.2 p) hv₁p hv₁e
  have hv₂_exp := mem_exposedIn_of_mem_M_of_not_mem_sym2 hM he₂M
    (not_mem_sym2_of_not_insidePart e₂.2 p) hv₂p hv₂e
  have hcard1 := exposedIn_card_eq_one_of_blossomSet hM (C.blossom_sets p.1 p.2)
  have hv_eq : v₁ = v₂ := Finset.card_le_one.mp (by omega) v₁ hv₁_exp v₂ hv₂_exp
  subst hv_eq
  exact hM e₁.1 he₁M e₂.1 he₂M (Subtype.coe_ne_coe.mpr hne) v₁ hv₁e hv₂e

lemma isExposed_tree_iff_eq_root {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (C : HungarianConfig G M) {w : {U : Finset V // U ∈ C.P.parts}}
    (hw : w ∈ C.J.verts) :
    IsExposed (shrink G C.P) (shrinkMatching G C.P M ∩ C.J.edges) w ↔
      w = toPart C.P C.root := by
  obtain ⟨v₀, _hv₀, hiff⟩ := (lemma_4_2 (shrink G C.P) C.J).2.2
    (shrinkMatching G C.P M ∩ C.J.edges) C.planted.1
  have hr_exp : IsExposed (shrink G C.P) (shrinkMatching G C.P M ∩ C.J.edges)
      (toPart C.P C.root) := C.planted.2.2.1
  have hr_eq : toPart C.P C.root = v₀ := (hiff (toPart C.P C.root) C.planted.2.1).mp hr_exp
  rw [hr_eq]
  exact hiff w hw

lemma mem_J_edges_of_mem_shrinkMatching_of_mem_verts {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (hM : IsMatching G M) (C : HungarianConfig G M)
    {e_sh : {e : E // ¬ InsidePart G C.P e}} (heM : e_sh ∈ shrinkMatching G C.P M)
    {p : {U : Finset V // U ∈ C.P.parts}} (hp_verts : p ∈ C.J.verts)
    (hp_ends : p ∈ (shrink G C.P).ends e_sh) : e_sh ∈ C.J.edges := by
  have hp_ne_root : p ≠ toPart C.P C.root := by
    rintro rfl
    exact C.planted.2.2.2 e_sh heM hp_ends
  have hnot_exp : ¬ IsExposed (shrink G C.P) (shrinkMatching G C.P M ∩ C.J.edges) p :=
    fun hexp => hp_ne_root ((isExposed_tree_iff_eq_root C hp_verts).mp hexp)
  simp only [PathsTreesFlowers.Duality.IsExposed, not_forall, not_not] at hnot_exp
  rcases hnot_exp with ⟨f_sh, hf_sh, hp_f⟩
  have heq : e_sh = f_sh := by
    by_contra hne
    exact isMatching_shrinkMatching hM C e_sh heM f_sh (Finset.mem_inter.mp hf_sh).1 hne p hp_ends hp_f
  exact heq ▸ (Finset.mem_inter.mp hf_sh).2

lemma isExposed_shrink_iff_eq_root {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (C : HungarianConfig G M)
    {w : {U : Finset V // U ∈ C.P.parts}} (hw : w ∈ C.J.verts) :
    IsExposed (shrink G C.P) (shrinkMatching G C.P M) w ↔ w = toPart C.P C.root := by
  constructor
  · intro hexp
    refine (isExposed_tree_iff_eq_root C hw).mp fun e he => ?_
    exact hexp e (Finset.mem_inter.mp he).1
  · rintro rfl
    exact C.planted.2.2.2

lemma not_mem_X_of_mem_M_of_not_mem_X {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (hM : IsMatching G M) (C : HungarianConfig G M)
    {e : E} (heM : e ∈ M) {a b : V} (hends : G.ends e = s(a, b)) (ha : a ∉ C.X) :
    b ∉ C.X := by
  simp only [HungarianConfig.X, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at ha ⊢
  by_cases h_in : InsidePart G C.P e
  · rcases h_in with ⟨U, hU, heU⟩
    rw [hends, Finset.mk_mem_sym2_iff] at heU
    have ha_p : toPart C.P a = ⟨U, hU⟩ := (toPart_eq_iff C.P a ⟨U, hU⟩).mpr heU.1
    have hb_p : toPart C.P b = ⟨U, hU⟩ := (toPart_eq_iff C.P b ⟨U, hU⟩).mpr heU.2
    rw [hb_p, ← ha_p]
    exact ha
  · set e_sh : {e : E // ¬ InsidePart G C.P e} := ⟨e, h_in⟩
    have he_shM : e_sh ∈ shrinkMatching G C.P M := Finset.mem_subtype.mpr heM
    have ha_ends : toPart C.P a ∈ (shrink G C.P).ends e_sh := by
      change toPart C.P a ∈ (G.ends e).map (toPart C.P)
      rw [hends, Sym2.map_mk]
      exact Sym2.mem_mk_left _ _
    have he_J : e_sh ∈ C.J.edges :=
      mem_J_edges_of_mem_shrinkMatching_of_mem_verts hM C he_shM ha ha_ends
    have hb_ends : toPart C.P b ∈ (shrink G C.P).ends e_sh := by
      change toPart C.P b ∈ (G.ends e).map (toPart C.P)
      rw [hends, Sym2.map_mk]
      exact Sym2.mem_mk_right _ _
    have hsub := C.J.toSub.edges_sub e_sh he_J
    rw [Finset.mem_sym2_iff] at hsub
    exact hsub (toPart C.P b) hb_ends

/-! ### Part 4: The 7 Conjuncts of `cover_step_5_8` -/

lemma conj1_odd {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (C : HungarianConfig G M) :
    ∀ U ∈ C.SJ, IsOddSet U := by
  intro U hU_SJ
  rcases mem_verts_of_mem_SJ C hU_SJ with ⟨hU, _⟩
  exact blossomSet_odd (C.blossom_sets U hU)

lemma conj2_capacity {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (hM : IsMatching G M) (C : HungarianConfig G M) :
    ∀ U ∈ C.SJ, (M.filter (Covers G U)).card = capacity U := by
  intro U hU_SJ
  rcases (mem_SJ_iff C U).mp hU_SJ with ⟨hU, h_in | ⟨_h_out, hcard⟩⟩
  · have hcard1 : U.card = 1 := card_eq_one_of_mem_inner C h_in
    have hcap : capacity U = 1 := by simp [capacity, hcard1]
    rw [hcap]
    obtain ⟨u, huU⟩ := Finset.card_eq_one.mp hcard1
    have hfilt_eq : M.filter (Covers G U) = M.filter (fun e => u ∈ G.ends e) := by
      ext e
      simp [Covers, huU]
    rw [hfilt_eq]
    have hle : (M.filter (fun e => u ∈ G.ends e)).card ≤ 1 := card_filter_matching_le_one hM u
    have h_verts : (⟨U, hU⟩ : {W : Finset V // W ∈ C.P.parts}) ∈ C.J.verts :=
      Finset.mem_union_left _ h_in
    have h_ne_root : (⟨U, hU⟩ : {W : Finset V // W ∈ C.P.parts}) ≠ toPart C.P C.root := by
      rintro heq
      have hr_exp := C.planted.2.2.1
      obtain ⟨v₀, hv₀, hiff⟩ := (lemma_4_2 (shrink G C.P) C.J).2.2
        (shrinkMatching G C.P M ∩ C.J.edges) C.planted.1
      have hr_v₀ : toPart C.P C.root = v₀ := (hiff (toPart C.P C.root) C.planted.2.1).mp hr_exp
      exact Finset.disjoint_left.mp C.J.disjoint h_in (heq.trans hr_v₀ ▸ hv₀)
    have hnot_exp : ¬ IsExposed (shrink G C.P) (shrinkMatching G C.P M ∩ C.J.edges) ⟨U, hU⟩ :=
      fun hexp => h_ne_root ((isExposed_tree_iff_eq_root C h_verts).mp hexp)
    simp only [PathsTreesFlowers.Duality.IsExposed, not_forall, not_not] at hnot_exp
    rcases hnot_exp with ⟨e_sh, he_sh, hp_ends⟩
    obtain ⟨v, hvU, hve⟩ := exists_mem_part_and_ends_of_mem_shrink_ends hp_ends
    have hvu : v = u := Finset.mem_singleton.mp (huU ▸ hvU)
    subst hvu
    have heM : e_sh.1 ∈ M := Finset.mem_subtype.mp (Finset.mem_inter.mp he_sh).1
    have hpos : 0 < (M.filter (fun e => v ∈ G.ends e)).card :=
      Finset.card_pos.mpr ⟨e_sh.1, Finset.mem_filter.mpr ⟨heM, hve⟩⟩
    omega
  · have hne1 : U.card ≠ 1 := by omega
    have hcap : capacity U = (U.card - 1) / 2 := by simp [capacity, hne1]
    have hfilt_eq : M.filter (Covers G U) = M.filter (fun e => G.ends e ∈ U.sym2) := by
      ext e
      simp [Covers, hne1]
    rw [hcap, hfilt_eq]
    have hcard_eq := blossomSet_card_eq_two_mul_add_one hM (C.blossom_sets U hU)
    omega

lemma conj4_covers_iff {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (C : HungarianConfig G M) (e : E) :
    (∃ U ∈ C.SJ, Covers G U e) ↔ G.ends e ∉ C.X.sym2 := by
  rcases Sym2.exists.mp ⟨G.ends e, rfl⟩ with ⟨a, b, hab⟩
  constructor
  · rintro ⟨U, hU_SJ, hcov⟩ hX
    rw [hab, Finset.mk_mem_sym2_iff] at hX
    by_cases h1 : U.card = 1
    · simp only [Covers, h1, ↓reduceIte, hab, Sym2.mem_iff] at hcov
      rcases hcov with ⟨v, hvU, rfl | rfl⟩
      · exact not_mem_X_of_mem_SJ C hU_SJ hvU hX.1
      · exact not_mem_X_of_mem_SJ C hU_SJ hvU hX.2
    · simp only [Covers, h1, ↓reduceIte, hab, Finset.mk_mem_sym2_iff] at hcov
      exact not_mem_X_of_mem_SJ C hU_SJ hcov.1 hX.1
  · intro hnotX
    have h_not_both : a ∉ C.X ∨ b ∉ C.X := by
      rw [hab, Finset.mk_mem_sym2_iff, not_and_or] at hnotX
      exact hnotX
    by_cases h_in : InsidePart G C.P e
    · rcases h_in with ⟨U, hU, heU⟩
      have hne : a ≠ b := by
        rintro rfl
        exact G.loopless e (hab ▸ Sym2.mk_isDiag_iff.mpr rfl)
      have heU' := heU
      rw [hab, Finset.mk_mem_sym2_iff] at heU'
      have hcard2 : 2 ≤ U.card := Finset.one_lt_card.mpr ⟨a, heU'.1, b, heU'.2, hne⟩
      have hU_out : (⟨U, hU⟩ : {W : Finset V // W ∈ C.P.parts}) ∈ C.J.outer :=
        C.pseudo_outer U hU hcard2
      have hU_SJ : U ∈ C.SJ := (mem_SJ_iff C U).mpr ⟨hU, Or.inr ⟨hU_out, hcard2⟩⟩
      have hne1 : U.card ≠ 1 := by omega
      exact ⟨U, hU_SJ, by simp [Covers, hne1, heU]⟩
    · set e_sh : {e : E // ¬ InsidePart G C.P e} := ⟨e, h_in⟩
      have hends_sh : (shrink G C.P).ends e_sh = s(toPart C.P a, toPart C.P b) := by
        change (G.ends e).map (toPart C.P) = _
        rw [hab, Sym2.map_mk]
      have hex_inner : ∃ p ∈ C.J.inner, p ∈ (shrink G C.P).ends e_sh := by
        rcases h_not_both with haX | hbX
        · simp only [HungarianConfig.X, Finset.mem_filter, Finset.mem_univ, true_and, not_not,
            AltTree.verts, Finset.mem_union] at haX
          rcases haX with ha_in | ha_out
          · exact ⟨toPart C.P a, ha_in, by rw [hends_sh]; exact Sym2.mem_mk_left _ _⟩
          · obtain ⟨w, hw_in, hw_ends⟩ := C.hungarian e_sh (toPart C.P a) ha_out
              (by rw [hends_sh]; exact Sym2.mem_mk_left _ _)
            exact ⟨w, hw_in, by rw [hw_ends]; exact Sym2.mem_mk_right _ _⟩
        · simp only [HungarianConfig.X, Finset.mem_filter, Finset.mem_univ, true_and, not_not,
            AltTree.verts, Finset.mem_union] at hbX
          rcases hbX with hb_in | hb_out
          · exact ⟨toPart C.P b, hb_in, by rw [hends_sh]; exact Sym2.mem_mk_right _ _⟩
          · obtain ⟨w, hw_in, hw_ends⟩ := C.hungarian e_sh (toPart C.P b) hb_out
              (by rw [hends_sh]; exact Sym2.mem_mk_right _ _)
            exact ⟨w, hw_in, by rw [hw_ends]; exact Sym2.mem_mk_right _ _⟩
      rcases hex_inner with ⟨p, hp_in, hp_ends⟩
      have hp_SJ : p.1 ∈ C.SJ := (mem_SJ_iff C p.1).mpr ⟨p.2, Or.inl hp_in⟩
      have hp_card1 : p.1.card = 1 := card_eq_one_of_mem_inner C hp_in
      obtain ⟨v, hvp, hve⟩ := exists_mem_part_and_ends_of_mem_shrink_ends hp_ends
      exact ⟨p.1, hp_SJ, by rw [Covers, if_pos hp_card1]; exact ⟨v, hvp, hve⟩⟩

lemma conj3_unique_cover {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (hM : IsMatching G M) (C : HungarianConfig G M) :
    ∀ e ∈ M, G.ends e ∉ C.X.sym2 → (C.SJ.filter (fun U => Covers G U e)).card = 1 := by
  intro e heM hnotX
  obtain ⟨U₀, hU₀_SJ, hcov₀⟩ := (conj4_covers_iff C e).mpr hnotX
  refine Finset.card_eq_one.mpr ⟨U₀, ?_⟩
  ext U
  simp only [Finset.mem_filter, Finset.mem_singleton]
  refine ⟨fun ⟨hU_SJ, hcov⟩ => ?_, fun h => h ▸ ⟨hU₀_SJ, hcov₀⟩⟩
  by_cases h_in : InsidePart G C.P e
  · rcases h_in with ⟨W, hW, heW⟩
    have hUW : ∀ V₁ ∈ C.SJ, Covers G V₁ e → V₁ = W := by
      intro V₁ hV₁_SJ hcov₁
      rcases mem_verts_of_mem_SJ C hV₁_SJ with ⟨hV₁, _⟩
      rcases Sym2.exists.mp ⟨G.ends e, rfl⟩ with ⟨a, b, hab⟩
      have heW' := heW
      rw [hab, Finset.mk_mem_sym2_iff] at heW'
      by_cases hcard1 : V₁.card = 1
      · simp only [Covers, hcard1, ↓reduceIte, hab, Sym2.mem_iff] at hcov₁
        rcases hcov₁ with ⟨v, hvV₁, rfl | rfl⟩
        · exact C.P.eq_of_mem_parts hV₁ hW hvV₁ heW'.1
        · exact C.P.eq_of_mem_parts hV₁ hW hvV₁ heW'.2
      · simp only [Covers, hcard1, ↓reduceIte, hab, Finset.mk_mem_sym2_iff] at hcov₁
        exact C.P.eq_of_mem_parts hV₁ hW hcov₁.1 heW'.1
    exact (hUW U hU_SJ hcov).trans (hUW U₀ hU₀_SJ hcov₀).symm
  · set e_sh : {e : E // ¬ InsidePart G C.P e} := ⟨e, h_in⟩
    have he_shM : e_sh ∈ shrinkMatching G C.P M := Finset.mem_subtype.mpr heM
    have h_inner_end : ∀ V₁ ∈ C.SJ, Covers G V₁ e →
        ∃ hV₁ : V₁ ∈ C.P.parts,
          (⟨V₁, hV₁⟩ : {W : Finset V // W ∈ C.P.parts}) ∈ C.J.inner ∧
          (⟨V₁, hV₁⟩ : {W : Finset V // W ∈ C.P.parts}) ∈ (shrink G C.P).ends e_sh := by
      intro V₁ hV₁_SJ hcov₁
      rcases (mem_SJ_iff C V₁).mp hV₁_SJ with ⟨hV₁, h_inner | ⟨_h_outer, hcard2⟩⟩
      · have hcard1 : V₁.card = 1 := card_eq_one_of_mem_inner C h_inner
        simp only [Covers, hcard1, ↓reduceIte] at hcov₁
        rcases hcov₁ with ⟨v, hvV₁, hve⟩
        exact ⟨hV₁, h_inner, mem_shrink_ends_of_mem_part_and_ends hvV₁ hve⟩
      · have hne1 : V₁.card ≠ 1 := by omega
        simp only [Covers, hne1, ↓reduceIte] at hcov₁
        exact False.elim (h_in ⟨V₁, hV₁, hcov₁⟩)
    obtain ⟨hU, hU_in, hU_end⟩ := h_inner_end U hU_SJ hcov
    obtain ⟨hU₀, hU₀_in, hU₀_end⟩ := h_inner_end U₀ hU₀_SJ hcov₀
    have he_J : e_sh ∈ C.J.edges :=
      mem_J_edges_of_mem_shrinkMatching_of_mem_verts hM C he_shM
        (Finset.mem_union_left _ hU_in) hU_end
    obtain ⟨u_in, hu_in, w_out, hw_out, hends_J⟩ := C.J.edge_ends e_sh he_J
    have hU_eq_u : (⟨U, hU⟩ : {W : Finset V // W ∈ C.P.parts}) = u_in := by
      rw [hends_J, Sym2.mem_iff] at hU_end
      rcases hU_end with rfl | h_eq
      · rfl
      · exact False.elim (Finset.disjoint_left.mp C.J.disjoint hU_in (h_eq ▸ hw_out))
    have hU₀_eq_u : (⟨U₀, hU₀⟩ : {W : Finset V // W ∈ C.P.parts}) = u_in := by
      rw [hends_J, Sym2.mem_iff] at hU₀_end
      rcases hU₀_end with rfl | h_eq
      · rfl
      · exact False.elim (Finset.disjoint_left.mp C.J.disjoint hU₀_in (h_eq ▸ hw_out))
    exact congrArg Subtype.val (hU_eq_u.trans hU₀_eq_u.symm)

lemma conj7_card {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (hM : IsMatching G M) (C : HungarianConfig G M) :
    M.card = capacitySum C.SJ + (M ∩ edgesWithin G C.X).card := by
  set M₁ := M.filter (fun e => G.ends e ∉ C.X.sym2)
  set M₂ := M.filter (fun e => G.ends e ∈ C.X.sym2)
  have hM₂_eq : M₂ = M ∩ edgesWithin G C.X := by
    ext e
    simp [M₂, edgesWithin]
  have hM_split : M.card = M₁.card + M₂.card := by
    have h := (Finset.card_filter_add_card_filter_not (s := M) (p := fun e => G.ends e ∈ C.X.sym2)).symm
    change M.card = M₂.card + M₁.card at h
    omega
  have hM₁_cap : M₁.card = capacitySum C.SJ := by
    have hsum1 : M₁.card = ∑ e ∈ M₁, (C.SJ.filter (fun U => Covers G U e)).card := by
      calc M₁.card = ∑ _e ∈ M₁, 1 := by simp
        _ = ∑ e ∈ M₁, (C.SJ.filter (fun U => Covers G U e)).card :=
          Finset.sum_congr rfl fun e he => (conj3_unique_cover hM C e
            (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2).symm
    have hsum2 : ∑ e ∈ M₁, (C.SJ.filter (fun U => Covers G U e)).card =
        ∑ U ∈ C.SJ, (M₁.filter (Covers G U)).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.sum_comm
    have hsum3 : ∑ U ∈ C.SJ, (M₁.filter (Covers G U)).card =
        ∑ U ∈ C.SJ, (M.filter (Covers G U)).card := by
      refine Finset.sum_congr rfl fun U hU_SJ => congrArg Finset.card ?_
      ext e
      simp only [M₁, Finset.mem_filter]
      exact ⟨fun ⟨⟨heM, _⟩, hcov⟩ => ⟨heM, hcov⟩,
        fun ⟨heM, hcov⟩ => ⟨⟨heM, (conj4_covers_iff C e).mp ⟨U, hU_SJ, hcov⟩⟩, hcov⟩⟩
    have hsum4 : ∑ U ∈ C.SJ, (M.filter (Covers G U)).card = capacitySum C.SJ :=
      Finset.sum_congr rfl fun U hU_SJ => conj2_capacity hM C U hU_SJ
    exact hsum1.trans (hsum2.trans (hsum3.trans hsum4))
  rw [hM_split, hM₁_cap, hM₂_eq]

lemma conj5_maxMatchingIn_X {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (hM : IsMaxMatching G M) (C : HungarianConfig G M) :
    IsMaxMatchingIn G (induced G C.X) (M ∩ edgesWithin G C.X) := by
  refine ⟨Finset.inter_subset_right, ?_, ?_⟩
  · exact fun e he f hf => hM.1 e (Finset.mem_inter.mp he).1 f (Finset.mem_inter.mp hf).1
  · intro MX hMX_sub hMX_match
    set M₁ := M.filter (fun e => G.ends e ∉ C.X.sym2)
    have hM₁_no_X : ∀ e ∈ M₁, ∀ v ∈ G.ends e, v ∉ C.X := by
      intro e he v hve hvX
      rcases Finset.mem_filter.mp he with ⟨heM, hnotX⟩
      rcases Sym2.exists.mp ⟨G.ends e, rfl⟩ with ⟨a, b, hab⟩
      have h_not_both : a ∉ C.X ∨ b ∉ C.X := by
        rw [hab, Finset.mk_mem_sym2_iff, not_and_or] at hnotX
        exact hnotX
      have haX : a ∉ C.X := by
        rcases h_not_both with haX | hbX
        · exact haX
        · exact not_mem_X_of_mem_M_of_not_mem_X hM.1 C heM (hab.trans Sym2.eq_swap) hbX
      have hbX : b ∉ C.X := not_mem_X_of_mem_M_of_not_mem_X hM.1 C heM hab haX
      rw [hab, Sym2.mem_iff] at hve
      rcases hve with rfl | rfl
      · exact haX hvX
      · exact hbX hvX
    have hMX_in_X : ∀ e ∈ MX, ∀ v ∈ G.ends e, v ∈ C.X := by
      intro e he v hve
      have heX := (Finset.mem_filter.mp (hMX_sub he)).2
      exact Finset.mem_sym2_iff.mp heX v hve
    have hdisj : Disjoint M₁ MX := by
      rw [Finset.disjoint_left]
      intro e he₁ heX
      rcases Sym2.exists.mp ⟨G.ends e, rfl⟩ with ⟨a, b, hab⟩
      have ha : a ∈ G.ends e := by rw [hab]; exact Sym2.mem_mk_left _ _
      exact hM₁_no_X e he₁ a ha (hMX_in_X e heX a ha)
    have h_union_match : IsMatching G (M₁ ∪ MX) := by
      intro e he f hf hef v hve hvf
      rcases Finset.mem_union.mp he with he₁ | heX <;>
        rcases Finset.mem_union.mp hf with hf₁ | hfX
      · exact hM.1 e (Finset.mem_filter.mp he₁).1 f (Finset.mem_filter.mp hf₁).1 hef v hve hvf
      · exact hM₁_no_X e he₁ v hve (hMX_in_X f hfX v hvf)
      · exact hM₁_no_X f hf₁ v hvf (hMX_in_X e heX v hve)
      · exact hMX_match e heX f hfX hef v hve hvf
    have hle := hM.2 (M₁ ∪ MX) h_union_match
    rw [Finset.card_union_of_disjoint hdisj] at hle
    have hM_split : M.card = M₁.card + (M ∩ edgesWithin G C.X).card := by
      have hM₂_eq : M.filter (fun e => G.ends e ∈ C.X.sym2) = M ∩ edgesWithin G C.X := by
        ext e; simp [edgesWithin]
      have h := (Finset.card_filter_add_card_filter_not (s := M) (p := fun e => G.ends e ∈ C.X.sym2)).symm
      change M.card = (M.filter (fun e => G.ends e ∈ C.X.sym2)).card + M₁.card at h
      rw [hM₂_eq] at h
      omega
    omega

lemma conj6_exposed {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (hM : IsMatching G M) (C : HungarianConfig G M) :
    (exposedIn G C.X M).card + 1 = (Finset.univ.filter (IsExposed G M)).card := by
  have hexpX_eq : exposedIn G C.X M = C.X.filter (IsExposed G M) := by
    ext v
    simp only [exposedIn, Finset.mem_filter, PathsTreesFlowers.Duality.IsExposed]
    refine ⟨fun ⟨hvX, h⟩ => ⟨hvX, fun e heM hve => ?_⟩, fun ⟨hvX, h⟩ => ⟨hvX, fun e heM _ => h e heM⟩⟩
    refine h e heM ?_ hve
    by_contra hnotX
    rcases Sym2.exists.mp ⟨G.ends e, rfl⟩ with ⟨a, b, hab⟩
    have h_not_both : a ∉ C.X ∨ b ∉ C.X := by
      rw [hab, Finset.mk_mem_sym2_iff, not_and_or] at hnotX
      exact hnotX
    have haX : a ∉ C.X := by
      rcases h_not_both with haX | hbX
      · exact haX
      · exact not_mem_X_of_mem_M_of_not_mem_X hM C heM (hab.trans Sym2.eq_swap) hbX
    have hbX : b ∉ C.X := not_mem_X_of_mem_M_of_not_mem_X hM C heM hab haX
    rw [hab, Sym2.mem_iff] at hve
    rcases hve with rfl | rfl
    · exact haX hvX
    · exact hbX hvX
  have hpart_exp : ∀ p : {U : Finset V // U ∈ C.P.parts}, p ∈ C.J.verts →
      (p.1.filter (IsExposed G M)).card = if p = toPart C.P C.root then 1 else 0 := by
    intro p hp_verts
    by_cases hp_root : p = toPart C.P C.root
    · rw [if_pos hp_root]
      have hp_exp : IsExposed (shrink G C.P) (shrinkMatching G C.P M) p :=
        (isExposed_shrink_iff_eq_root C hp_verts).mpr hp_root
      have hfilt_eq : p.1.filter (IsExposed G M) = exposedIn G p.1 M := by
        ext v
        simp only [Finset.mem_filter, PathsTreesFlowers.Duality.IsExposed, exposedIn]
        refine ⟨fun ⟨hvp, h⟩ => ⟨hvp, fun e heM _ => h e heM⟩,
          fun ⟨hvp, h⟩ => ⟨hvp, fun e heM hve => ?_⟩⟩
        by_cases he_in : InsidePart G C.P e
        · rcases he_in with ⟨U, hU, heU⟩
          have hUp : U = p.1 := by
            rcases Sym2.exists.mp ⟨G.ends e, rfl⟩ with ⟨a, b, hab⟩
            have heU' := heU
            rw [hab, Finset.mk_mem_sym2_iff] at heU'
            rw [hab, Sym2.mem_iff] at hve
            rcases hve with rfl | rfl
            · exact C.P.eq_of_mem_parts hU p.2 heU'.1 hvp
            · exact C.P.eq_of_mem_parts hU p.2 heU'.2 hvp
          exact h e heM (hUp ▸ heU) hve
        · set e_sh : {e : E // ¬ InsidePart G C.P e} := ⟨e, he_in⟩
          exact hp_exp e_sh (Finset.mem_subtype.mpr heM)
            (mem_shrink_ends_of_mem_part_and_ends hvp hve)
      rw [hfilt_eq]
      exact exposedIn_card_eq_one_of_blossomSet hM (C.blossom_sets p.1 p.2)
    · rw [if_neg hp_root, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro v hvp hv_exp
      have hnot_exp : ¬ IsExposed (shrink G C.P) (shrinkMatching G C.P M) p :=
        fun hexp => hp_root ((isExposed_shrink_iff_eq_root C hp_verts).mp hexp)
      simp only [PathsTreesFlowers.Duality.IsExposed, not_forall, not_not] at hnot_exp
      rcases hnot_exp with ⟨e_sh, he_sh, hp_ends⟩
      obtain ⟨u, hup, hue⟩ := exists_mem_part_and_ends_of_mem_shrink_ends hp_ends
      have heM : e_sh.1 ∈ M := Finset.mem_subtype.mp he_sh
      have hu_expIn := mem_exposedIn_of_mem_M_of_not_mem_sym2 hM heM
        (not_mem_sym2_of_not_insidePart e_sh.2 p) hup hue
      have hv_expIn : v ∈ exposedIn G p.1 M :=
        Finset.mem_filter.mpr ⟨hvp, fun e heM _ => hv_exp e heM⟩
      have hcard1 := exposedIn_card_eq_one_of_blossomSet hM (C.blossom_sets p.1 p.2)
      have hvu : v = u := Finset.card_le_one.mp (by omega) v hv_expIn u hu_expIn
      subst hvu
      exact hv_exp e_sh.1 heM hue
  have hcompl_eq : Finset.univ \ C.X = C.J.verts.biUnion Subtype.val := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, HungarianConfig.X,
      Finset.mem_filter, not_not, Finset.mem_biUnion, Subtype.exists]
    exact ⟨fun hv => ⟨C.P.part v, C.P.part_mem.2 (Finset.mem_univ v), hv,
      C.P.mem_part (Finset.mem_univ v)⟩,
      fun ⟨U, hU, hv_verts, hvU⟩ => (toPart_eq_iff C.P v ⟨U, hU⟩).mpr hvU ▸ hv_verts⟩
  have hcompl_filt : ((Finset.univ \ C.X).filter (IsExposed G M)).card = 1 := by
    have hbi_eq : (C.J.verts.biUnion Subtype.val).filter (IsExposed G M) =
        C.J.verts.biUnion (fun p => p.1.filter (IsExposed G M)) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_biUnion]
      exact ⟨fun ⟨⟨p, hp, hvp⟩, hexp⟩ => ⟨p, hp, hvp, hexp⟩,
        fun ⟨p, hp, hvp, hexp⟩ => ⟨⟨p, hp, hvp⟩, hexp⟩⟩
    rw [hcompl_eq, hbi_eq]
    have hdisj_biUnion : ((C.J.verts.biUnion (fun p => p.1.filter (IsExposed G M))).card) =
        ∑ p ∈ C.J.verts, (p.1.filter (IsExposed G M)).card := by
      refine Finset.card_biUnion fun p₁ _ p₂ _ hpne => ?_
      rw [Function.onFun]
      exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
        (C.P.disjoint p₁.2 p₂.2 (Subtype.coe_ne_coe.mpr hpne))
    rw [hdisj_biUnion, Finset.sum_congr rfl hpart_exp, ← Finset.sum_filter,
      ← Finset.card_eq_sum_ones]
    have hfilt_root : C.J.verts.filter (fun p => p = toPart C.P C.root) = {toPart C.P C.root} := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_singleton]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ C.planted.2.1, h⟩⟩
    rw [hfilt_root, Finset.card_singleton]
  have huniv_split : (Finset.univ.filter (IsExposed G M)).card =
      (C.X.filter (IsExposed G M)).card + ((Finset.univ \ C.X).filter (IsExposed G M)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_sdiff]
      tauto
    · rw [Finset.disjoint_left]
      intro v hv₁ hv₂
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv₂).1).2 (Finset.mem_filter.mp hv₁).1
  rw [hexpX_eq, huniv_split, hcompl_filt]

end SolPathsTreesFlowersCoverStep58

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (hM : PathsTreesFlowers.Duality.IsMaxMatching G M)
    (C : PathsTreesFlowers.Duality.HungarianConfig G M) :
    (∀ U ∈ C.SJ, PathsTreesFlowers.Duality.IsOddSet U) ∧
    (∀ U ∈ C.SJ, (M.filter (PathsTreesFlowers.Duality.Covers G U)).card =
      PathsTreesFlowers.Duality.capacity U) ∧
    (∀ e ∈ M, G.ends e ∉ C.X.sym2 →
      (C.SJ.filter (fun U => PathsTreesFlowers.Duality.Covers G U e)).card = 1) ∧
    (∀ e : E, (∃ U ∈ C.SJ, PathsTreesFlowers.Duality.Covers G U e) ↔ G.ends e ∉ C.X.sym2) ∧
    PathsTreesFlowers.Duality.IsMaxMatchingIn G
      (PathsTreesFlowers.Duality.induced G C.X)
      (M ∩ PathsTreesFlowers.Duality.edgesWithin G C.X) ∧
    (PathsTreesFlowers.Duality.exposedIn G C.X M).card + 1 =
      (Finset.univ.filter (PathsTreesFlowers.Duality.IsExposed G M)).card ∧
    M.card = PathsTreesFlowers.Duality.capacitySum C.SJ +
      (M ∩ PathsTreesFlowers.Duality.edgesWithin G C.X).card :=
  ⟨SolPathsTreesFlowersCoverStep58.conj1_odd C,
   SolPathsTreesFlowersCoverStep58.conj2_capacity hM.1 C,
   SolPathsTreesFlowersCoverStep58.conj3_unique_cover hM.1 C,
   SolPathsTreesFlowersCoverStep58.conj4_covers_iff C,
   SolPathsTreesFlowersCoverStep58.conj5_maxMatchingIn_X hM C,
   SolPathsTreesFlowersCoverStep58.conj6_exposed hM.1 C,
   SolPathsTreesFlowersCoverStep58.conj7_card hM.1 C⟩
