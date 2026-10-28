-- Prove2me | solution 1 for PathsTreesFlowers.Duality.theorem_4_12
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T09:42:57.236593+00:00
-- url     : https://prove2.me/submissions/0176e09c-8f96-480e-98fa-524778c9d19e

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
import Theorems.Thm_PathsTreesFlowers_Duality_lemma_4_14
import Theorems.Thm_PathsTreesFlowers_Duality_lemma_4_15

namespace SolPathsTreesFlowersTheorem412

set_option linter.unusedSectionVars false

open EdmondsMatching65.Polyhedron (IsMatching)
open PathsTreesFlowers.Duality

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ### Part 1: `blockPartition` characterizations -/

lemma toPart_blockPartition_eq_iff {U : Finset V} {a b : V} :
    toPart (blockPartition U) a = toPart (blockPartition U) b ↔ a = b ∨ (a ∈ U ∧ b ∈ U) := by
  rw [toPart, toPart, Subtype.mk.injEq,
    ← Finpartition.mem_part_iff_part_eq_part _ (Finset.mem_univ a) (Finset.mem_univ b),
    blockPartition, Finpartition.mem_part_ofSetoid_iff_rel]
  change (b = a ∨ (b ∈ U ∧ a ∈ U)) ↔ (a = b ∨ (a ∈ U ∧ b ∈ U))
  tauto

lemma insidePart_blockPartition_iff {G : EdmondsMatching65.Polyhedron.Graph V E}
    {U : Finset V} {e : E} :
    InsidePart G (blockPartition U) e ↔ G.ends e ∈ U.sym2 := by
  rcases Sym2.exists.mp ⟨G.ends e, rfl⟩ with ⟨a, b, hab⟩
  have hne : a ≠ b := by
    rintro rfl
    exact G.loopless e (hab ▸ Sym2.mk_isDiag_iff.mpr rfl)
  unfold InsidePart
  simp only [hab, Finset.mk_mem_sym2_iff]
  rw [← Finpartition.mem_part_iff_exists, blockPartition, Finpartition.mem_part_ofSetoid_iff_rel]
  change (b = a ∨ (b ∈ U ∧ a ∈ U)) ↔ (a ∈ U ∧ b ∈ U)
  exact ⟨fun h => (h.resolve_left hne.symm).symm, fun h => Or.inr h.symm⟩

/-! ### Part 2: Circuit and blossom properties -/

lemma circuit_edge_ends {G : EdmondsMatching65.Polyhedron.Graph V E} {vs : List V} {es : List E}
    (hB : IsCircuit G vs es) (i : ℕ) (hi : i < vs.length) :
    G.ends (es[i]'(hB.2.2.2.1 ▸ hi)) =
      s(vs[i], vs[(i + 1) % vs.length]'(Nat.mod_lt _ (by omega))) := by
  have hmap := congrArg (fun l => l[i]?) hB.2.2.2.2
  have hi_es : i < es.length := hB.2.2.2.1 ▸ hi
  have hi_rot : i < (vs.rotate 1).length := by rw [List.length_rotate]; exact hi
  rw [List.getElem?_map, List.getElem?_eq_getElem hi_es, Option.map_some,
    List.getElem?_zipWith, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi_rot] at hmap
  simp only [Option.some.injEq, List.getElem_rotate] at hmap
  exact hmap

lemma circuit_edge_ends_mem_sym2 {G : EdmondsMatching65.Polyhedron.Graph V E} {vs : List V}
    {es : List E} (hB : IsCircuit G vs es) {e : E} (he : e ∈ es.toFinset) :
    G.ends e ∈ vs.toFinset.sym2 := by
  rw [List.mem_toFinset] at he
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  have hi_vs : i < vs.length := hB.2.2.2.1.symm ▸ hi
  rw [circuit_edge_ends hB i hi_vs, Finset.mk_mem_sym2_iff, List.mem_toFinset, List.mem_toFinset]
  exact ⟨List.getElem_mem _, List.getElem_mem _⟩

lemma circuit_has_matching_half {G : EdmondsMatching65.Polyhedron.Graph V E} {vs : List V}
    {es : List E} (hB : IsCircuit G vs es) (hodd : Odd vs.length) :
    ∃ M₀ : Finset E, M₀ ⊆ es.toFinset ∧ IsMatching G M₀ ∧ 2 * M₀.card + 1 = vs.length := by
  rcases hodd with ⟨k, hk⟩
  have hlen_eq : vs.length = es.length := hB.2.2.2.1
  let emb : Fin k ↪ E :=
    ⟨fun i => es[2 * i.1]'(by omega), fun i j hij => by
      have h1 : 2 * i.1 = 2 * j.1 := (List.Nodup.getElem_inj_iff hB.2.1).mp hij
      apply Fin.ext
      omega⟩
  refine ⟨Finset.univ.map emb, ?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_map.mp he with ⟨i, _, rfl⟩
    exact List.mem_toFinset.mpr (List.getElem_mem _)
  · intro e he f hf hef v hve hvf
    rcases Finset.mem_map.mp he with ⟨i, _, rfl⟩
    rcases Finset.mem_map.mp hf with ⟨j, _, rfl⟩
    have hij : i.1 ≠ j.1 := fun h => hef (congrArg emb (Fin.ext h))
    have hi_lt : 2 * i.1 < vs.length := by omega
    have hj_lt : 2 * j.1 < vs.length := by omega
    have hends_i := circuit_edge_ends hB (2 * i.1) hi_lt
    have hends_j := circuit_edge_ends hB (2 * j.1) hj_lt
    have hmod_i : (2 * i.1 + 1) % vs.length = 2 * i.1 + 1 := Nat.mod_eq_of_lt (by omega)
    have hmod_j : (2 * j.1 + 1) % vs.length = 2 * j.1 + 1 := Nat.mod_eq_of_lt (by omega)
    change v ∈ G.ends (es[2 * i.1]'(by omega)) at hve
    change v ∈ G.ends (es[2 * j.1]'(by omega)) at hvf
    rw [hends_i, Sym2.mem_iff] at hve
    rw [hends_j, Sym2.mem_iff] at hvf
    rcases hve with rfl | rfl <;> rcases hvf with h_eq | h_eq
    · have := (List.Nodup.getElem_inj_iff hB.1).mp h_eq
      omega
    · have := (List.Nodup.getElem_inj_iff hB.1).mp h_eq
      omega
    · have := (List.Nodup.getElem_inj_iff hB.1).mp h_eq
      omega
    · have := (List.Nodup.getElem_inj_iff hB.1).mp h_eq
      omega
  · rw [Finset.card_map, Finset.card_univ, Fintype.card_fin, hk]

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

lemma blossom_matching_covers_erase {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (hM : IsMatching G M) {vs : List V} {es : List E} {b : V}
    (hBl : IsBlossom G M vs es b) :
    ∀ v ∈ vs.toFinset.erase b, ∃ e ∈ M ∩ es.toFinset, v ∈ G.ends e := by
  set U := vs.toFinset
  set MB := M ∩ es.toFinset
  have hMB_match : IsMatching G MB := fun e he f hf =>
    hM e (Finset.mem_inter.mp he).1 f (Finset.mem_inter.mp hf).1
  have hMB_ends : ∀ e ∈ MB, G.ends e ∈ (U.erase b).sym2 := by
    intro e he
    have he_es : e ∈ es.toFinset := (Finset.mem_inter.mp he).2
    have he_U := circuit_edge_ends_mem_sym2 hBl.1 he_es
    have hb_not := hBl.2.2.2.2 e he
    rw [Finset.mem_sym2_iff] at he_U ⊢
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun hxb => hb_not (hxb ▸ hx), he_U x hx⟩
  have hsum_e : ∑ e ∈ MB, ((U.erase b).filter (fun v => v ∈ G.ends e)).card = 2 * MB.card := by
    calc ∑ e ∈ MB, ((U.erase b).filter (fun v => v ∈ G.ends e)).card
        = ∑ _e ∈ MB, 2 :=
          Finset.sum_congr rfl fun e he => card_filter_ends_eq_two_of_mem_sym2 (hMB_ends e he)
      _ = 2 * MB.card := by simp [Nat.mul_comm]
  have hdeg_le : ∀ v ∈ U.erase b, (MB.filter (fun e => v ∈ G.ends e)).card ≤ 1 := by
    intro v _
    refine Finset.card_le_one.mpr fun e₁ he₁ e₂ he₂ => ?_
    simp only [Finset.mem_filter] at he₁ he₂
    by_contra hne
    exact hMB_match e₁ he₁.1 e₂ he₂.1 hne v he₁.2 he₂.2
  obtain ⟨M₀, hM₀_sub, hM₀_match, hM₀_card⟩ := circuit_has_matching_half hBl.1 hBl.2.1
  have hM₀_le : M₀.card ≤ MB.card := hBl.2.2.1.2.2 M₀ hM₀_sub hM₀_match
  have hU_card : U.card = vs.length := List.toFinset_card_of_nodup hBl.1.1
  have hb_U : b ∈ U := List.mem_toFinset.mpr hBl.2.2.2.1
  have herase_card : (U.erase b).card = 2 * M₀.card := by
    have := Finset.card_erase_of_mem hb_U
    omega
  have hsum_v : ∑ v ∈ U.erase b, (MB.filter (fun e => v ∈ G.ends e)).card = 2 * MB.card := by
    rw [sum_card_filter_ends, hsum_e]
  have hsum_le : ∑ v ∈ U.erase b, (MB.filter (fun e => v ∈ G.ends e)).card ≤ (U.erase b).card := by
    calc ∑ v ∈ U.erase b, (MB.filter (fun e => v ∈ G.ends e)).card
        ≤ ∑ _v ∈ U.erase b, 1 := Finset.sum_le_sum hdeg_le
      _ = (U.erase b).card := by simp
  intro v hv
  by_contra hnone
  push Not at hnone
  have hv_zero : (MB.filter (fun e => v ∈ G.ends e)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact hnone
  have hlt : ∑ w ∈ U.erase b, (MB.filter (fun e => w ∈ G.ends e)).card <
      ∑ _w ∈ U.erase b, 1 := by
    refine Finset.sum_lt_sum hdeg_le ⟨v, hv, ?_⟩
    omega
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hlt
  omega

lemma mem_es_of_mem_M_of_mem_erase {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (hM : IsMatching G M) {vs : List V} {es : List E} {b : V}
    (hBl : IsBlossom G M vs es b) {e : E} (heM : e ∈ M) {v : V}
    (hv : v ∈ vs.toFinset.erase b) (hve : v ∈ G.ends e) :
    e ∈ es.toFinset := by
  obtain ⟨g, hg, hvg⟩ := blossom_matching_covers_erase hM hBl v hv
  have hgM : g ∈ M := (Finset.mem_inter.mp hg).1
  have hges : g ∈ es.toFinset := (Finset.mem_inter.mp hg).2
  by_cases heg : e = g
  · exact heg ▸ hges
  · exact False.elim (hM e heM g hgM heg v hve hvg)

lemma eq_b_of_mem_M_of_not_insidePart {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (hM : IsMatching G M) {vs : List V} {es : List E} {b : V}
    (hBl : IsBlossom G M vs es b) {e : E} (heM : e ∈ M)
    (hnot : ¬ InsidePart G (blockPartition vs.toFinset) e)
    {v : V} (hvU : v ∈ vs.toFinset) (hve : v ∈ G.ends e) :
    v = b := by
  by_contra hvb
  have hv_er : v ∈ vs.toFinset.erase b := Finset.mem_erase.mpr ⟨hvb, hvU⟩
  have he_es := mem_es_of_mem_M_of_mem_erase hM hBl heM hv_er hve
  exact hnot (insidePart_blockPartition_iff.mpr (circuit_edge_ends_mem_sym2 hBl.1 he_es))

lemma filter_insidePart_eq_inter_es {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (hM : IsMatching G M) {vs : List V} {es : List E} {b : V}
    (hBl : IsBlossom G M vs es b) :
    M.filter (InsidePart G (blockPartition vs.toFinset)) = M ∩ es.toFinset := by
  ext e
  simp only [Finset.mem_filter, Finset.mem_inter, insidePart_blockPartition_iff]
  constructor
  · rintro ⟨heM, heU⟩
    refine ⟨heM, ?_⟩
    rcases Sym2.exists.mp ⟨G.ends e, rfl⟩ with ⟨x, y, hxy⟩
    have hne : x ≠ y := by
      rintro rfl
      exact G.loopless e (hxy ▸ Sym2.mk_isDiag_iff.mpr rfl)
    rw [hxy, Finset.mk_mem_sym2_iff] at heU
    by_cases hxb : x = b
    · have hyb : y ≠ b := fun h => hne (hxb.trans h.symm)
      exact mem_es_of_mem_M_of_mem_erase hM hBl heM
        (Finset.mem_erase.mpr ⟨hyb, heU.2⟩) (by rw [hxy]; simp)
    · exact mem_es_of_mem_M_of_mem_erase hM hBl heM
        (Finset.mem_erase.mpr ⟨hxb, heU.1⟩) (by rw [hxy]; simp)
  · rintro ⟨heM, he_es⟩
    exact ⟨heM, circuit_edge_ends_mem_sym2 hBl.1 he_es⟩

lemma exposedIn_blossom_eq_singleton {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (hM : IsMatching G M) {vs : List V} {es : List E} {b : V}
    (hBl : IsBlossom G M vs es b) :
    exposedIn G vs.toFinset M = {b} := by
  ext v
  simp only [exposedIn, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hvU, hexp⟩
    by_contra hvb
    obtain ⟨e, he, hve⟩ := blossom_matching_covers_erase hM hBl v (Finset.mem_erase.mpr ⟨hvb, hvU⟩)
    have heM : e ∈ M := (Finset.mem_inter.mp he).1
    have he_es : e ∈ es.toFinset := (Finset.mem_inter.mp he).2
    exact hexp e heM (circuit_edge_ends_mem_sym2 hBl.1 he_es) hve
  · rintro rfl
    refine ⟨List.mem_toFinset.mpr hBl.2.2.2.1, fun e heM heU => ?_⟩
    have he_in : e ∈ M ∩ es.toFinset := by
      rw [← filter_insidePart_eq_inter_es hM hBl]
      exact Finset.mem_filter.mpr ⟨heM, insidePart_blockPartition_iff.mpr heU⟩
    exact hBl.2.2.2.2 e he_in

lemma isMatching_shrinkMatching_blossom {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (hM : IsMatching G M) {vs : List V} {es : List E} {b : V}
    (hBl : IsBlossom G M vs es b) :
    IsMatching (shrink G (blockPartition vs.toFinset))
      (shrinkMatching G (blockPartition vs.toFinset) M) := by
  set P := blockPartition vs.toFinset
  intro e he f hf hef W hWe hWf
  have heM : e.1 ∈ M := Finset.mem_subtype.mp he
  have hfM : f.1 ∈ M := Finset.mem_subtype.mp hf
  have hef1 : e.1 ≠ f.1 := fun h => hef (Subtype.ext h)
  change W ∈ Sym2.map (toPart P) (G.ends e.1) at hWe
  change W ∈ Sym2.map (toPart P) (G.ends f.1) at hWf
  rw [Sym2.mem_map] at hWe hWf
  rcases hWe with ⟨x, hxe, rfl⟩
  rcases hWf with ⟨y, hyf, hxy⟩
  have hxy' := toPart_blockPartition_eq_iff.mp hxy.symm
  rcases hxy' with rfl | ⟨hxU, hyU⟩
  · exact hM e.1 heM f.1 hfM hef1 x hxe hyf
  · have hxb := eq_b_of_mem_M_of_not_insidePart hM hBl heM e.2 hxU hxe
    have hyb := eq_b_of_mem_M_of_not_insidePart hM hBl hfM f.2 hyU hyf
    exact hM e.1 heM f.1 hfM hef1 b (hxb ▸ hxe) (hyb ▸ hyf)

/-! ### Part 3: Connectedness of `induced G vs.toFinset` -/

lemma isConnectedSub_induced_circuit {G : EdmondsMatching65.Polyhedron.Graph V E}
    {vs : List V} {es : List E} (hB : IsCircuit G vs es) :
    IsConnectedSub G (induced G vs.toFinset) := by
  set U := vs.toFinset
  have hlen : 2 ≤ vs.length := hB.2.2.1
  have hv0_mem : vs[0]'(by omega) ∈ U := List.mem_toFinset.mpr (List.getElem_mem _)
  refine ⟨⟨vs[0]'(by omega), hv0_mem⟩, ?_⟩
  have hreach : ∀ (i : ℕ) (hi : i < vs.length),
      Relation.ReflTransGen
        (fun a b => ∃ e ∈ (induced G U).edges, G.ends e = s(a, b))
        (vs[0]'(by omega)) (vs[i]'hi) := by
    intro i
    induction i with
    | zero => intro _; exact .refl
    | succ i ih =>
      intro hi
      have hi' : i < vs.length := by omega
      have hstep : ∃ e ∈ (induced G U).edges, G.ends e = s(vs[i]'hi', vs[i + 1]'hi) := by
        refine ⟨es[i]'(hB.2.2.2.1 ▸ hi'), ?_, ?_⟩
        · simp only [induced, edgesWithin, Finset.mem_filter, Finset.mem_univ, true_and]
          exact circuit_edge_ends_mem_sym2 hB (List.mem_toFinset.mpr (List.getElem_mem _))
        · have hends := circuit_edge_ends hB i hi'
          have hmod : (i + 1) % vs.length = i + 1 := Nat.mod_eq_of_lt hi
          simpa [hmod] using hends
      exact Relation.ReflTransGen.tail (ih hi') hstep
  have hsymm : ∀ {x y : V},
      Relation.ReflTransGen (fun a b => ∃ e ∈ (induced G U).edges, G.ends e = s(a, b)) x y →
      Relation.ReflTransGen (fun a b => ∃ e ∈ (induced G U).edges, G.ends e = s(a, b)) y x := by
    intro x y hxy
    induction hxy using Relation.ReflTransGen.head_induction_on with
    | refl => exact .refl
    | head hst _ ih =>
      rcases hst with ⟨e, he, hends⟩
      exact Relation.ReflTransGen.tail ih ⟨e, he, hends.trans Sym2.eq_swap⟩
  intro u hu w hw
  change u ∈ vs.toFinset at hu
  change w ∈ vs.toFinset at hw
  rw [List.mem_toFinset] at hu hw
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
  exact Relation.ReflTransGen.trans (hsymm (hreach i hi)) (hreach j hj)

/-! ### Part 4: Stem projection into `shrink G (blockPartition vs.toFinset)` -/

lemma zipWith_sym2_map {α β : Type} (f : α → β) (l₁ l₂ : List α) :
    List.zipWith (fun a b => s(a, b)) (l₁.map f) (l₂.map f) =
      (List.zipWith (fun a b => s(a, b)) l₁ l₂).map (Sym2.map f) := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp
    | cons b l₂ =>
      simp [ih]

lemma map_val_pmap_subtype {α : Type} {P : α → Prop} :
    ∀ (l : List α) (hl : ∀ x ∈ l, P x),
      (l.pmap Subtype.mk hl).map Subtype.val = l
  | [], _ => rfl
  | a :: t, hl => congrArg (a :: ·) (map_val_pmap_subtype t (fun x hx => hl x (List.mem_cons_of_mem a hx)))

lemma isChain_pmap_subtype {α : Type} {P : α → Prop} {R : α → α → Prop} :
    ∀ (l : List α) (hl : ∀ x ∈ l, P x),
      l.IsChain R →
      (l.pmap Subtype.mk hl).IsChain (fun a b => R a.1 b.1)
  | [], _, _ => .nil
  | [_], _, _ => .singleton _
  | a :: b :: t, hl, .cons_cons hab hchain =>
    .cons_cons hab (isChain_pmap_subtype (b :: t) (fun x hx => hl x (List.mem_cons_of_mem a hx)) hchain)

lemma flower_stem_in_shrink {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (hM : IsMatching G M)
    {vs : List V} {es : List E} {b : V} {svs : List V} {ses : List E}
    (hF : IsFlower G M vs es b svs ses) :
    ∃ (svs' : List {W : Finset V // W ∈ (blockPartition vs.toFinset).parts})
      (ses' : List {e : E // ¬ InsidePart G (blockPartition vs.toFinset) e}),
      IsStem (shrink G (blockPartition vs.toFinset))
        (shrinkMatching G (blockPartition vs.toFinset) M) svs' ses' ∧
        ∃ u ∈ vs.toFinset, svs'.getLast? = some (toPart (blockPartition vs.toFinset) u) := by
  set U := vs.toFinset
  set P := blockPartition U
  have hBl := hF.1
  have hSt := hF.2.1
  have hPath := hSt.1.1
  have hlen_svs : svs.length = ses.length + 1 := hPath.2.1
  have hses_not_in : ∀ e ∈ ses, ¬ InsidePart G P e := by
    intro e he hin
    rw [insidePart_blockPartition_iff] at hin
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    have hi_svs : i < svs.length := by omega
    have hi_svs1 : i + 1 < svs.length := by omega
    have hi_tail : i < svs.tail.length := by rw [List.length_tail]; omega
    have hmap := congrArg (fun l => l[i]?) hPath.2.2
    rw [List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some,
      List.getElem?_zipWith, List.getElem?_eq_getElem hi_svs,
      List.getElem?_eq_getElem hi_tail, List.getElem_tail] at hmap
    simp only [Option.some.injEq] at hmap
    rw [hmap, Finset.mk_mem_sym2_iff, List.mem_toFinset, List.mem_toFinset] at hin
    have h1 : svs[i]'hi_svs = b := hF.2.2.2 (svs[i]'hi_svs) (List.getElem_mem _) hin.1
    have h2 : svs[i + 1]'hi_svs1 = b := hF.2.2.2 (svs[i + 1]'hi_svs1) (List.getElem_mem _) hin.2
    have h_eq : i = i + 1 := (List.Nodup.getElem_inj_iff hPath.1).mp (h1.trans h2.symm)
    omega
  let svs' := svs.map (toPart P)
  let ses' := ses.pmap Subtype.mk hses_not_in
  refine ⟨svs', ses', ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩, b, List.mem_toFinset.mpr hBl.2.2.2.1, ?_⟩
  · refine hPath.1.map_on fun x hx y hy hxy => ?_
    rcases toPart_blockPartition_eq_iff.mp hxy with rfl | ⟨hxU, hyU⟩
    · rfl
    · rw [List.mem_toFinset] at hxU hyU
      exact (hF.2.2.2 x hx hxU).trans (hF.2.2.2 y hy hyU).symm
  · simp [svs', ses', hPath.2.1]
  · have hses'_ends : ses'.map (shrink G P).ends = (ses.map G.ends).map (Sym2.map (toPart P)) := by
      calc ses'.map (shrink G P).ends
          = (ses'.map Subtype.val).map (fun e => Sym2.map (toPart P) (G.ends e)) := by
            rw [List.map_map]; rfl
        _ = (ses.map G.ends).map (Sym2.map (toPart P)) := by
            rw [map_val_pmap_subtype, List.map_map]; rfl
    rw [hses'_ends, hPath.2.2, ← zipWith_sym2_map, ← List.map_tail]
  · simpa [ses', shrinkMatching, Finset.mem_subtype] using
      isChain_pmap_subtype ses hses_not_in hSt.1.2
  · intro r' hr' e he hr'e
    have hhead : svs'.head? = svs.head?.map (toPart P) := List.head?_map
    rw [hhead, Option.mem_def, Option.map_eq_some_iff] at hr'
    rcases hr' with ⟨r, hr_head, rfl⟩
    have hr_exp := hSt.2.1 r hr_head
    have hr_svs : r ∈ svs := List.mem_of_mem_head? hr_head
    have heM : e.1 ∈ M := Finset.mem_subtype.mp he
    change toPart P r ∈ Sym2.map (toPart P) (G.ends e.1) at hr'e
    rw [Sym2.mem_map] at hr'e
    rcases hr'e with ⟨x, hxe, hxr⟩
    rcases toPart_blockPartition_eq_iff.mp hxr with rfl | ⟨hxU, hrU⟩
    · exact hr_exp e.1 heM hxe
    · have hrb : r = b := hF.2.2.2 r hr_svs (List.mem_toFinset.mp hrU)
      have hxb : x = b := eq_b_of_mem_M_of_not_insidePart hM hBl heM e.2 hxU hxe
      exact hr_exp e.1 heM (hrb.symm ▸ hxb ▸ hxe)
  · intro e' he'
    have hlast : (ses'.map Subtype.val).getLast? = ses.getLast? := by
      rw [map_val_pmap_subtype]
    have he'_val : e'.1 ∈ ses.getLast? := by
      rw [← hlast, List.getLast?_map]
      exact Option.map_eq_some_iff.mpr ⟨e', he', rfl⟩
    exact Finset.mem_subtype.mpr (hSt.2.2 e'.1 he'_val)
  · simp [svs', List.getLast?_map, hF.2.2.1]

end SolPathsTreesFlowersTheorem412

open EdmondsMatching65.Polyhedron (IsMatching)
open PathsTreesFlowers.Duality
open SolPathsTreesFlowersTheorem412

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (hM : EdmondsMatching65.Polyhedron.IsMatching G M)
    (vs : List V) (es : List E) (b : V) (svs : List V) (ses : List E)
    (hF : IsFlower G M vs es b svs ses) :
    IsMaxMatching G M ↔
      IsMaxMatching (shrink G (blockPartition vs.toFinset))
        (shrinkMatching G (blockPartition vs.toFinset) M) := by
  set U := vs.toFinset
  set P := blockPartition U
  have hBl := hF.1
  constructor
  · intro hMax
    refine ⟨isMatching_shrinkMatching_blossom hM hBl, fun M₁ hM₁ => ?_⟩
    obtain ⟨MB, hMB, hM_union⟩ := lemma_4_14 G vs es hBl.1 hBl.2.1 M₁ hM₁
    have hdisj : Disjoint (M₁.map (Function.Embedding.subtype _)) MB := by
      rw [Finset.disjoint_left]
      intro e he₁ heB
      rcases Finset.mem_map.mp he₁ with ⟨e', _, rfl⟩
      exact e'.2 (insidePart_blockPartition_iff.mpr (circuit_edge_ends_mem_sym2 hBl.1 (hMB.1 heB)))
    have hcard_union : (M₁.map (Function.Embedding.subtype _) ∪ MB).card = M₁.card + MB.card := by
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_map]
    have hMB_eq : MB.card = (M ∩ es.toFinset).card :=
      le_antisymm (hBl.2.2.1.2.2 MB hMB.1 hMB.2.1) (hMB.2.2 (M ∩ es.toFinset) hBl.2.2.1.1 hBl.2.2.1.2.1)
    have hM_split : M.card = (shrinkMatching G P M).card + (M ∩ es.toFinset).card := by
      have hpart := (Finset.card_filter_add_card_filter_not (s := M) (p := InsidePart G P)).symm
      rw [filter_insidePart_eq_inter_es hM hBl] at hpart
      have hsub_card : (shrinkMatching G P M).card = (M.filter (fun e => ¬ InsidePart G P e)).card :=
        Finset.card_subtype _ _
      omega
    have hle := hMax.2 (M₁.map (Function.Embedding.subtype _) ∪ MB) hM_union
    omega
  · intro hMax_shrink
    refine lemma_4_15 G M hM U
      (isConnectedSub_induced_circuit hBl.1)
      (by rw [exposedIn_blossom_eq_singleton hM hBl, Finset.card_singleton])
      hMax_shrink
      (flower_stem_in_shrink hM hF)
