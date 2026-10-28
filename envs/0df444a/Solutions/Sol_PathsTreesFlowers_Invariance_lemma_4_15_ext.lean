-- Prove2me | solution 1 for PathsTreesFlowers.Invariance.lemma_4_15_ext
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T11:47:44.85118+00:00
-- url     : https://prove2.me/submissions/98cbd1be-ab68-4507-b1ed-f63b3952466e

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
import Definitions.Def_PathsTreesFlowers_Invariance_Basic
import Definitions.Def_PathsTreesFlowers_Invariance_Shrink
import Theorems.Thm_PathsTreesFlowers_Duality_berge_3_7
import Theorems.Thm_PathsTreesFlowers_Duality_lemma_4_2
import Theorems.Thm_PathsTreesFlowers_Invariance_lemma_4_2

namespace SolPathsTreesFlowersLemma415Ext

set_option linter.unusedSectionVars false

open EdmondsMatching65.Polyhedron (IsMatching)
open PathsTreesFlowers.Invariance

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ### Section 1: Double counting, `splitPart`, and `shrink` helpers -/

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

def splitSetoid (P : Finpartition (Finset.univ : Finset V)) (U : Finset V) : Setoid V where
  r x y := x = y ∨ (P.part x = P.part y ∧ P.part x ≠ U)
  iseqv := ⟨fun _ => Or.inl rfl,
    fun h => by rcases h with rfl | ⟨h1, h2⟩; exacts [Or.inl rfl, Or.inr ⟨h1.symm, h1 ▸ h2⟩],
    fun h1 h2 => by
      rcases h1 with rfl | ⟨h1a, h1b⟩
      · exact h2
      · rcases h2 with rfl | ⟨h2a, _⟩
        · exact Or.inr ⟨h1a, h1b⟩
        · exact Or.inr ⟨h1a.trans h2a, h1b⟩⟩

instance (P : Finpartition (Finset.univ : Finset V)) (U : Finset V) :
    DecidableRel (splitSetoid P U).r := fun x y =>
  show Decidable (x = y ∨ (P.part x = P.part y ∧ P.part x ≠ U)) from inferInstance

def splitPart (P : Finpartition (Finset.univ : Finset V)) (U : Finset V) :
    Finpartition (Finset.univ : Finset V) :=
  Finpartition.ofSetoid (splitSetoid P U)

lemma splitPart_part_of_mem (P : Finpartition (Finset.univ : Finset V)) {U : Finset V}
    (hU : U ∈ P.parts) {x : V} (hx : x ∈ U) :
    (splitPart P U).part x = {x} := by
  have hx_part : P.part x = U :=
    P.eq_of_mem_parts (P.part_mem.2 (Finset.mem_univ x)) hU (P.mem_part (Finset.mem_univ x)) hx
  ext y
  rw [splitPart, Finpartition.mem_part_ofSetoid_iff_rel]
  change (x = y ∨ (P.part x = P.part y ∧ P.part x ≠ U)) ↔ y ∈ ({x} : Finset V)
  simp [hx_part, eq_comm]

lemma splitPart_part_of_not_mem (P : Finpartition (Finset.univ : Finset V)) {U : Finset V}
    {x : V} (hx : x ∉ U) :
    (splitPart P U).part x = P.part x := by
  have hx_ne : P.part x ≠ U := fun h => hx (h ▸ P.mem_part (Finset.mem_univ x))
  ext y
  rw [splitPart, Finpartition.mem_part_ofSetoid_iff_rel]
  change (x = y ∨ (P.part x = P.part y ∧ P.part x ≠ U)) ↔ y ∈ P.part x
  constructor
  · rintro (rfl | ⟨h1, _⟩)
    · exact P.mem_part (Finset.mem_univ x)
    · rw [h1]; exact P.mem_part (Finset.mem_univ y)
  · intro hy
    refine Or.inr ⟨?_, hx_ne⟩
    exact P.eq_of_mem_parts (P.part_mem.2 (Finset.mem_univ x))
      (P.part_mem.2 (Finset.mem_univ y)) hy (P.mem_part (Finset.mem_univ y))

lemma splitPart_parts (P : Finpartition (Finset.univ : Finset V)) {U : Finset V}
    (hU : U ∈ P.parts) :
    (splitPart P U).parts = P.parts.erase U ∪ U.image (fun u => ({u} : Finset V)) := by
  ext W
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_image]
  constructor
  · intro hW
    obtain ⟨x, hxW⟩ := (splitPart P U).nonempty_of_mem_parts hW
    have hpart_x : (splitPart P U).part x = W :=
      (splitPart P U).eq_of_mem_parts ((splitPart P U).part_mem.2 (Finset.mem_univ x)) hW
        ((splitPart P U).mem_part (Finset.mem_univ x)) hxW
    by_cases hxU : x ∈ U
    · refine Or.inr ⟨x, hxU, ?_⟩
      rw [← hpart_x, splitPart_part_of_mem P hU hxU]
    · refine Or.inl ⟨?_, ?_⟩
      · rw [← hpart_x, splitPart_part_of_not_mem P hxU]
        exact fun h => hxU (h ▸ P.mem_part (Finset.mem_univ x))
      · rw [← hpart_x, splitPart_part_of_not_mem P hxU]
        exact P.part_mem.2 (Finset.mem_univ x)
  · rintro (⟨hWU, hWP⟩ | ⟨u, huU, rfl⟩)
    · obtain ⟨x, hxW⟩ := P.nonempty_of_mem_parts hWP
      have hpart_x : P.part x = W :=
        P.eq_of_mem_parts (P.part_mem.2 (Finset.mem_univ x)) hWP
          (P.mem_part (Finset.mem_univ x)) hxW
      have hxU : x ∉ U := fun hxU => hWU (hpart_x.symm.trans
        (P.eq_of_mem_parts (P.part_mem.2 (Finset.mem_univ x)) hU
          (P.mem_part (Finset.mem_univ x)) hxU))
      rw [← hpart_x, ← splitPart_part_of_not_mem P hxU]
      exact (splitPart P U).part_mem.2 (Finset.mem_univ x)
    · rw [← splitPart_part_of_mem P hU huU]
      exact (splitPart P U).part_mem.2 (Finset.mem_univ u)

lemma partOf_eq_iff (P : Finpartition (Finset.univ : Finset V)) (v : V)
    (p : {U : Finset V // U ∈ P.parts}) :
    partOf P v = p ↔ v ∈ p.1 := by
  constructor
  · intro h
    rw [← congrArg Subtype.val h]
    exact P.mem_part (Finset.mem_univ v)
  · intro hv
    exact Subtype.ext (P.eq_of_mem_parts (P.part_mem.2 (Finset.mem_univ v)) p.2
      (P.mem_part (Finset.mem_univ v)) hv)

lemma not_mem_sym2_of_shrinkE {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} (e : ShrinkE G P)
    (p : {U : Finset V // U ∈ P.parts}) : G.ends e.1 ∉ p.1.sym2 := by
  intro h
  apply e.2
  rcases Sym2.exists.mp ⟨G.ends e.1, rfl⟩ with ⟨a, b, hab⟩
  rw [hab, Finset.mk_mem_sym2_iff] at h
  rw [hab, Sym2.map_mk, Sym2.mk_isDiag_iff]
  exact ((partOf_eq_iff P a p).mpr h.1).trans ((partOf_eq_iff P b p).mpr h.2).symm

lemma isDiag_map_partOf_iff {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} (e : E) :
    ((G.ends e).map (partOf P)).IsDiag ↔ ∃ U ∈ P.parts, G.ends e ∈ U.sym2 := by
  rcases Sym2.exists.mp ⟨G.ends e, rfl⟩ with ⟨a, b, hab⟩
  rw [hab, Sym2.map_mk, Sym2.mk_isDiag_iff]
  constructor
  · intro h
    refine ⟨P.part a, P.part_mem.2 (Finset.mem_univ a), ?_⟩
    have hba : P.part a = P.part b := congrArg Subtype.val h
    rw [Finset.mk_mem_sym2_iff, hba]
    exact ⟨hba ▸ P.mem_part (Finset.mem_univ a), P.mem_part (Finset.mem_univ b)⟩
  · rintro ⟨U, hU, heU⟩
    rw [Finset.mk_mem_sym2_iff] at heU
    exact ((partOf_eq_iff P a ⟨U, hU⟩).mpr heU.1).trans
      ((partOf_eq_iff P b ⟨U, hU⟩).mpr heU.2).symm

lemma exists_mem_part_and_ends_of_mem_shrink_ends {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {e : ShrinkE G P}
    {p : {U : Finset V // U ∈ P.parts}} (hp : p ∈ (shrink G P).ends e) :
    ∃ v ∈ p.1, v ∈ G.ends e.1 := by
  change p ∈ (G.ends e.1).map (partOf P) at hp
  rcases Sym2.mem_map.mp hp with ⟨v, hve, hvp⟩
  exact ⟨v, (partOf_eq_iff P v p).mp hvp, hve⟩

/-! ### Section 2: Projection from `splitPart P U` to `P` and single-part expansion -/

def projSplit (P : Finpartition (Finset.univ : Finset V)) {U : Finset V} (hU : U ∈ P.parts)
    (w : {W : Finset V // W ∈ (splitPart P U).parts}) : {W : Finset V // W ∈ P.parts} :=
  if h : w.1 ∈ P.parts then ⟨w.1, h⟩ else ⟨U, hU⟩

lemma projSplit_partOf (P : Finpartition (Finset.univ : Finset V)) {U : Finset V}
    (hU : U ∈ P.parts) (x : V) :
    projSplit P hU (partOf (splitPart P U) x) = partOf P x := by
  dsimp [projSplit, partOf]
  split_ifs with h
  · by_cases hxU : x ∈ U
    · have hsing : (splitPart P U).part x = {x} := splitPart_part_of_mem P hU hxU
      have hx_mem : x ∈ (splitPart P U).part x := (splitPart P U).mem_part (Finset.mem_univ x)
      have h_eq : (splitPart P U).part x = P.part x :=
        P.eq_of_mem_parts h (P.part_mem.2 (Finset.mem_univ x)) hx_mem (P.mem_part (Finset.mem_univ x))
      exact Subtype.ext h_eq
    · exact Subtype.ext (splitPart_part_of_not_mem P hxU)
  · by_cases hxU : x ∈ U
    · have h_eq : U = P.part x :=
        P.eq_of_mem_parts hU (P.part_mem.2 (Finset.mem_univ x)) hxU (P.mem_part (Finset.mem_univ x))
      exact Subtype.ext h_eq
    · exfalso
      apply h
      rw [splitPart_part_of_not_mem P hxU]
      exact P.part_mem.2 (Finset.mem_univ x)

def uTilde (P : Finpartition (Finset.univ : Finset V)) {U : Finset V} (hU : U ∈ P.parts) :
    Finset {W : Finset V // W ∈ (splitPart P U).parts} :=
  Finset.univ.filter (fun w => projSplit P hU w = ⟨U, hU⟩)

lemma mem_uTilde_iff {P : Finpartition (Finset.univ : Finset V)} {U : Finset V}
    (hU : U ∈ P.parts) {w : {W : Finset V // W ∈ (splitPart P U).parts}} :
    w ∈ uTilde P hU ↔ projSplit P hU w = ⟨U, hU⟩ := by
  simp [uTilde]

lemma partOf_splitPart_mem_uTilde_iff {P : Finpartition (Finset.univ : Finset V)} {U : Finset V}
    (hU : U ∈ P.parts) {x : V} :
    partOf (splitPart P U) x ∈ uTilde P hU ↔ x ∈ U := by
  rw [mem_uTilde_iff, projSplit_partOf, partOf_eq_iff]

lemma projSplit_eq_iff {P : Finpartition (Finset.univ : Finset V)} {U : Finset V}
    (hU : U ∈ P.parts) {a b : {W : Finset V // W ∈ (splitPart P U).parts}} :
    projSplit P hU a = projSplit P hU b ↔ a = b ∨ (a ∈ uTilde P hU ∧ b ∈ uTilde P hU) := by
  rw [mem_uTilde_iff, mem_uTilde_iff]
  constructor
  · intro h
    by_cases ha : projSplit P hU a = ⟨U, hU⟩
    · exact Or.inr ⟨ha, h.symm.trans ha⟩
    · left
      have hb : projSplit P hU b ≠ ⟨U, hU⟩ := h ▸ ha
      dsimp [projSplit] at ha hb h
      split_ifs at ha with haP
      swap; · exact False.elim (ha rfl)
      split_ifs at hb with hbP
      swap; · exact False.elim (hb rfl)
      rw [dif_pos haP, dif_pos hbP, Subtype.mk.injEq] at h
      exact Subtype.ext h
  · rintro (rfl | ⟨ha, hb⟩)
    · rfl
    · exact ha.trans hb.symm

lemma not_isDiag_splitPart_of_not_isDiag {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {U : Finset V} (hU : U ∈ P.parts)
    {e : E} (he : ¬ ((G.ends e).map (partOf P)).IsDiag) :
    ¬ ((G.ends e).map (partOf (splitPart P U))).IsDiag := by
  intro hdiag
  apply he
  rcases Sym2.exists.mp ⟨G.ends e, rfl⟩ with ⟨a, b, hab⟩
  rw [hab, Sym2.map_mk, Sym2.mk_isDiag_iff] at hdiag ⊢
  rw [← projSplit_partOf P hU a, ← projSplit_partOf P hU b, hdiag]

lemma not_isDiag_splitPart_of_mem_sym2 {G : EdmondsMatching65.Polyhedron.Graph V E}
    (P : Finpartition (Finset.univ : Finset V)) {U : Finset V} (hU : U ∈ P.parts)
    {e : E} (he : G.ends e ∈ U.sym2) :
    ¬ ((G.ends e).map (partOf (splitPart P U))).IsDiag := by
  rcases Sym2.exists.mp ⟨G.ends e, rfl⟩ with ⟨a, b, hab⟩
  have hne : a ≠ b := by
    rintro rfl
    exact G.loopless e (hab ▸ Sym2.mk_isDiag_iff.mpr rfl)
  rw [hab, Finset.mk_mem_sym2_iff] at he
  rw [hab, Sym2.map_mk, Sym2.mk_isDiag_iff, Subtype.ext_iff]
  change (splitPart P U).part a ≠ (splitPart P U).part b
  rw [splitPart_part_of_mem P hU he.1, splitPart_part_of_mem P hU he.2]
  intro h
  exact hne (Finset.singleton_injective h)

lemma isDiag_map_partOf_iff_mem_uTilde_sym2 {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {U : Finset V} (hU : U ∈ P.parts)
    (e : ShrinkE G (splitPart P U)) :
    ((G.ends e.1).map (partOf P)).IsDiag ↔
      (shrink G (splitPart P U)).ends e ∈ (uTilde P hU).sym2 := by
  rcases Sym2.exists.mp ⟨G.ends e.1, rfl⟩ with ⟨a, b, hab⟩
  have hne_sp : partOf (splitPart P U) a ≠ partOf (splitPart P U) b := by
    intro h
    apply e.2
    rw [hab, Sym2.map_mk, Sym2.mk_isDiag_iff]
    exact h
  change ((G.ends e.1).map (partOf P)).IsDiag ↔
    (G.ends e.1).map (partOf (splitPart P U)) ∈ (uTilde P hU).sym2
  rw [hab, Sym2.map_mk, Sym2.map_mk, Sym2.mk_isDiag_iff, Finset.mk_mem_sym2_iff,
    ← projSplit_partOf P hU a, ← projSplit_partOf P hU b, projSplit_eq_iff]
  exact ⟨fun h => h.resolve_left hne_sp, fun h => Or.inr h⟩

lemma mem_uTilde_sym2_iff_mem_U_sym2 {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {U : Finset V} (hU : U ∈ P.parts)
    (e : ShrinkE G (splitPart P U)) :
    (shrink G (splitPart P U)).ends e ∈ (uTilde P hU).sym2 ↔ G.ends e.1 ∈ U.sym2 := by
  rcases Sym2.exists.mp ⟨G.ends e.1, rfl⟩ with ⟨a, b, hab⟩
  change (G.ends e.1).map (partOf (splitPart P U)) ∈ (uTilde P hU).sym2 ↔ G.ends e.1 ∈ U.sym2
  rw [hab, Sym2.map_mk, Finset.mk_mem_sym2_iff, Finset.mk_mem_sym2_iff,
    partOf_splitPart_mem_uTilde_iff, partOf_splitPart_mem_uTilde_iff]

def toShrinkEP {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {U : Finset V} (hU : U ∈ P.parts)
    (e : ShrinkE G (splitPart P U))
    (he : (shrink G (splitPart P U)).ends e ∉ (uTilde P hU).sym2) : ShrinkE G P :=
  ⟨e.1, fun hdiag => he ((isDiag_map_partOf_iff_mem_uTilde_sym2 hU e).mp hdiag)⟩

def fromShrinkEP {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {U : Finset V} (hU : U ∈ P.parts)
    (e : ShrinkE G P) : ShrinkE G (splitPart P U) :=
  ⟨e.1, not_isDiag_splitPart_of_not_isDiag hU e.2⟩

def projSplitMatching {G : EdmondsMatching65.Polyhedron.Graph V E}
    (P : Finpartition (Finset.univ : Finset V)) {U : Finset V} (hU : U ∈ P.parts)
    (K : Finset (ShrinkE G (splitPart P U))) : Finset (ShrinkE G P) :=
  Finset.univ.filter (fun e : ShrinkE G P => fromShrinkEP hU e ∈ K)

lemma shrink_ends_eq_map_projSplit {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {U : Finset V} (hU : U ∈ P.parts)
    (e : ShrinkE G P) :
    (shrink G P).ends e =
      ((shrink G (splitPart P U)).ends (fromShrinkEP hU e)).map (projSplit P hU) := by
  rcases Sym2.exists.mp ⟨G.ends e.1, rfl⟩ with ⟨a, b, hab⟩
  change (G.ends e.1).map (partOf P) =
    ((G.ends e.1).map (partOf (splitPart P U))).map (projSplit P hU)
  rw [hab, Sym2.map_mk, Sym2.map_mk, Sym2.map_mk, projSplit_partOf, projSplit_partOf]

lemma fromShrinkEP_toShrinkEP {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {U : Finset V} (hU : U ∈ P.parts)
    (e : ShrinkE G (splitPart P U))
    (he : (shrink G (splitPart P U)).ends e ∉ (uTilde P hU).sym2) :
    fromShrinkEP hU (toShrinkEP hU e he) = e := rfl

lemma toShrinkEP_fromShrinkEP {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {U : Finset V} (hU : U ∈ P.parts)
    (e : ShrinkE G P)
    (he : (shrink G (splitPart P U)).ends (fromShrinkEP hU e) ∉ (uTilde P hU).sym2) :
    toShrinkEP hU (fromShrinkEP hU e) he = e := rfl

lemma fromShrinkEP_ends_not_mem_uTilde_sym2 {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {U : Finset V} (hU : U ∈ P.parts)
    (e : ShrinkE G P) :
    (shrink G (splitPart P U)).ends (fromShrinkEP hU e) ∉ (uTilde P hU).sym2 :=
  fun h => e.2 ((isDiag_map_partOf_iff_mem_uTilde_sym2 hU (fromShrinkEP hU e)).mpr h)

lemma mem_projSplitMatching_iff {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {U : Finset V} (hU : U ∈ P.parts)
    {K : Finset (ShrinkE G (splitPart P U))} {e : ShrinkE G P} :
    e ∈ projSplitMatching P hU K ↔ fromShrinkEP hU e ∈ K := by
  simp [projSplitMatching]

lemma projSplitMatching_shrinkMatching {G : EdmondsMatching65.Polyhedron.Graph V E}
    (P : Finpartition (Finset.univ : Finset V)) {U : Finset V} (hU : U ∈ P.parts)
    (M : Finset E) :
    projSplitMatching P hU (shrinkMatching G (splitPart P U) M) = shrinkMatching G P M := by
  ext e
  simp [projSplitMatching, shrinkMatching, fromShrinkEP, Finset.mem_subtype]

lemma projSplitMatching_insert_erase {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {U : Finset V} (hU : U ∈ P.parts)
    {K : Finset (ShrinkE G (splitPart P U))} (e_add e_rem : ShrinkE G P) :
    projSplitMatching P hU (insert (fromShrinkEP hU e_add) (K.erase (fromShrinkEP hU e_rem))) =
      insert e_add ((projSplitMatching P hU K).erase e_rem) := by
  ext e
  have hinj : ∀ a b : ShrinkE G P, fromShrinkEP hU a = fromShrinkEP hU b ↔ a = b := by
    intro a b
    simp [fromShrinkEP, Subtype.ext_iff]
  simp [projSplitMatching, hinj]

/-! ### Section 3: Matching swap and alternating path helpers -/

lemma not_mem_of_isExposed {V₁ E₁ : Type} [Fintype V₁] [DecidableEq V₁] [Fintype E₁] [DecidableEq E₁]
    {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁} {M : Finset E₁}
    {e : E₁} {u : V₁} (hu_end : u ∈ G₁.ends e)
    (hu_exp : PathsTreesFlowers.Duality.IsExposed G₁ M u) :
    e ∉ M :=
  fun he => hu_exp e he hu_end

lemma isMatching_erase {V₁ E₁ : Type} [Fintype V₁] [DecidableEq V₁] [Fintype E₁] [DecidableEq E₁]
    {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁} {M : Finset E₁}
    (hM : IsMatching G₁ M) (e : E₁) :
    IsMatching G₁ (M.erase e) := by
  intro e₁ he₁ e₂ he₂ hne v hv₁ hv₂
  exact hM e₁ (Finset.mem_erase.mp he₁).2 e₂ (Finset.mem_erase.mp he₂).2 hne v hv₁ hv₂

lemma isExposed_erase_of_isExposed {V₁ E₁ : Type} [Fintype V₁] [DecidableEq V₁] [Fintype E₁] [DecidableEq E₁]
    {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁} {M : Finset E₁}
    {v : V₁} (hv : PathsTreesFlowers.Duality.IsExposed G₁ M v) (e : E₁) :
    PathsTreesFlowers.Duality.IsExposed G₁ (M.erase e) v := by
  intro f hf
  exact hv f (Finset.mem_erase.mp hf).2

lemma isExposed_erase_of_mem_ends {V₁ E₁ : Type} [Fintype V₁] [DecidableEq V₁] [Fintype E₁] [DecidableEq E₁]
    {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁} {M : Finset E₁}
    (hM : IsMatching G₁ M) {e : E₁} (he : e ∈ M) {v : V₁} (hv : v ∈ G₁.ends e) :
    PathsTreesFlowers.Duality.IsExposed G₁ (M.erase e) v := by
  intro f hf hvf
  have hne : f ≠ e := (Finset.mem_erase.mp hf).1
  have hfM : f ∈ M := (Finset.mem_erase.mp hf).2
  exact hM e he f hfM hne.symm v hv hvf

lemma isMatching_insert_of_isExposed {V₁ E₁ : Type} [Fintype V₁] [DecidableEq V₁] [Fintype E₁] [DecidableEq E₁]
    {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁} {M : Finset E₁}
    (hM : IsMatching G₁ M) {e : E₁} {u v : V₁} (hends : G₁.ends e = s(u, v))
    (hu : PathsTreesFlowers.Duality.IsExposed G₁ M u)
    (hv : PathsTreesFlowers.Duality.IsExposed G₁ M v) :
    e ∉ M ∧ IsMatching G₁ (insert e M) ∧ (insert e M).card = M.card + 1 := by
  have hu_end : u ∈ G₁.ends e := by rw [hends]; simp
  have he_not : e ∉ M := not_mem_of_isExposed hu_end hu
  refine ⟨he_not, ?_, Finset.card_insert_of_notMem he_not⟩
  intro e₁ he₁ e₂ he₂ hne x hx₁ hx₂
  rcases Finset.mem_insert.mp he₁ with rfl | he₁M <;>
    rcases Finset.mem_insert.mp he₂ with rfl | he₂M
  · exact hne rfl
  · rw [hends, Sym2.mem_iff] at hx₁
    rcases hx₁ with rfl | rfl
    · exact hu e₂ he₂M hx₂
    · exact hv e₂ he₂M hx₂
  · rw [hends, Sym2.mem_iff] at hx₂
    rcases hx₂ with rfl | rfl
    · exact hu e₁ he₁M hx₁
    · exact hv e₁ he₁M hx₁
  · exact hM e₁ he₁M e₂ he₂M hne x hx₁ hx₂

lemma isExposed_insert_of_ne {V₁ E₁ : Type} [Fintype V₁] [DecidableEq V₁] [Fintype E₁] [DecidableEq E₁]
    {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁} {M : Finset E₁}
    {e : E₁} {u v w : V₁} (hends : G₁.ends e = s(u, v))
    (hwu : w ≠ u) (hwv : w ≠ v) (hw : PathsTreesFlowers.Duality.IsExposed G₁ M w) :
    PathsTreesFlowers.Duality.IsExposed G₁ (insert e M) w := by
  intro f hf hwf
  rcases Finset.mem_insert.mp hf with rfl | hfM
  · rw [hends, Sym2.mem_iff] at hwf
    rcases hwf with rfl | rfl
    · exact hwu rfl
    · exact hwv rfl
  · exact hw f hfM hwf

lemma swap_matching {V₁ E₁ : Type} [Fintype V₁] [DecidableEq V₁] [Fintype E₁] [DecidableEq E₁]
    {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁} {K : Finset E₁}
    (hK : IsMatching G₁ K) {e_rem e_add : E₁} {x y z : V₁}
    (he_rem : e_rem ∈ K) (hends_rem : G₁.ends e_rem = s(x, y))
    (hends_add : G₁.ends e_add = s(y, z))
    (hz : PathsTreesFlowers.Duality.IsExposed G₁ K z) :
    IsMatching G₁ (insert e_add (K.erase e_rem)) ∧
      (insert e_add (K.erase e_rem)).card = K.card ∧
      (x ≠ y → x ≠ z → PathsTreesFlowers.Duality.IsExposed G₁ (insert e_add (K.erase e_rem)) x) ∧
      (∀ w : V₁, w ≠ y → w ≠ z → PathsTreesFlowers.Duality.IsExposed G₁ K w →
        PathsTreesFlowers.Duality.IsExposed G₁ (insert e_add (K.erase e_rem)) w) := by
  have hK_er : IsMatching G₁ (K.erase e_rem) := isMatching_erase hK e_rem
  have hy_end : y ∈ G₁.ends e_rem := by rw [hends_rem]; simp
  have hx_end : x ∈ G₁.ends e_rem := by rw [hends_rem]; simp
  have hy_exp : PathsTreesFlowers.Duality.IsExposed G₁ (K.erase e_rem) y :=
    isExposed_erase_of_mem_ends hK he_rem hy_end
  have hx_exp : PathsTreesFlowers.Duality.IsExposed G₁ (K.erase e_rem) x :=
    isExposed_erase_of_mem_ends hK he_rem hx_end
  have hz_exp : PathsTreesFlowers.Duality.IsExposed G₁ (K.erase e_rem) z :=
    isExposed_erase_of_isExposed hz e_rem
  obtain ⟨_, hK', hcard'⟩ :=
    isMatching_insert_of_isExposed hK_er hends_add hy_exp hz_exp
  have hcard_er : (K.erase e_rem).card + 1 = K.card := Finset.card_erase_add_one he_rem
  refine ⟨hK', hcard'.trans hcard_er, ?_, ?_⟩
  · intro hxy hxz
    exact isExposed_insert_of_ne hends_add hxy hxz hx_exp
  · intro w hwy hwz hw
    exact isExposed_insert_of_ne hends_add hwy hwz (isExposed_erase_of_isExposed hw e_rem)

lemma isChain_congr {α : Type*} {R S : α → α → Prop} :
    ∀ (L : List α), (∀ x ∈ L, ∀ y ∈ L, R x y → S x y) → L.IsChain R → L.IsChain S
  | [], _, _ => List.IsChain.nil
  | [a], _, _ => List.isChain_singleton a
  | a :: b :: t, h, List.IsChain.cons_cons hab hchain =>
    List.IsChain.cons_cons (h a (by simp) b (by simp) hab)
      (isChain_congr (b :: t)
        (fun x hx y hy => h x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy)) hchain)

lemma mem_zipWith_tail_ends {V₁ : Type} : ∀ (L : List V₁) (p : Sym2 V₁),
    p ∈ List.zipWith (fun a b => s(a, b)) L L.tail → ∀ v ∈ p, v ∈ L
  | [], _, hp => by cases hp
  | [_], _, hp => by cases hp
  | a :: b :: t, p, hp => by
    simp only [List.tail_cons, List.zipWith_cons_cons, List.mem_cons] at hp
    intro v hv
    rcases hp with rfl | hp
    · rw [Sym2.mem_iff] at hv
      rcases hv with rfl | rfl <;> simp
    · exact List.mem_cons_of_mem a (mem_zipWith_tail_ends (b :: t) p hp v hv)

lemma ends_mem_verts_of_isPath {V₁ E₁ : Type} [Fintype V₁] [DecidableEq V₁] [Fintype E₁] [DecidableEq E₁]
    {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁} {vs : List V₁} {es : List E₁}
    (hpath : PathsTreesFlowers.Duality.IsPath G₁ vs es) {e : E₁} (he : e ∈ es) {v : V₁}
    (hv : v ∈ G₁.ends e) :
    v ∈ vs := by
  have hmap : G₁.ends e ∈ List.zipWith (fun a b => s(a, b)) vs vs.tail := by
    rw [← hpath.2.2]
    exact List.mem_map_of_mem he
  exact mem_zipWith_tail_ends vs (G₁.ends e) hmap v hv

lemma zipWith_tail_append_singleton {V₁ : Type} : ∀ (vs : List V₁) (b w : V₁),
    vs.getLast? = some b →
    List.zipWith (fun x y => s(x, y)) (vs ++ [w]) (vs ++ [w]).tail =
      List.zipWith (fun x y => s(x, y)) vs vs.tail ++ [s(b, w)]
  | [], _, _, h => by cases h
  | [x], b, w, h => by
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    subst h; rfl
  | x :: y :: t, b, w, h => by
    have h' : (y :: t).getLast? = some b := by simpa using h
    exact congrArg (s(x, y) :: ·) (zipWith_tail_append_singleton (y :: t) b w h')

lemma isChain_append_singleton {α : Type*} (R : α → α → Prop) :
    ∀ (es : List α) (e_last f : α),
      es.IsChain R → es.getLast? = some e_last → R e_last f → (es ++ [f]).IsChain R
  | [], _, _, _, h, _ => by cases h
  | [x], e_last, f, _, h, hR => by
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    subst h
    exact List.IsChain.cons_cons hR (List.isChain_singleton f)
  | x :: y :: t, e_last, f, hchain, hlast, hR => by
    cases hchain with
    | cons_cons hxy hchain' =>
      have hlast' : (y :: t).getLast? = some e_last := by simpa using hlast
      exact List.IsChain.cons_cons hxy (isChain_append_singleton R (y :: t) e_last f hchain' hlast' hR)

lemma zipWith_sym2_reverse {V₁ : Type} : ∀ (vs : List V₁),
    List.zipWith (fun a b => s(a, b)) vs.reverse vs.reverse.tail =
      (List.zipWith (fun a b => s(a, b)) vs vs.tail).reverse
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
    have hlast : (b :: t).reverse.getLast? = some b := by simp
    calc List.zipWith (fun x y => s(x, y)) (a :: b :: t).reverse (a :: b :: t).reverse.tail
        = List.zipWith (fun x y => s(x, y)) ((b :: t).reverse ++ [a]) ((b :: t).reverse ++ [a]).tail := by
          simp
      _ = List.zipWith (fun x y => s(x, y)) (b :: t).reverse (b :: t).reverse.tail ++ [s(b, a)] :=
          zipWith_tail_append_singleton (b :: t).reverse b a hlast
      _ = (List.zipWith (fun x y => s(x, y)) (b :: t) (b :: t).tail).reverse ++ [s(a, b)] := by
          rw [zipWith_sym2_reverse (b :: t), Sym2.eq_swap]
      _ = (List.zipWith (fun x y => s(x, y)) (a :: b :: t) (a :: b :: t).tail).reverse := by
          simp

lemma isChain_reverse_symm {α : Type*} {R : α → α → Prop} (hsymm : ∀ x y, R x y → R y x) :
    ∀ (es : List α), es.IsChain R → es.reverse.IsChain R
  | [], _ => .nil
  | [a], _ => .singleton a
  | a :: b :: t, .cons_cons hab hchain => by
    have hlast : (b :: t).reverse.getLast? = some b := by simp
    simpa using isChain_append_singleton R (b :: t).reverse b a
      (isChain_reverse_symm hsymm (b :: t) hchain) hlast (hsymm a b hab)

lemma isAlternatingPath_reverse {V₁ E₁ : Type} [Fintype V₁] [DecidableEq V₁] [Fintype E₁] [DecidableEq E₁]
    {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁}
    {M : Finset E₁} {vs : List V₁} {es : List E₁}
    (hAlt : PathsTreesFlowers.Duality.IsAlternatingPath G₁ M vs es) :
    PathsTreesFlowers.Duality.IsAlternatingPath G₁ M vs.reverse es.reverse := by
  refine ⟨⟨List.nodup_reverse.mpr hAlt.1.1, by simp [hAlt.1.2.1], ?_⟩, ?_⟩
  · rw [List.map_reverse, hAlt.1.2.2, zipWith_sym2_reverse]
  · exact isChain_reverse_symm (fun x y h => by tauto) es hAlt.2

/-! ### Section 4: Single-part unshrinking (`isMaxMatching_splitPart_of_stem`) -/

lemma ends_not_mem_uTilde_sym2_of_not_mem {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {U : Finset V} (hU : U ∈ P.parts)
    {e : ShrinkE G (splitPart P U)} {x : {W : Finset V // W ∈ (splitPart P U).parts}}
    (hx : x ∉ uTilde P hU) (hxe : x ∈ (shrink G (splitPart P U)).ends e) :
    (shrink G (splitPart P U)).ends e ∉ (uTilde P hU).sym2 := by
  rw [Finset.mem_sym2_iff]
  intro h
  exact hx (h x hxe)

lemma isExposed_projSplit_of_not_mem_uTilde {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {U : Finset V} (hU : U ∈ P.parts)
    {K : Finset (ShrinkE G (splitPart P U))} {x : {W : Finset V // W ∈ (splitPart P U).parts}}
    (hx : x ∉ uTilde P hU)
    (hx_exp : PathsTreesFlowers.Duality.IsExposed (shrink G (splitPart P U)) K x) :
    PathsTreesFlowers.Duality.IsExposed (shrink G P) (projSplitMatching P hU K)
      (projSplit P hU x) := by
  intro e he hxe
  have heK : fromShrinkEP hU e ∈ K := (mem_projSplitMatching_iff hU).mp he
  rw [shrink_ends_eq_map_projSplit hU e, Sym2.mem_map] at hxe
  rcases hxe with ⟨y, hye, hyx⟩
  rcases (projSplit_eq_iff hU).mp hyx with rfl | ⟨_, hx'⟩
  · exact hx_exp (fromShrinkEP hU e) heK hye
  · exact hx hx'

lemma no_aug_path_from_outside_uTilde {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {U : Finset V} (hU : U ∈ P.parts)
    {u : {W : Finset V // W ∈ (splitPart P U).parts}} (hu : u ∈ uTilde P hU) :
    ∀ (vs : List {W : Finset V // W ∈ (splitPart P U).parts})
      (es : List (ShrinkE G (splitPart P U)))
      (K : Finset (ShrinkE G (splitPart P U))),
      IsMatching (shrink G (splitPart P U)) K →
      PathsTreesFlowers.Duality.IsAlternatingPath (shrink G (splitPart P U)) K vs es →
      es ≠ [] →
      (∀ a ∈ vs.head?, a ∉ uTilde P hU ∧
        PathsTreesFlowers.Duality.IsExposed (shrink G (splitPart P U)) K a) →
      (∀ b ∈ vs.getLast?,
        PathsTreesFlowers.Duality.IsExposed (shrink G (splitPart P U)) K b) →
      PathsTreesFlowers.Duality.IsMaxMatching (shrink G P) (projSplitMatching P hU K) →
      PathsTreesFlowers.Duality.IsExposed (shrink G P) (projSplitMatching P hU K)
        (projSplit P hU u) →
      False
  | _, [], _, _, _, hes, _, _, _, _ => hes rfl
  | [], _ :: _, _, _, hAlt, _, _, _, _, _ => by
    have := hAlt.1.2.1; simp at this
  | [_], _ :: _, _, _, hAlt, _, _, _, _, _ => by
    have := hAlt.1.2.1; simp at this
  | [v₀, v₁], [e₀], K, _hK, hAlt, _, ha, hb, hMax_sh, hu_exp => by
    have hends : (shrink G (splitPart P U)).ends e₀ = s(v₀, v₁) := by simpa using hAlt.1.2.2
    obtain ⟨hv₀_not_U, hv₀_exp⟩ := ha v₀ (by simp)
    have hv₁_exp := hb v₁ (by simp)
    have he₀_not_in := ends_not_mem_uTilde_sym2_of_not_mem hU hv₀_not_U (by rw [hends]; simp)
    let e₀' : ShrinkE G P := toShrinkEP hU e₀ he₀_not_in
    have hends_sh : (shrink G P).ends e₀' = s(projSplit P hU v₀, projSplit P hU v₁) := by
      rw [shrink_ends_eq_map_projSplit hU e₀', fromShrinkEP_toShrinkEP, hends, Sym2.map_mk]
    have hv₀_sh_exp := isExposed_projSplit_of_not_mem_uTilde hU hv₀_not_U hv₀_exp
    have hv₁_sh_exp :
        PathsTreesFlowers.Duality.IsExposed (shrink G P) (projSplitMatching P hU K)
          (projSplit P hU v₁) := by
      by_cases hv₁U : v₁ ∈ uTilde P hU
      · have h_eq : projSplit P hU v₁ = projSplit P hU u :=
          (projSplit_eq_iff hU).mpr (Or.inr ⟨hv₁U, hu⟩)
        exact h_eq ▸ hu_exp
      · exact isExposed_projSplit_of_not_mem_uTilde hU hv₁U hv₁_exp
    obtain ⟨_, hM'_sh, hcard'_sh⟩ :=
      isMatching_insert_of_isExposed hMax_sh.1 hends_sh hv₀_sh_exp hv₁_sh_exp
    have hle := hMax_sh.2 (insert e₀' (projSplitMatching P hU K)) hM'_sh
    omega
  | [_, _], _ :: _ :: _, _, _, hAlt, _, _, _, _, _ => by
    have := hAlt.1.2.1; simp at this
  | _ :: _ :: _ :: _, [_], _, _, hAlt, _, _, _, _, _ => by
    have := hAlt.1.2.1; simp at this
  | [v₀, v₁, v₂], [e₀, e₁], K, _hK, hAlt, _, ha, hb, _, _ => by
    have hmap := hAlt.1.2.2
    simp only [List.map, List.tail_cons, List.zipWith, List.cons.injEq, and_true] at hmap
    rcases hmap with ⟨hends₀, hends₁⟩
    obtain ⟨_, hv₀_exp⟩ := ha v₀ (by simp)
    have hv₂_exp := hb v₂ (by simp)
    have he₀_not : e₀ ∉ K := not_mem_of_isExposed (by rw [hends₀]; simp) hv₀_exp
    cases hAlt.2 with
    | cons_cons h01 _ =>
      have he₁_mem : e₁ ∈ K := by tauto
      exact hv₂_exp e₁ he₁_mem (by rw [hends₁]; simp)
  | _ :: _ :: _ :: _ :: _, [_, _], _, _, hAlt, _, _, _, _, _ => by
    have := hAlt.1.2.1; simp at this
  | v₀ :: v₁ :: v₂ :: vs', e₀ :: e₁ :: e₂ :: es', K, hK, hAlt, _, ha, hb, hMax_sh, hu_exp => by
    have hmap := hAlt.1.2.2
    simp only [List.map_cons, List.tail_cons, List.zipWith_cons_cons, List.cons.injEq] at hmap
    rcases hmap with ⟨hends₀, hends₁, hmap'⟩
    obtain ⟨hv₀_not_U, hv₀_exp⟩ := ha v₀ (by simp)
    have he₀_not_in := ends_not_mem_uTilde_sym2_of_not_mem hU hv₀_not_U (by rw [hends₀]; simp)
    let e₀' : ShrinkE G P := toShrinkEP hU e₀ he₀_not_in
    have hends₀_sh : (shrink G P).ends e₀' = s(projSplit P hU v₀, projSplit P hU v₁) := by
      rw [shrink_ends_eq_map_projSplit hU e₀', fromShrinkEP_toShrinkEP, hends₀, Sym2.map_mk]
    have hv₀_sh_exp := isExposed_projSplit_of_not_mem_uTilde hU hv₀_not_U hv₀_exp
    by_cases hv₁U : v₁ ∈ uTilde P hU
    · have hv₁_sh_exp :
          PathsTreesFlowers.Duality.IsExposed (shrink G P) (projSplitMatching P hU K)
            (projSplit P hU v₁) := by
        have h_eq : projSplit P hU v₁ = projSplit P hU u :=
          (projSplit_eq_iff hU).mpr (Or.inr ⟨hv₁U, hu⟩)
        exact h_eq ▸ hu_exp
      obtain ⟨_, hM'_sh, hcard'_sh⟩ :=
        isMatching_insert_of_isExposed hMax_sh.1 hends₀_sh hv₀_sh_exp hv₁_sh_exp
      have hle := hMax_sh.2 (insert e₀' (projSplitMatching P hU K)) hM'_sh
      omega
    · have he₀_not : e₀ ∉ K := not_mem_of_isExposed (by rw [hends₀]; simp) hv₀_exp
      cases hAlt.2 with
      | cons_cons h01 hchain1 =>
        cases hchain1 with
        | cons_cons h12 hchain' =>
          have he₁_mem : e₁ ∈ K := by tauto
          have he₁_not_in := ends_not_mem_uTilde_sym2_of_not_mem hU hv₁U (by rw [hends₁]; simp)
          let e₁' : ShrinkE G P := toShrinkEP hU e₁ he₁_not_in
          have he₁'_mem : e₁' ∈ projSplitMatching P hU K :=
            (mem_projSplitMatching_iff hU).mpr (by rwa [fromShrinkEP_toShrinkEP])
          have hends₁_sh : (shrink G P).ends e₁' = s(projSplit P hU v₁, projSplit P hU v₂) := by
            rw [shrink_ends_eq_map_projSplit hU e₁', fromShrinkEP_toShrinkEP, hends₁, Sym2.map_mk]
          have hv₂_not_U : v₂ ∉ uTilde P hU := by
            intro hv₂U
            have h_eq : projSplit P hU v₂ = projSplit P hU u :=
              (projSplit_eq_iff hU).mpr (Or.inr ⟨hv₂U, hu⟩)
            exact hu_exp e₁' he₁'_mem (by rw [hends₁_sh, h_eq]; simp)
          have hnodup := hAlt.1.1
          rw [List.nodup_cons, List.nodup_cons, List.nodup_cons] at hnodup
          rcases hnodup with ⟨hv0_not, hv1_not, hv2_not, hnodup_vs'⟩
          simp only [List.mem_cons, not_or] at hv0_not hv1_not
          rcases hv0_not with ⟨hv01, hv02, hv0_vs'⟩
          rcases hv1_not with ⟨hv12, hv1_vs'⟩
          have hpath' : PathsTreesFlowers.Duality.IsPath (shrink G (splitPart P U)) (v₂ :: vs') (e₂ :: es') := by
            refine ⟨List.nodup_cons.mpr ⟨hv2_not, hnodup_vs'⟩, ?_, hmap'⟩
            have := hAlt.1.2.1; simp only [List.length_cons] at this ⊢; omega
          have hends₁_swap : (shrink G (splitPart P U)).ends e₁ = s(v₂, v₁) :=
            hends₁.trans Sym2.eq_swap
          have hends₀_swap : (shrink G (splitPart P U)).ends e₀ = s(v₁, v₀) :=
            hends₀.trans Sym2.eq_swap
          obtain ⟨hK₁, _, hv₂_exp_fn, hw_exp_fn⟩ :=
            swap_matching hK he₁_mem hends₁_swap hends₀_swap hv₀_exp
          let K₁ := insert e₀ (K.erase e₁)
          have hv₂_exp : PathsTreesFlowers.Duality.IsExposed (shrink G (splitPart P U)) K₁ v₂ :=
            hv₂_exp_fn (Ne.symm hv12) (Ne.symm hv02)
          have hmem_iff : ∀ e ∈ e₂ :: es', (e ∈ K₁ ↔ e ∈ K) := by
            intro e he
            have he_ne_e₀ : e ≠ e₀ := by
              intro h_eq
              have hv₁_mem : v₁ ∈ v₂ :: vs' :=
                ends_mem_verts_of_isPath hpath' (h_eq ▸ he) (by rw [hends₀]; simp)
              rcases List.mem_cons.mp hv₁_mem with rfl | hmem
              · exact hv12 rfl
              · exact hv1_vs' hmem
            have he_ne_e₁ : e ≠ e₁ := by
              intro h_eq
              have hv₁_mem : v₁ ∈ v₂ :: vs' :=
                ends_mem_verts_of_isPath hpath' (h_eq ▸ he) (by rw [hends₁]; simp)
              rcases List.mem_cons.mp hv₁_mem with rfl | hmem
              · exact hv12 rfl
              · exact hv1_vs' hmem
            simp [K₁, Finset.mem_insert, Finset.mem_erase, he_ne_e₀, he_ne_e₁]
          have hAlt' :
              PathsTreesFlowers.Duality.IsAlternatingPath (shrink G (splitPart P U)) K₁
                (v₂ :: vs') (e₂ :: es') := by
            refine ⟨hpath', isChain_congr (e₂ :: es') ?_ hchain'⟩
            intro x hx y hy hxy
            rw [hmem_iff x hx, hmem_iff y hy]
            exact hxy
          have hlast_exp' :
              ∀ b ∈ (v₂ :: vs').getLast?,
                PathsTreesFlowers.Duality.IsExposed (shrink G (splitPart P U)) K₁ b := by
            intro b hb_last
            have hb_orig : b ∈ (v₀ :: v₁ :: v₂ :: vs').getLast? := by simpa using hb_last
            have hb_mem : b ∈ v₂ :: vs' := List.mem_of_mem_getLast? hb_last
            have hbv₁ : b ≠ v₁ := by
              rintro rfl
              rcases List.mem_cons.mp hb_mem with rfl | hmem
              · exact hv12 rfl
              · exact hv1_vs' hmem
            have hbv₀ : b ≠ v₀ := by
              rintro rfl
              rcases List.mem_cons.mp hb_mem with rfl | hmem
              · exact hv02 rfl
              · exact hv0_vs' hmem
            exact hw_exp_fn b hbv₁ hbv₀ (hb b hb_orig)
          have hends₁_sh_swap : (shrink G P).ends e₁' = s(projSplit P hU v₂, projSplit P hU v₁) :=
            hends₁_sh.trans Sym2.eq_swap
          have hends₀_sh_swap : (shrink G P).ends e₀' = s(projSplit P hU v₁, projSplit P hU v₀) :=
            hends₀_sh.trans Sym2.eq_swap
          obtain ⟨hK₁_sh, hK₁_sh_card, _, hw_sh_exp⟩ :=
            swap_matching hMax_sh.1 he₁'_mem hends₁_sh_swap hends₀_sh_swap hv₀_sh_exp
          have hK₁_eq : K₁ = insert (fromShrinkEP hU e₀') (K.erase (fromShrinkEP hU e₁')) := rfl
          rw [← projSplitMatching_insert_erase hU e₀' e₁', ← hK₁_eq]
            at hK₁_sh hK₁_sh_card hw_sh_exp
          have hMax_sh' : PathsTreesFlowers.Duality.IsMaxMatching (shrink G P) (projSplitMatching P hU K₁) :=
            ⟨hK₁_sh, fun M' hM' => hK₁_sh_card.symm ▸ hMax_sh.2 M' hM'⟩
          have hu_ne_v₁ : projSplit P hU u ≠ projSplit P hU v₁ := by
            intro h_eq
            rcases (projSplit_eq_iff hU).mp h_eq with rfl | ⟨_, hv₁U'⟩
            · exact hv₁U hu
            · exact hv₁U hv₁U'
          have hu_ne_v₀ : projSplit P hU u ≠ projSplit P hU v₀ := by
            intro h_eq
            rcases (projSplit_eq_iff hU).mp h_eq with rfl | ⟨_, hv₀U'⟩
            · exact hv₀_not_U hu
            · exact hv₀_not_U hv₀U'
          have hu_exp' :
              PathsTreesFlowers.Duality.IsExposed (shrink G P) (projSplitMatching P hU K₁)
                (projSplit P hU u) :=
            hw_sh_exp (projSplit P hU u) hu_ne_v₁ hu_ne_v₀ hu_exp
          exact no_aug_path_from_outside_uTilde hU hu (v₂ :: vs') (e₂ :: es') K₁ hK₁ hAlt'
            (List.cons_ne_nil _ _)
            (fun a ha' => by
              simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at ha'
              subst ha'
              exact ⟨hv₂_not_U, hv₂_exp⟩)
            hlast_exp' hMax_sh' hu_exp'

lemma lemma_4_15_of_exposed_projSplit {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {U : Finset V} (hU : U ∈ P.parts)
    {K : Finset (ShrinkE G (splitPart P U))}
    (hK : IsMatching (shrink G (splitPart P U)) K)
    {u : {W : Finset V // W ∈ (splitPart P U).parts}} (hu : u ∈ uTilde P hU)
    (h1 : (PathsTreesFlowers.Duality.exposedIn (shrink G (splitPart P U)) (uTilde P hU) K).card ≤ 1)
    (h2 : PathsTreesFlowers.Duality.IsMaxMatching (shrink G P) (projSplitMatching P hU K))
    (hu_exp : PathsTreesFlowers.Duality.IsExposed (shrink G P) (projSplitMatching P hU K)
      (projSplit P hU u)) :
    PathsTreesFlowers.Duality.IsMaxMatching (shrink G (splitPart P U)) K := by
  by_contra hnot
  rw [PathsTreesFlowers.Duality.berge_3_7 (shrink G (splitPart P U)) K hK] at hnot
  rcases hnot with ⟨vs, es, hAlt, hes_ne, hhead, hlast⟩
  have hvs_len : 2 ≤ vs.length := by
    have := List.length_pos_of_ne_nil hes_ne
    have := hAlt.1.2.1; omega
  have hv₀_mem_head : vs[0]'(by omega) ∈ vs.head? := by
    cases vs with
    | nil => simp at hvs_len
    | cons a _ => simp
  have hvm_mem_last : vs[vs.length - 1]'(by omega) ∈ vs.getLast? := by
    rw [Option.mem_def, List.getLast?_eq_getElem?]
    exact List.getElem?_eq_getElem (by omega)
  have hv₀_exp := hhead _ hv₀_mem_head
  have hvm_exp := hlast _ hvm_mem_last
  have hne_0_m : vs[0]'(by omega) ≠ vs[vs.length - 1]'(by omega) := by
    intro h_eq
    have := (List.Nodup.getElem_inj_iff hAlt.1.1).mp h_eq
    omega
  by_cases hv₀U : vs[0]'(by omega) ∈ uTilde P hU
  · have hvm_not_U : vs[vs.length - 1]'(by omega) ∉ uTilde P hU := by
      intro hvmU
      have hv₀_in : vs[0]'(by omega) ∈
          PathsTreesFlowers.Duality.exposedIn (shrink G (splitPart P U)) (uTilde P hU) K :=
        Finset.mem_filter.mpr ⟨hv₀U, fun e heK _ => hv₀_exp e heK⟩
      have hvm_in : vs[vs.length - 1]'(by omega) ∈
          PathsTreesFlowers.Duality.exposedIn (shrink G (splitPart P U)) (uTilde P hU) K :=
        Finset.mem_filter.mpr ⟨hvmU, fun e heK _ => hvm_exp e heK⟩
      exact hne_0_m (Finset.card_le_one.mp h1 _ hv₀_in _ hvm_in)
    have hAlt_rev := isAlternatingPath_reverse hAlt
    have hes_rev_ne : es.reverse ≠ [] := by simp [hes_ne]
    exact no_aug_path_from_outside_uTilde hU hu vs.reverse es.reverse K hK hAlt_rev hes_rev_ne
      (fun a ha_rev => by
        rw [List.head?_reverse] at ha_rev
        have ha_eq : a = vs[vs.length - 1]'(by omega) := by
          rw [Option.mem_def] at ha_rev hvm_mem_last
          exact Option.some.inj (ha_rev.symm.trans hvm_mem_last)
        subst ha_eq
        exact ⟨hvm_not_U, hvm_exp⟩)
      (fun b hb_rev => by
        rw [List.getLast?_reverse] at hb_rev
        exact hhead b hb_rev)
      h2 hu_exp
  · exact no_aug_path_from_outside_uTilde hU hu vs es K hK hAlt hes_ne
      (fun a ha => by
        have ha_eq : a = vs[0]'(by omega) := by
          rw [Option.mem_def] at ha hv₀_mem_head
          exact Option.some.inj (ha.symm.trans hv₀_mem_head)
        subst ha_eq
        exact ⟨hv₀U, hv₀_exp⟩)
      hlast h2 hu_exp

lemma exposedIn_uTilde_insert_erase {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {U : Finset V} (hU : U ∈ P.parts)
    {K : Finset (ShrinkE G (splitPart P U))}
    (e_add e_rem : ShrinkE G P) :
    PathsTreesFlowers.Duality.exposedIn (shrink G (splitPart P U)) (uTilde P hU)
      (insert (fromShrinkEP hU e_add) (K.erase (fromShrinkEP hU e_rem))) =
    PathsTreesFlowers.Duality.exposedIn (shrink G (splitPart P U)) (uTilde P hU) K := by
  have hadd := fromShrinkEP_ends_not_mem_uTilde_sym2 hU e_add
  have hrem := fromShrinkEP_ends_not_mem_uTilde_sym2 hU e_rem
  ext v
  simp only [PathsTreesFlowers.Duality.exposedIn, Finset.mem_filter, Finset.mem_insert,
    Finset.mem_erase]
  refine and_congr_right fun _ => ⟨fun h e heK heU => ?_, fun h e he_ins heU => ?_⟩
  · have he_ne_rem : e ≠ fromShrinkEP hU e_rem := fun h_eq => hrem (h_eq ▸ heU)
    exact h e (Or.inr ⟨he_ne_rem, heK⟩) heU
  · rcases he_ins with rfl | ⟨_, heK⟩
    · exact False.elim (hadd heU)
    · exact h e heK heU

lemma stem_induction_splitPart {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {U : Finset V} (hU : U ∈ P.parts)
    {u : {W : Finset V // W ∈ (splitPart P U).parts}} (hu : u ∈ uTilde P hU) :
    ∀ (svs : List {W : Finset V // W ∈ P.parts})
      (ses : List (ShrinkE G P))
      (K : Finset (ShrinkE G (splitPart P U))),
      IsMatching (shrink G (splitPart P U)) K →
      (PathsTreesFlowers.Duality.exposedIn (shrink G (splitPart P U)) (uTilde P hU) K).card ≤ 1 →
      PathsTreesFlowers.Duality.IsMaxMatching (shrink G P) (projSplitMatching P hU K) →
      PathsTreesFlowers.Duality.IsStem (shrink G P) (projSplitMatching P hU K) svs ses →
      svs.getLast? = some (projSplit P hU u) →
      PathsTreesFlowers.Duality.IsMaxMatching (shrink G (splitPart P U)) K
  | [], _, _, _, _, _, _, hlast => by cases hlast
  | [w₀], [], K, hK, h1, h2, hSt, hlast => by
    simp only [List.getLast?_singleton, Option.some.injEq] at hlast
    subst hlast
    have hu_exp := hSt.2.1 (projSplit P hU u) (by simp)
    exact lemma_4_15_of_exposed_projSplit hU hK hu h1 h2 hu_exp
  | [_], _ :: _, _, _, _, _, hSt, _ => by
    have := hSt.1.1.2.1; simp at this
  | _ :: _ :: _, [], _, _, _, _, hSt, _ => by
    have := hSt.1.1.2.1; simp at this
  | [w₀, w₁], [e₀], K, _, _, _, hSt, _ => by
    have hends₀ : (shrink G P).ends e₀ = s(w₀, w₁) := by
      simpa using hSt.1.1.2.2
    have hw₀_exp := hSt.2.1 w₀ (by simp)
    have he₀_mem := hSt.2.2 e₀ (by simp)
    exact False.elim (hw₀_exp e₀ he₀_mem (by rw [hends₀]; simp))
  | [_, _], _ :: _ :: _, _, _, _, _, hSt, _ => by
    have := hSt.1.1.2.1; simp at this
  | _ :: _ :: _ :: _, [_], _, _, _, _, hSt, _ => by
    have := hSt.1.1.2.1; simp at this
  | w₀ :: w₁ :: w₂ :: svs', e₀ :: e₁ :: ses', K, hK, h1, h2, hSt, hlast => by
    have hmap := hSt.1.1.2.2
    simp only [List.map_cons, List.tail_cons, List.zipWith_cons_cons, List.cons.injEq] at hmap
    rcases hmap with ⟨hends₀_sh, hends₁_sh, hmap'⟩
    have hnodup := hSt.1.1.1
    rw [List.nodup_cons, List.nodup_cons, List.nodup_cons] at hnodup
    rcases hnodup with ⟨hw0_not, hw1_not, hw2_not, hnodup_svs'⟩
    simp only [List.mem_cons, not_or] at hw0_not hw1_not
    rcases hw0_not with ⟨hw01, hw02, hw0_svs'⟩
    rcases hw1_not with ⟨hw12, hw1_svs'⟩
    have hlast' : (w₂ :: svs').getLast? = some (projSplit P hU u) := by simpa using hlast
    have hu_mem_tail : projSplit P hU u ∈ w₂ :: svs' := List.mem_of_mem_getLast? hlast'
    have hw₀_ne_u : w₀ ≠ projSplit P hU u := by
      rintro rfl
      rcases List.mem_cons.mp hu_mem_tail with h | h
      · exact hw02 h
      · exact hw0_svs' h
    have hw₁_ne_u : w₁ ≠ projSplit P hU u := by
      rintro rfl
      rcases List.mem_cons.mp hu_mem_tail with h | h
      · exact hw12 h
      · exact hw1_svs' h
    have hw₀_exp_sh := hSt.2.1 w₀ (by simp)
    have he₀_not_sh : e₀ ∉ projSplitMatching P hU K :=
      not_mem_of_isExposed (by rw [hends₀_sh]; simp) hw₀_exp_sh
    cases hSt.1.2 with
    | cons_cons h01 hchain1 =>
      have he₁_mem_sh : e₁ ∈ projSplitMatching P hU K := by tauto
      have he₁_mem : fromShrinkEP hU e₁ ∈ K := (mem_projSplitMatching_iff hU).mp he₁_mem_sh
      rcases Sym2.exists.mp ⟨(shrink G (splitPart P U)).ends (fromShrinkEP hU e₀), rfl⟩ with
        ⟨a₀, b₀, hab₀⟩
      have hpair₀ : s(projSplit P hU a₀, projSplit P hU b₀) = s(w₀, w₁) := by
        calc s(projSplit P hU a₀, projSplit P hU b₀)
            = Sym2.map (projSplit P hU) ((shrink G (splitPart P U)).ends (fromShrinkEP hU e₀)) := by
              rw [hab₀, Sym2.map_mk]
          _ = s(w₀, w₁) := (shrink_ends_eq_map_projSplit hU e₀).symm.trans hends₀_sh
      have h_ends₀ :
          ∃ v₀ v₁ : {W : Finset V // W ∈ (splitPart P U).parts},
            projSplit P hU v₀ = w₀ ∧ projSplit P hU v₁ = w₁ ∧
              (shrink G (splitPart P U)).ends (fromShrinkEP hU e₀) = s(v₀, v₁) := by
        rw [Sym2.eq_iff] at hpair₀
        rcases hpair₀ with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact ⟨a₀, b₀, ha, hb, hab₀⟩
        · exact ⟨b₀, a₀, hb, ha, hab₀.trans Sym2.eq_swap⟩
      rcases h_ends₀ with ⟨v₀, v₁, hv₀_w₀, hv₁_w₁, hends₀⟩
      have hv₀_not_U : v₀ ∉ uTilde P hU := by
        intro hv₀U
        exact hw₀_ne_u (hv₀_w₀.symm.trans ((projSplit_eq_iff hU).mpr (Or.inr ⟨hv₀U, hu⟩)))
      have hv₁_not_U : v₁ ∉ uTilde P hU := by
        intro hv₁U
        exact hw₁_ne_u (hv₁_w₁.symm.trans ((projSplit_eq_iff hU).mpr (Or.inr ⟨hv₁U, hu⟩)))
      rcases Sym2.exists.mp ⟨(shrink G (splitPart P U)).ends (fromShrinkEP hU e₁), rfl⟩ with
        ⟨a₁, b₁, hab₁⟩
      have hpair₁ : s(projSplit P hU a₁, projSplit P hU b₁) = s(w₁, w₂) := by
        calc s(projSplit P hU a₁, projSplit P hU b₁)
            = Sym2.map (projSplit P hU) ((shrink G (splitPart P U)).ends (fromShrinkEP hU e₁)) := by
              rw [hab₁, Sym2.map_mk]
          _ = s(w₁, w₂) := (shrink_ends_eq_map_projSplit hU e₁).symm.trans hends₁_sh
      have h_ends₁ :
          ∃ v₂ : {W : Finset V // W ∈ (splitPart P U).parts},
            projSplit P hU v₂ = w₂ ∧
              (shrink G (splitPart P U)).ends (fromShrinkEP hU e₁) = s(v₁, v₂) := by
        rw [Sym2.eq_iff] at hpair₁
        rcases hpair₁ with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · have ha_v₁ : a₁ = v₁ := by
            rcases (projSplit_eq_iff hU).mp (ha.trans hv₁_w₁.symm) with rfl | ⟨_, hv₁U⟩
            · rfl
            · exact False.elim (hv₁_not_U hv₁U)
          exact ⟨b₁, hb, ha_v₁ ▸ hab₁⟩
        · have hb_v₁ : b₁ = v₁ := by
            rcases (projSplit_eq_iff hU).mp (hb.trans hv₁_w₁.symm) with rfl | ⟨_, hv₁U⟩
            · rfl
            · exact False.elim (hv₁_not_U hv₁U)
          exact ⟨a₁, ha, (hb_v₁ ▸ hab₁).trans Sym2.eq_swap⟩
      rcases h_ends₁ with ⟨v₂, hv₂_w₂, hends₁⟩
      have hv₀_exp : PathsTreesFlowers.Duality.IsExposed (shrink G (splitPart P U)) K v₀ := by
        intro f hfK hv₀f
        have hf_not_in := ends_not_mem_uTilde_sym2_of_not_mem hU hv₀_not_U hv₀f
        let f' : ShrinkE G P := toShrinkEP hU f hf_not_in
        have hf_sh : f' ∈ projSplitMatching P hU K :=
          (mem_projSplitMatching_iff hU).mpr (by rwa [fromShrinkEP_toShrinkEP])
        have hw₀_end : w₀ ∈ (shrink G P).ends f' := by
          rw [shrink_ends_eq_map_projSplit hU f', fromShrinkEP_toShrinkEP]
          exact Sym2.mem_map.mpr ⟨v₀, hv₀f, hv₀_w₀⟩
        exact hw₀_exp_sh f' hf_sh hw₀_end
      obtain ⟨hK', hK'_card, _, _⟩ :=
        swap_matching hK he₁_mem (hends₁.trans Sym2.eq_swap) (hends₀.trans Sym2.eq_swap) hv₀_exp
      let K' := insert (fromShrinkEP hU e₀) (K.erase (fromShrinkEP hU e₁))
      have h1' :
          (PathsTreesFlowers.Duality.exposedIn (shrink G (splitPart P U)) (uTilde P hU) K').card ≤ 1 := by
        rw [exposedIn_uTilde_insert_erase hU e₀ e₁]
        exact h1
      obtain ⟨hK'_sh, hK'_sh_card, hw₂_exp_sh_fn, _⟩ :=
        swap_matching h2.1 he₁_mem_sh (hends₁_sh.trans Sym2.eq_swap)
          (hends₀_sh.trans Sym2.eq_swap) hw₀_exp_sh
      rw [← projSplitMatching_insert_erase hU e₀ e₁] at hK'_sh hK'_sh_card hw₂_exp_sh_fn
      have hw₂_exp_sh :
          PathsTreesFlowers.Duality.IsExposed (shrink G P) (projSplitMatching P hU K') w₂ :=
        hw₂_exp_sh_fn (Ne.symm hw12) (Ne.symm hw02)
      have h2' : PathsTreesFlowers.Duality.IsMaxMatching (shrink G P) (projSplitMatching P hU K') :=
        ⟨hK'_sh, fun N hN => hK'_sh_card.symm ▸ h2.2 N hN⟩
      have hpath_sh' : PathsTreesFlowers.Duality.IsPath (shrink G P) (w₂ :: svs') ses' := by
        refine ⟨List.nodup_cons.mpr ⟨hw2_not, hnodup_svs'⟩, ?_, hmap'⟩
        have := hSt.1.1.2.1; simp only [List.length_cons] at this ⊢; omega
      have hmem_sh_iff :
          ∀ e ∈ ses', (e ∈ projSplitMatching P hU K' ↔ e ∈ projSplitMatching P hU K) := by
        intro e he
        have he_ne_e₀ : e ≠ e₀ := by
          intro h_eq
          have hw₁_mem : w₁ ∈ w₂ :: svs' :=
            ends_mem_verts_of_isPath hpath_sh' (h_eq ▸ he) (by rw [hends₀_sh]; simp)
          rcases List.mem_cons.mp hw₁_mem with rfl | hmem
          · exact hw12 rfl
          · exact hw1_svs' hmem
        have he_ne_e₁ : e ≠ e₁ := by
          intro h_eq
          have hw₁_mem : w₁ ∈ w₂ :: svs' :=
            ends_mem_verts_of_isPath hpath_sh' (h_eq ▸ he) (by rw [hends₁_sh]; simp)
          rcases List.mem_cons.mp hw₁_mem with rfl | hmem
          · exact hw12 rfl
          · exact hw1_svs' hmem
        change e ∈ projSplitMatching P hU (insert (fromShrinkEP hU e₀) (K.erase (fromShrinkEP hU e₁))) ↔
          e ∈ projSplitMatching P hU K
        rw [projSplitMatching_insert_erase hU e₀ e₁]
        simp only [Finset.mem_insert, Finset.mem_erase, he_ne_e₀, false_or]
        exact and_iff_right he_ne_e₁
      have hchain_sh' : ses'.IsChain
          (fun e f => e ∈ projSplitMatching P hU K' ↔ f ∉ projSplitMatching P hU K') := by
        refine isChain_congr ses' ?_ (List.isChain_cons.mp hchain1).2
        intro x hx y hy hxy
        rw [hmem_sh_iff x hx, hmem_sh_iff y hy]
        exact hxy
      have hlast_ses' : ∀ e ∈ ses'.getLast?, e ∈ projSplitMatching P hU K' := by
        intro e he_last
        have he_mem : e ∈ ses' := List.mem_of_mem_getLast? he_last
        have he_orig : e ∈ (e₀ :: e₁ :: ses').getLast? := by
          cases ses' with
          | nil => cases he_last
          | cons a t => simpa using he_last
        rw [hmem_sh_iff e he_mem]
        exact hSt.2.2 e he_orig
      have hSt' :
          PathsTreesFlowers.Duality.IsStem (shrink G P) (projSplitMatching P hU K')
            (w₂ :: svs') ses' :=
        ⟨⟨hpath_sh', hchain_sh'⟩,
          fun r hr => by
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hr
            exact hr ▸ hw₂_exp_sh,
          hlast_ses'⟩
      have hMax_K' := stem_induction_splitPart hU hu (w₂ :: svs') ses' K' hK' h1' h2' hSt' hlast'
      exact ⟨hK, fun N hN => hK'_card.symm ▸ hMax_K'.2 N hN⟩

lemma isMatching_shrinkMatching_splitPart {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {U : Finset V} (hU : U ∈ P.parts)
    {M : Finset E} (hM : IsMatching G M)
    (hM_P : IsMatching (shrink G P) (shrinkMatching G P M)) :
    IsMatching (shrink G (splitPart P U)) (shrinkMatching G (splitPart P U) M) := by
  intro e₁ he₁ e₂ he₂ hne w hw₁ hw₂
  have he₁M : e₁.1 ∈ M := Finset.mem_subtype.mp he₁
  have he₂M : e₂.1 ∈ M := Finset.mem_subtype.mp he₂
  by_cases hwU : w ∈ uTilde P hU
  · obtain ⟨v₁, hv₁w, hv₁e⟩ := exists_mem_part_and_ends_of_mem_shrink_ends hw₁
    obtain ⟨v₂, hv₂w, hv₂e⟩ := exists_mem_part_and_ends_of_mem_shrink_ends hw₂
    have hv₁_part : partOf (splitPart P U) v₁ = w := (partOf_eq_iff (splitPart P U) v₁ w).mpr hv₁w
    have hv₁U : v₁ ∈ U := (partOf_splitPart_mem_uTilde_iff hU).mp (hv₁_part.symm ▸ hwU)
    have hw_sing : w.1 = {v₁} := by
      have h1 : (partOf (splitPart P U) v₁).1 = w.1 := congrArg Subtype.val hv₁_part
      exact h1.symm.trans (splitPart_part_of_mem P hU hv₁U)
    have hv₂_eq : v₂ = v₁ := Finset.mem_singleton.mp (hw_sing ▸ hv₂w)
    exact hM e₁.1 he₁M e₂.1 he₂M (Subtype.coe_ne_coe.mpr hne) v₁ hv₁e (hv₂_eq ▸ hv₂e)
  · have he₁_not := ends_not_mem_uTilde_sym2_of_not_mem hU hwU hw₁
    have he₂_not := ends_not_mem_uTilde_sym2_of_not_mem hU hwU hw₂
    let e₁' : ShrinkE G P := toShrinkEP hU e₁ he₁_not
    let e₂' : ShrinkE G P := toShrinkEP hU e₂ he₂_not
    have he₁'_M : e₁' ∈ shrinkMatching G P M := Finset.mem_subtype.mpr he₁M
    have he₂'_M : e₂' ∈ shrinkMatching G P M := Finset.mem_subtype.mpr he₂M
    have hne' : e₁' ≠ e₂' := fun h => hne (Subtype.ext (by
      change e₁'.1 = e₂'.1
      exact congrArg Subtype.val h))
    have hw₁' : projSplit P hU w ∈ (shrink G P).ends e₁' := by
      rw [shrink_ends_eq_map_projSplit hU e₁', fromShrinkEP_toShrinkEP]
      exact Sym2.mem_map.mpr ⟨w, hw₁, rfl⟩
    have hw₂' : projSplit P hU w ∈ (shrink G P).ends e₂' := by
      rw [shrink_ends_eq_map_projSplit hU e₂', fromShrinkEP_toShrinkEP]
      exact Sym2.mem_map.mpr ⟨w, hw₂, rfl⟩
    exact hM_P e₁' he₁'_M e₂' he₂'_M hne' (projSplit P hU w) hw₁' hw₂'

lemma exposedIn_uTilde_card_le_one {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {U : Finset V} (hU : U ∈ P.parts)
    {M : Finset E} {u₀ : V} (_hu₀U : u₀ ∈ U)
    (hu₀ : ∀ x ∈ U, (PathsTreesFlowers.Duality.IsExposed G (M ∩ (induced G U).edges) x ↔ x = u₀)) :
    (PathsTreesFlowers.Duality.exposedIn (shrink G (splitPart P U)) (uTilde P hU)
      (shrinkMatching G (splitPart P U) M)).card ≤ 1 := by
  have h_eq : ∀ w ∈ PathsTreesFlowers.Duality.exposedIn (shrink G (splitPart P U)) (uTilde P hU)
      (shrinkMatching G (splitPart P U) M), w = partOf (splitPart P U) u₀ := by
    intro w hw
    rcases Finset.mem_filter.mp hw with ⟨hwU, hw_exp⟩
    obtain ⟨x, hxw⟩ := (splitPart P U).nonempty_of_mem_parts w.2
    have hx_part : partOf (splitPart P U) x = w := (partOf_eq_iff (splitPart P U) x w).mpr hxw
    have hxU : x ∈ U := (partOf_splitPart_mem_uTilde_iff hU).mp (hx_part.symm ▸ hwU)
    have hx_exp : PathsTreesFlowers.Duality.IsExposed G (M ∩ (induced G U).edges) x := by
      intro e he hxe
      have heM : e ∈ M := (Finset.mem_inter.mp he).1
      have heU : G.ends e ∈ U.sym2 := (Finset.mem_filter.mp (Finset.mem_inter.mp he).2).2
      let e' : ShrinkE G (splitPart P U) := ⟨e, not_isDiag_splitPart_of_mem_sym2 P hU heU⟩
      have he'_M : e' ∈ shrinkMatching G (splitPart P U) M := Finset.mem_subtype.mpr heM
      have he'_sym2 : (shrink G (splitPart P U)).ends e' ∈ (uTilde P hU).sym2 :=
        (mem_uTilde_sym2_iff_mem_U_sym2 hU e').mpr heU
      have hw_end : w ∈ (shrink G (splitPart P U)).ends e' :=
        hx_part ▸ Sym2.mem_map.mpr ⟨x, hxe, rfl⟩
      exact hw_exp e' he'_M he'_sym2 hw_end
    have hxu₀ : x = u₀ := (hu₀ x hxU).mp hx_exp
    exact hx_part.symm.trans (congrArg (partOf (splitPart P U)) hxu₀)
  exact Finset.card_le_one.mpr fun w₁ hw₁ w₂ hw₂ => (h_eq w₁ hw₁).trans (h_eq w₂ hw₂).symm

lemma isMaxMatching_splitPart_of_stem {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {U : Finset V} (hU : U ∈ P.parts)
    {M : Finset E} (hM : IsMatching G M)
    (h1_U : ∃ u ∈ U, ∀ w ∈ U,
      (PathsTreesFlowers.Duality.IsExposed G (M ∩ (induced G U).edges) w ↔ w = u))
    (h2 : PathsTreesFlowers.Duality.IsMaxMatching (shrink G P) (shrinkMatching G P M))
    {svs : List {W : Finset V // W ∈ P.parts}} {ses : List (ShrinkE G P)}
    (hSt : PathsTreesFlowers.Duality.IsStem (shrink G P) (shrinkMatching G P M) svs ses)
    (hlast : svs.getLast? = some ⟨U, hU⟩) :
    PathsTreesFlowers.Duality.IsMaxMatching (shrink G (splitPart P U))
      (shrinkMatching G (splitPart P U) M) := by
  rcases h1_U with ⟨u₀, hu₀U, hu₀⟩
  let u := partOf (splitPart P U) u₀
  have hu : u ∈ uTilde P hU := (partOf_splitPart_mem_uTilde_iff hU).mpr hu₀U
  have hproj_u : projSplit P hU u = ⟨U, hU⟩ := (mem_uTilde_iff hU).mp hu
  have hK : IsMatching (shrink G (splitPart P U)) (shrinkMatching G (splitPart P U) M) :=
    isMatching_shrinkMatching_splitPart hU hM h2.1
  have h1 : (PathsTreesFlowers.Duality.exposedIn (shrink G (splitPart P U)) (uTilde P hU)
      (shrinkMatching G (splitPart P U) M)).card ≤ 1 :=
    exposedIn_uTilde_card_le_one hU hu₀U hu₀
  have hproj_M : projSplitMatching P hU (shrinkMatching G (splitPart P U) M) =
      shrinkMatching G P M :=
    projSplitMatching_shrinkMatching P hU M
  exact stem_induction_splitPart hU hu svs ses (shrinkMatching G (splitPart P U) M) hK h1
    (hproj_M.symm ▸ h2) (hproj_M.symm ▸ hSt) (hproj_u.symm ▸ hlast)

/-! ### Section 5: `liftPart` embedding and transporting `AltTree` across `splitPart P U` -/

noncomputable def liftPart (P : Finpartition (Finset.univ : Finset V)) {U : Finset V}
    (hU : U ∈ P.parts) (w : {W : Finset V // W ∈ P.parts}) :
    {W : Finset V // W ∈ (splitPart P U).parts} :=
  if hw : w.1 ∈ (splitPart P U).parts then ⟨w.1, hw⟩
  else partOf (splitPart P U) (P.nonempty_of_mem_parts hU).choose

lemma liftPart_val_of_ne (P : Finpartition (Finset.univ : Finset V)) {U : Finset V}
    (hU : U ∈ P.parts) {w : {W : Finset V // W ∈ P.parts}} (hne : w ≠ ⟨U, hU⟩) :
    (liftPart P hU w).1 = w.1 := by
  have hw_sp : w.1 ∈ (splitPart P U).parts := by
    rw [splitPart_parts P hU]
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun h => hne (Subtype.ext h), w.2⟩)
  dsimp [liftPart]
  rw [dif_pos hw_sp]

lemma projSplit_liftPart (P : Finpartition (Finset.univ : Finset V)) {U : Finset V}
    (hU : U ∈ P.parts) (w : {W : Finset V // W ∈ P.parts}) :
    projSplit P hU (liftPart P hU w) = w := by
  by_cases hne : w = ⟨U, hU⟩
  · subst hne
    dsimp [liftPart]
    split_ifs with hw_sp
    · dsimp [projSplit]
      rw [dif_pos hU]
    · rw [projSplit_partOf]
      exact (partOf_eq_iff P _ ⟨U, hU⟩).mpr (P.nonempty_of_mem_parts hU).choose_spec
  · have hval := liftPart_val_of_ne P hU hne
    dsimp [projSplit]
    have hwP : (liftPart P hU w).1 ∈ P.parts := hval.symm ▸ w.2
    rw [dif_pos hwP]
    exact Subtype.ext hval

lemma liftPart_injective (P : Finpartition (Finset.univ : Finset V)) {U : Finset V}
    (hU : U ∈ P.parts) : Function.Injective (liftPart P hU) :=
  Function.LeftInverse.injective (projSplit_liftPart P hU)

lemma fromShrinkEP_injective {G : EdmondsMatching65.Polyhedron.Graph V E}
    (P : Finpartition (Finset.univ : Finset V)) {U : Finset V} (hU : U ∈ P.parts) :
    Function.Injective (fromShrinkEP (G := G) hU) := by
  intro e₁ e₂ h
  exact Subtype.ext (congrArg (fun x : ShrinkE G (splitPart P U) => x.1) h)

lemma liftPart_not_mem_uTilde_of_ne (P : Finpartition (Finset.univ : Finset V)) {U : Finset V}
    (hU : U ∈ P.parts) {w : {W : Finset V // W ∈ P.parts}} (hne : w ≠ ⟨U, hU⟩) :
    liftPart P hU w ∉ uTilde P hU := by
  rw [mem_uTilde_iff, projSplit_liftPart]
  exact hne

lemma projSplit_eq_iff_eq_liftPart (P : Finpartition (Finset.univ : Finset V)) {U : Finset V}
    (hU : U ∈ P.parts) {z : {W : Finset V // W ∈ (splitPart P U).parts}}
    {w : {W : Finset V // W ∈ P.parts}} (hne : w ≠ ⟨U, hU⟩) :
    projSplit P hU z = w ↔ z = liftPart P hU w := by
  have h1 : projSplit P hU z = w ↔ projSplit P hU z = projSplit P hU (liftPart P hU w) := by
    rw [projSplit_liftPart]
  rw [h1, projSplit_eq_iff]
  have hnot := liftPart_not_mem_uTilde_of_ne P hU hne
  exact ⟨fun h => h.resolve_right (fun h2 => hnot h2.2), fun h => Or.inl h⟩

lemma shrink_splitPart_ends_fromShrinkEP {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {U : Finset V} (hU : U ∈ P.parts)
    {e : ShrinkE G P} {w₁ w₂ : {W : Finset V // W ∈ P.parts}}
    (hw₁ : w₁ ≠ ⟨U, hU⟩) (hw₂ : w₂ ≠ ⟨U, hU⟩)
    (hends : (shrink G P).ends e = s(w₁, w₂)) :
    (shrink G (splitPart P U)).ends (fromShrinkEP hU e) =
      s(liftPart P hU w₁, liftPart P hU w₂) := by
  rcases Sym2.exists.mp ⟨(shrink G (splitPart P U)).ends (fromShrinkEP hU e), rfl⟩ with
    ⟨z₁, z₂, hz⟩
  have hmap : s(projSplit P hU z₁, projSplit P hU z₂) = s(w₁, w₂) := by
    calc s(projSplit P hU z₁, projSplit P hU z₂)
        = ((shrink G (splitPart P U)).ends (fromShrinkEP hU e)).map (projSplit P hU) := by
          rw [hz, Sym2.map_mk]
      _ = (shrink G P).ends e := (shrink_ends_eq_map_projSplit hU e).symm
      _ = s(w₁, w₂) := hends
  rw [Sym2.eq_iff, projSplit_eq_iff_eq_liftPart P hU hw₁,
    projSplit_eq_iff_eq_liftPart P hU hw₂, projSplit_eq_iff_eq_liftPart P hU hw₂,
    projSplit_eq_iff_eq_liftPart P hU hw₁] at hmap
  rw [hz, Sym2.eq_iff]
  exact hmap

lemma shrink_splitPart_ends_eq_map_liftPart {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {U : Finset V} (hU : U ∈ P.parts)
    {e : ShrinkE G P} {w₁ w₂ : {W : Finset V // W ∈ P.parts}}
    (hw₁ : w₁ ≠ ⟨U, hU⟩) (hw₂ : w₂ ≠ ⟨U, hU⟩)
    (hends : (shrink G P).ends e = s(w₁, w₂)) :
    (shrink G (splitPart P U)).ends (fromShrinkEP hU e) =
      ((shrink G P).ends e).map (liftPart P hU) := by
  rw [shrink_splitPart_ends_fromShrinkEP hU hw₁ hw₂ hends, hends, Sym2.map_mk]

def mapSub {V₁ E₁ V₂ E₂ : Type} [DecidableEq V₁] [DecidableEq E₁]
    [DecidableEq V₂] [DecidableEq E₂]
    {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁}
    {G₂ : EdmondsMatching65.Polyhedron.Graph V₂ E₂}
    (fv : V₁ ↪ V₂) (fe : E₁ ↪ E₂) (H : Sub G₁)
    (hends_map : ∀ e ∈ H.edges, G₂.ends (fe e) = (G₁.ends e).map fv) :
    Sub G₂ where
  verts := H.verts.map fv
  edges := H.edges.map fe
  ends_mem := by
    intro e' he' z hz
    rcases Finset.mem_map.mp he' with ⟨e, he, rfl⟩
    rw [hends_map e he] at hz
    rcases Sym2.mem_map.mp hz with ⟨v, hv, rfl⟩
    exact Finset.mem_map_of_mem fv (H.ends_mem e he v hv)

def mapAltTree {V₁ E₁ V₂ E₂ : Type} [DecidableEq V₁] [DecidableEq E₁]
    [DecidableEq V₂] [DecidableEq E₂]
    {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁}
    {G₂ : EdmondsMatching65.Polyhedron.Graph V₂ E₂}
    (fv : V₁ ↪ V₂) (fe : E₁ ↪ E₂) (T : AltTree G₁)
    (hends_map : ∀ e ∈ T.edges, G₂.ends (fe e) = (G₁.ends e).map fv) :
    AltTree G₂ where
  toSub := mapSub fv fe T.toSub hends_map
  inner := T.inner.map fv
  outer := T.outer.map fv
  verts_eq := by
    change T.verts.map fv = T.inner.map fv ∪ T.outer.map fv
    rw [T.verts_eq, Finset.map_union]
  disjoint_inner_outer := by
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    rcases Finset.mem_map.mp hz₁ with ⟨x₁, hx₁, rfl⟩
    rcases Finset.mem_map.mp hz₂ with ⟨x₂, hx₂, heq⟩
    rw [fv.injective heq] at hx₂
    exact Finset.disjoint_left.mp T.disjoint_inner_outer hx₁ hx₂
  edge_inner_outer := by
    intro e' he'
    rcases Finset.mem_map.mp he' with ⟨e, he, rfl⟩
    obtain ⟨u, hu, w, hw, hends⟩ := T.edge_inner_outer e he
    refine ⟨fv u, Finset.mem_map_of_mem fv hu, fv w, Finset.mem_map_of_mem fv hw, ?_⟩
    rw [hends_map e he, hends, Sym2.map_mk]
  inner_degree := by
    intro u' hu'
    rcases Finset.mem_map.mp hu' with ⟨u, hu, rfl⟩
    have hfilt : (T.edges.map fe).filter (fun e' => fv u ∈ G₂.ends e') =
        (T.edges.filter (fun e => u ∈ G₁.ends e)).map fe := by
      ext e'
      simp only [Finset.mem_filter, Finset.mem_map]
      constructor
      · rintro ⟨⟨e, he, rfl⟩, hmem⟩
        rw [hends_map e he, Sym2.mem_map] at hmem
        rcases hmem with ⟨v, hv, hvu⟩
        rw [fv.injective hvu] at hv
        exact ⟨e, ⟨he, hv⟩, rfl⟩
      · rintro ⟨e, ⟨he, hv⟩, rfl⟩
        refine ⟨⟨e, he, rfl⟩, ?_⟩
        rw [hends_map e he]
        exact Sym2.mem_map.mpr ⟨u, hv, rfl⟩
    change ((T.edges.map fe).filter (fun e' => fv u ∈ G₂.ends e')).card = 2
    rw [hfilt, Finset.card_map]
    exact T.inner_degree u hu
  connected := by
    rcases T.connected.1 with ⟨v₀, hv₀⟩
    refine ⟨⟨fv v₀, Finset.mem_map_of_mem fv hv₀⟩, ?_⟩
    intro x' hx' y' hy'
    rcases Finset.mem_map.mp hx' with ⟨x, hx, rfl⟩
    rcases Finset.mem_map.mp hy' with ⟨y, hy, rfl⟩
    have hwalk : ∀ a b : V₁, Relation.ReflTransGen T.toSub.Adj a b →
        Relation.ReflTransGen (mapSub fv fe T.toSub hends_map).Adj (fv a) (fv b) := by
      intro a b hab
      induction hab using Relation.ReflTransGen.head_induction_on with
      | refl => exact Relation.ReflTransGen.refl
      | head hstep _ ih =>
        rcases hstep with ⟨e, he, hends⟩
        refine Relation.ReflTransGen.head ⟨fe e, Finset.mem_map_of_mem fe he, ?_⟩ ih
        rw [hends_map e he, hends, Sym2.map_mk]
    exact hwalk x y (T.connected.2 x hx y hy)
  card_verts := by
    change (T.verts.map fv).card = (T.edges.map fe).card + 1
    rw [Finset.card_map, Finset.card_map, T.card_verts]

lemma isMatching_map_iff {V₁ E₁ V₂ E₂ : Type} [DecidableEq V₁] [DecidableEq E₁]
    [DecidableEq V₂] [DecidableEq E₂]
    {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁}
    {G₂ : EdmondsMatching65.Polyhedron.Graph V₂ E₂}
    (fv : V₁ ↪ V₂) (fe : E₁ ↪ E₂) {F : Finset E₁}
    (hends_map : ∀ e ∈ F, G₂.ends (fe e) = (G₁.ends e).map fv)
    {N : Finset E₁} (hN_sub : N ⊆ F) :
    IsMatching G₂ (N.map fe) ↔ IsMatching G₁ N := by
  constructor
  · intro hM₂ e₁ he₁ e₂ he₂ hne v hv₁ hv₂
    have he₁' : fe e₁ ∈ N.map fe := Finset.mem_map_of_mem fe he₁
    have he₂' : fe e₂ ∈ N.map fe := Finset.mem_map_of_mem fe he₂
    have hne' : fe e₁ ≠ fe e₂ := fun h => hne (fe.injective h)
    have hv₁' : fv v ∈ G₂.ends (fe e₁) := by
      rw [hends_map e₁ (hN_sub he₁)]
      exact Sym2.mem_map.mpr ⟨v, hv₁, rfl⟩
    have hv₂' : fv v ∈ G₂.ends (fe e₂) := by
      rw [hends_map e₂ (hN_sub he₂)]
      exact Sym2.mem_map.mpr ⟨v, hv₂, rfl⟩
    exact hM₂ (fe e₁) he₁' (fe e₂) he₂' hne' (fv v) hv₁' hv₂'
  · intro hM₁ e₁' he₁' e₂' he₂' hne' z hz₁ hz₂
    rcases Finset.mem_map.mp he₁' with ⟨e₁, he₁, rfl⟩
    rcases Finset.mem_map.mp he₂' with ⟨e₂, he₂, rfl⟩
    have hne : e₁ ≠ e₂ := fun h => hne' (congrArg fe h)
    rw [hends_map e₁ (hN_sub he₁)] at hz₁
    rw [hends_map e₂ (hN_sub he₂)] at hz₂
    rcases Sym2.mem_map.mp hz₁ with ⟨v₁, hv₁, rfl⟩
    rcases Sym2.mem_map.mp hz₂ with ⟨v₂, hv₂, hv_eq⟩
    rw [fv.injective hv_eq] at hv₂
    exact hM₁ e₁ he₁ e₂ he₂ hne v₁ hv₁ hv₂

lemma isPlantedTree_mapAltTree {V₁ E₁ V₂ E₂ : Type} [DecidableEq V₁] [DecidableEq E₁]
    [DecidableEq V₂] [DecidableEq E₂]
    {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁}
    {G₂ : EdmondsMatching65.Polyhedron.Graph V₂ E₂}
    (fv : V₁ ↪ V₂) (fe : E₁ ↪ E₂) (T : AltTree G₁)
    (hends_map : ∀ e ∈ T.edges, G₂.ends (fe e) = (G₁.ends e).map fv)
    {M₁ : Finset E₁} {M₂ : Finset E₂} {r : V₁}
    (hM_iff : ∀ e ∈ T.edges, fe e ∈ M₂ ↔ e ∈ M₁)
    (hr_exp : PathsTreesFlowers.Duality.IsExposed G₂ M₂ (fv r))
    (hpl : IsPlantedTree G₁ M₁ T r) :
    IsPlantedTree G₂ M₂ (mapAltTree fv fe T hends_map) (fv r) := by
  have hinter_eq : M₂ ∩ (T.edges.map fe) = (M₁ ∩ T.edges).map fe := by
    ext e'
    simp only [Finset.mem_inter, Finset.mem_map]
    constructor
    · rintro ⟨he'M₂, e, heT, rfl⟩
      exact ⟨e, ⟨(hM_iff e heT).mp he'M₂, heT⟩, rfl⟩
    · rintro ⟨e, ⟨heM₁, heT⟩, rfl⟩
      exact ⟨(hM_iff e heT).mpr heM₁, e, heT, rfl⟩
  refine ⟨?_, Finset.mem_map_of_mem fv hpl.root_mem, ?_, hr_exp⟩
  · refine ⟨Finset.inter_subset_right, ?_, ?_⟩
    · change IsMatching G₂ (M₂ ∩ (T.edges.map fe))
      rw [hinter_eq]
      exact (isMatching_map_iff fv fe hends_map Finset.inter_subset_right).mpr hpl.max_in.2.1
    · intro N₂ hN₂_sub hN₂_match
      change N₂ ⊆ T.edges.map fe at hN₂_sub
      change N₂.card ≤ (M₂ ∩ (T.edges.map fe)).card
      let N₁ := T.edges.filter (fun e => fe e ∈ N₂)
      have hN₁_sub : N₁ ⊆ T.edges := Finset.filter_subset _ _
      have hN₁_map : N₁.map fe = N₂ := by
        ext e'
        simp only [N₁, Finset.mem_map, Finset.mem_filter]
        constructor
        · rintro ⟨e, ⟨_, heN₂⟩, rfl⟩; exact heN₂
        · intro he'N₂
          rcases Finset.mem_map.mp (hN₂_sub he'N₂) with ⟨e, heT, rfl⟩
          exact ⟨e, ⟨heT, he'N₂⟩, rfl⟩
      have hN₁_match : IsMatching G₁ N₁ :=
        (isMatching_map_iff fv fe hends_map hN₁_sub).mp (hN₁_map.symm ▸ hN₂_match)
      have hle := hpl.max_in.2.2 N₁ hN₁_sub hN₁_match
      rw [hinter_eq, Finset.card_map, ← hN₁_map, Finset.card_map]
      exact hle
  · change PathsTreesFlowers.Duality.IsExposed G₂ (M₂ ∩ (T.edges.map fe)) (fv r)
    rw [hinter_eq]
    intro e' he' hre'
    rcases Finset.mem_map.mp he' with ⟨e, he, rfl⟩
    have heT : e ∈ T.edges := (Finset.mem_inter.mp he).2
    rw [hends_map e heT] at hre'
    rcases Sym2.mem_map.mp hre' with ⟨v, hv, hvr⟩
    rw [fv.injective hvr] at hv
    exact hpl.root_exposed_in e he hv

lemma isExposed_liftPart_of_isExposed {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} {U : Finset V} (hU : U ∈ P.parts)
    {M : Finset E} {w : {W : Finset V // W ∈ P.parts}} (hne : w ≠ ⟨U, hU⟩)
    (hexp : PathsTreesFlowers.Duality.IsExposed (shrink G P) (shrinkMatching G P M) w) :
    PathsTreesFlowers.Duality.IsExposed (shrink G (splitPart P U))
      (shrinkMatching G (splitPart P U) M) (liftPart P hU w) := by
  intro f hfK hwf
  have hw_not_U : liftPart P hU w ∉ uTilde P hU := liftPart_not_mem_uTilde_of_ne P hU hne
  have hf_not_in := ends_not_mem_uTilde_sym2_of_not_mem hU hw_not_U hwf
  let f' : ShrinkE G P := toShrinkEP hU f hf_not_in
  have hf_sh : f' ∈ shrinkMatching G P M := by
    rw [← projSplitMatching_shrinkMatching P hU M, mem_projSplitMatching_iff hU,
      fromShrinkEP_toShrinkEP]
    exact hfK
  have hw_end : w ∈ (shrink G P).ends f' := by
    rw [shrink_ends_eq_map_projSplit hU f', fromShrinkEP_toShrinkEP]
    exact Sym2.mem_map.mpr ⟨liftPart P hU w, hwf, projSplit_liftPart P hU w⟩
  exact hexp f' hf_sh hw_end

noncomputable def liftAltTree {G : EdmondsMatching65.Polyhedron.Graph V E}
    (P : Finpartition (Finset.univ : Finset V)) {U : Finset V} (hU : U ∈ P.parts)
    (T : AltTree (shrink G P)) (hnot : ⟨U, hU⟩ ∉ T.verts) :
    AltTree (shrink G (splitPart P U)) :=
  mapAltTree ⟨liftPart P hU, liftPart_injective P hU⟩ ⟨fromShrinkEP hU, fromShrinkEP_injective P hU⟩ T
    (by
      intro e he
      obtain ⟨u, hu, w, hw, hends⟩ := T.edge_inner_outer e he
      have hu_ne : u ≠ ⟨U, hU⟩ := fun h => hnot (h ▸ T.verts_eq ▸ Finset.mem_union_left _ hu)
      have hw_ne : w ≠ ⟨U, hU⟩ := fun h => hnot (h ▸ T.verts_eq ▸ Finset.mem_union_right _ hw)
      exact shrink_splitPart_ends_eq_map_liftPart hU hu_ne hw_ne hends)

lemma isPlantedTree_liftAltTree {G : EdmondsMatching65.Polyhedron.Graph V E}
    (P : Finpartition (Finset.univ : Finset V)) {U : Finset V} (hU : U ∈ P.parts)
    {M : Finset E} (T : AltTree (shrink G P)) (hnot : ⟨U, hU⟩ ∉ T.verts)
    {r : {W : Finset V // W ∈ P.parts}}
    (hpl : IsPlantedTree (shrink G P) (shrinkMatching G P M) T r) :
    IsPlantedTree (shrink G (splitPart P U)) (shrinkMatching G (splitPart P U) M)
      (liftAltTree P hU T hnot) (liftPart P hU r) := by
  have hr_ne : r ≠ ⟨U, hU⟩ := fun h => hnot (h ▸ hpl.root_mem)
  refine isPlantedTree_mapAltTree
    ⟨liftPart P hU, liftPart_injective P hU⟩
    ⟨fromShrinkEP hU, fromShrinkEP_injective P hU⟩ T _ ?_
    (isExposed_liftPart_of_isExposed hU hr_ne hpl.root_exposed) hpl
  intro e _
  simp only [shrinkMatching, Finset.mem_subtype]
  rfl

/-! ### Section 6: Phase B — Unshrinking exposed parts and Singleton partition base case -/

lemma isStem_singleton {V₁ E₁ : Type} [DecidableEq V₁] [DecidableEq E₁]
    {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁} {M₁ : Finset E₁} {w : V₁}
    (hw : PathsTreesFlowers.Duality.IsExposed G₁ M₁ w) :
    PathsTreesFlowers.Duality.IsStem G₁ M₁ [w] [] := by
  refine ⟨⟨⟨List.nodup_singleton w, rfl, rfl⟩, List.IsChain.nil⟩, ?_, ?_⟩
  · intro r hr
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hr
    exact hr ▸ hw
  · intro e he
    cases he

lemma partOf_injective_of_card_le_one (P : Finpartition (Finset.univ : Finset V))
    (hle : ∀ U ∈ P.parts, U.card ≤ 1) :
    Function.Injective (partOf P) := by
  intro x y hxy
  have hxU : P.part x ∈ P.parts := P.part_mem.2 (Finset.mem_univ x)
  have hx_mem : x ∈ P.part x := P.mem_part (Finset.mem_univ x)
  have hy_mem : y ∈ P.part x := (partOf_eq_iff P y (partOf P x)).mp hxy.symm
  exact Finset.card_le_one.mp (hle (P.part x) hxU) x hx_mem y hy_mem

lemma not_isDiag_of_partOf_injective {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P : Finpartition (Finset.univ : Finset V)} (hinj : Function.Injective (partOf P)) (e : E) :
    ¬ ((G.ends e).map (partOf P)).IsDiag := by
  rcases Sym2.exists.mp ⟨G.ends e, rfl⟩ with ⟨a, b, hab⟩
  rw [hab, Sym2.map_mk, Sym2.mk_isDiag_iff]
  intro h
  exact G.loopless e (hab ▸ Sym2.mk_isDiag_iff.mpr (hinj h))

lemma isMaxMatching_of_card_le_one {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (hM : IsMatching G M) (P : Finpartition (Finset.univ : Finset V))
    (hle : ∀ U ∈ P.parts, U.card ≤ 1)
    (h2 : PathsTreesFlowers.Duality.IsMaxMatching (shrink G P) (shrinkMatching G P M)) :
    PathsTreesFlowers.Duality.IsMaxMatching G M := by
  have hinj := partOf_injective_of_card_le_one P hle
  have hcard_sh : ∀ S : Finset E, (shrinkMatching G P S).card = S.card := by
    intro S
    rw [shrinkMatching, Finset.card_subtype]
    have hfilt : S.filter (fun e => ¬ ((G.ends e).map (partOf P)).IsDiag) = S :=
      Finset.filter_eq_self.mpr fun e _ => not_isDiag_of_partOf_injective hinj e
    rw [hfilt]
  refine ⟨hM, fun N hN => ?_⟩
  have hN_sh : IsMatching (shrink G P) (shrinkMatching G P N) := by
    intro e₁ he₁ e₂ he₂ hne p hp₁ hp₂
    have he₁N : e₁.1 ∈ N := Finset.mem_subtype.mp he₁
    have he₂N : e₂.1 ∈ N := Finset.mem_subtype.mp he₂
    change p ∈ (G.ends e₁.1).map (partOf P) at hp₁
    change p ∈ (G.ends e₂.1).map (partOf P) at hp₂
    rcases Sym2.mem_map.mp hp₁ with ⟨x₁, hx₁, hpx₁⟩
    rcases Sym2.mem_map.mp hp₂ with ⟨x₂, hx₂, hpx₂⟩
    have hx_eq : x₁ = x₂ := hinj (hpx₁.trans hpx₂.symm)
    subst hx_eq
    exact hN e₁.1 he₁N e₂.1 he₂N (Subtype.coe_ne_coe.mpr hne) x₁ hx₁ hx₂
  have hle_sh := h2.2 (shrinkMatching G P N) hN_sh
  rwa [hcard_sh N, hcard_sh M] at hle_sh

lemma splitPart_parts_filter_one_lt_card (P : Finpartition (Finset.univ : Finset V))
    {U : Finset V} (hU : U ∈ P.parts) :
    (splitPart P U).parts.filter (fun W => 1 < W.card) =
      (P.parts.filter (fun W => 1 < W.card)).erase U := by
  ext W
  rw [Finset.mem_filter, splitPart_parts P hU, Finset.mem_union, Finset.mem_erase,
    Finset.mem_image, Finset.mem_erase, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hWU, hWP⟩ | ⟨u, _, rfl⟩, hcard⟩
    · exact ⟨hWU, hWP, hcard⟩
    · simp at hcard
  · rintro ⟨hWU, hWP, hcard⟩
    exact ⟨Or.inl ⟨hWU, hWP⟩, hcard⟩

lemma isMaxMatching_of_all_gt_one_exposed_aux {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (hM : IsMatching G M) :
    ∀ (m : ℕ) (P : Finpartition (Finset.univ : Finset V)),
      (P.parts.filter (fun U => 1 < U.card)).card = m →
      (∀ U ∈ P.parts, 1 < U.card →
        ∃ u ∈ U, ∀ w ∈ U, (PathsTreesFlowers.Duality.IsExposed G (M ∩ (induced G U).edges) w ↔ w = u)) →
      PathsTreesFlowers.Duality.IsMaxMatching (shrink G P) (shrinkMatching G P M) →
      (∀ (U : Finset V) (hU : U ∈ P.parts), 1 < U.card →
        PathsTreesFlowers.Duality.IsExposed (shrink G P) (shrinkMatching G P M) ⟨U, hU⟩) →
      PathsTreesFlowers.Duality.IsMaxMatching G M
  | 0, P, hm, _h1, h2, _hexp => by
    have h_empty : P.parts.filter (fun U => 1 < U.card) = ∅ := Finset.card_eq_zero.mp hm
    have hle : ∀ U ∈ P.parts, U.card ≤ 1 := by
      intro U hU
      by_contra hgt
      have hmem : U ∈ P.parts.filter (fun W => 1 < W.card) :=
        Finset.mem_filter.mpr ⟨hU, by omega⟩
      rw [h_empty] at hmem
      simp at hmem
    exact isMaxMatching_of_card_le_one hM P hle h2
  | m + 1, P, hm, h1, h2, hexp => by
    obtain ⟨U₀, hU₀_filt⟩ := Finset.card_pos.mp (by omega : 0 < (P.parts.filter (fun U => 1 < U.card)).card)
    have hU₀ : U₀ ∈ P.parts := (Finset.mem_filter.mp hU₀_filt).1
    have hU₀_card : 1 < U₀.card := (Finset.mem_filter.mp hU₀_filt).2
    have hSt := isStem_singleton (hexp U₀ hU₀ hU₀_card)
    have h2' := isMaxMatching_splitPart_of_stem hU₀ hM (h1 U₀ hU₀ hU₀_card) h2 hSt rfl
    have hm' : ((splitPart P U₀).parts.filter (fun W => 1 < W.card)).card = m := by
      rw [splitPart_parts_filter_one_lt_card P hU₀, Finset.card_erase_of_mem hU₀_filt]
      omega
    refine isMaxMatching_of_all_gt_one_exposed_aux hM m (splitPart P U₀) hm' ?_ h2' ?_
    · intro W hW hW_card
      have hW_filt : W ∈ (splitPart P U₀).parts.filter (fun X => 1 < X.card) :=
        Finset.mem_filter.mpr ⟨hW, hW_card⟩
      rw [splitPart_parts_filter_one_lt_card P hU₀] at hW_filt
      exact h1 W (Finset.mem_filter.mp (Finset.mem_erase.mp hW_filt).2).1 hW_card
    · intro W hW hW_card
      have hW_filt : W ∈ (splitPart P U₀).parts.filter (fun X => 1 < X.card) :=
        Finset.mem_filter.mpr ⟨hW, hW_card⟩
      rw [splitPart_parts_filter_one_lt_card P hU₀] at hW_filt
      have hW_ne : W ≠ U₀ := (Finset.mem_erase.mp hW_filt).1
      have hWP : W ∈ P.parts := (Finset.mem_filter.mp (Finset.mem_erase.mp hW_filt).2).1
      have hsub_ne : (⟨W, hWP⟩ : {X // X ∈ P.parts}) ≠ ⟨U₀, hU₀⟩ :=
        fun h => hW_ne (congrArg Subtype.val h)
      have h_lift_eq : liftPart P hU₀ ⟨W, hWP⟩ = ⟨W, hW⟩ :=
        Subtype.ext (liftPart_val_of_ne P hU₀ hsub_ne)
      rw [← h_lift_eq]
      exact isExposed_liftPart_of_isExposed hU₀ hsub_ne (hexp W hWP hW_card)

/-! ### Section 7: Phase A — Leaf pruning on `AltTree`, stems to outer vertices, and main proof -/

def toDualityAltTree {V₁ E₁ : Type} [Fintype V₁] [DecidableEq V₁] [Fintype E₁] [DecidableEq E₁]
    {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁} (J : AltTree G₁) :
    PathsTreesFlowers.Duality.AltTree G₁ where
  inner := J.inner
  outer := J.outer
  edges := J.edges
  disjoint := J.disjoint_inner_outer
  edge_ends := J.edge_inner_outer
  inner_deg := J.inner_degree
  connected := ⟨J.verts_eq ▸ J.connected.1,
    fun u hu w hw => J.connected.2 u (J.verts_eq ▸ hu) w (J.verts_eq ▸ hw)⟩
  card_verts := J.verts_eq ▸ J.card_verts

def ofDualityAltTree {V₁ E₁ : Type} [Fintype V₁] [DecidableEq V₁] [Fintype E₁] [DecidableEq E₁]
    {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁}
    (JD : PathsTreesFlowers.Duality.AltTree G₁) : AltTree G₁ where
  verts := JD.inner ∪ JD.outer
  edges := JD.edges
  ends_mem := fun e he v hv => by
    obtain ⟨u, hu, w, hw, hends⟩ := JD.edge_ends e he
    rw [hends, Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · exact Finset.mem_union_left _ hu
    · exact Finset.mem_union_right _ hw
  inner := JD.inner
  outer := JD.outer
  verts_eq := rfl
  disjoint_inner_outer := JD.disjoint
  edge_inner_outer := JD.edge_ends
  inner_degree := JD.inner_deg
  connected := JD.connected
  card_verts := JD.card_verts

lemma not_mem_outer_of_mem_inner_duality {V₁ E₁ : Type} [Fintype V₁] [DecidableEq V₁]
    [Fintype E₁] [DecidableEq E₁] {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁}
    (J : PathsTreesFlowers.Duality.AltTree G₁) {u : V₁} (hu : u ∈ J.inner) :
    u ∉ J.outer :=
  Finset.disjoint_left.mp J.disjoint hu

lemma not_mem_inner_of_mem_outer_duality {V₁ E₁ : Type} [Fintype V₁] [DecidableEq V₁]
    [Fintype E₁] [DecidableEq E₁] {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁}
    (J : PathsTreesFlowers.Duality.AltTree G₁) {w : V₁} (hw : w ∈ J.outer) :
    w ∉ J.inner :=
  Finset.disjoint_right.mp J.disjoint hw

lemma ne_of_mem_inner_of_mem_outer_duality {V₁ E₁ : Type} [Fintype V₁] [DecidableEq V₁]
    [Fintype E₁] [DecidableEq E₁] {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁}
    (J : PathsTreesFlowers.Duality.AltTree G₁) {u w : V₁}
    (hu : u ∈ J.inner) (hw : w ∈ J.outer) : u ≠ w :=
  fun h => not_mem_outer_of_mem_inner_duality J hu (h ▸ hw)

lemma card_filter_inner_ends_duality {V₁ E₁ : Type} [Fintype V₁] [DecidableEq V₁]
    [Fintype E₁] [DecidableEq E₁] {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁}
    (J : PathsTreesFlowers.Duality.AltTree G₁) {e : E₁} (he : e ∈ J.edges) :
    (J.inner.filter (fun x => x ∈ G₁.ends e)).card = 1 := by
  obtain ⟨u, hu, w, hw, hends⟩ := J.edge_ends e he
  have hfilt : J.inner.filter (fun x => x ∈ G₁.ends e) = {u} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton, hends, Sym2.mem_iff]
    exact ⟨fun ⟨hx, h⟩ => h.resolve_right (fun hxw => not_mem_inner_of_mem_outer_duality J hw (hxw ▸ hx)),
      fun h => ⟨h ▸ hu, Or.inl h⟩⟩
  rw [hfilt, Finset.card_singleton]

lemma card_filter_outer_ends_duality {V₁ E₁ : Type} [Fintype V₁] [DecidableEq V₁]
    [Fintype E₁] [DecidableEq E₁] {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁}
    (J : PathsTreesFlowers.Duality.AltTree G₁) {e : E₁} (he : e ∈ J.edges) :
    (J.outer.filter (fun x => x ∈ G₁.ends e)).card = 1 := by
  obtain ⟨u, hu, w, hw, hends⟩ := J.edge_ends e he
  have hfilt : J.outer.filter (fun x => x ∈ G₁.ends e) = {w} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton, hends, Sym2.mem_iff]
    exact ⟨fun ⟨hx, h⟩ => h.resolve_left (fun hxu => not_mem_outer_of_mem_inner_duality J hu (hxu ▸ hx)),
      fun h => ⟨h ▸ hw, Or.inr h⟩⟩
  rw [hfilt, Finset.card_singleton]

lemma edges_card_eq_two_mul_inner_duality {V₁ E₁ : Type} [Fintype V₁] [DecidableEq V₁]
    [Fintype E₁] [DecidableEq E₁] {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁}
    (J : PathsTreesFlowers.Duality.AltTree G₁) :
    J.edges.card = 2 * J.inner.card := by
  have hcomm : ∑ u ∈ J.inner, (J.edges.filter (fun e => u ∈ G₁.ends e)).card =
      ∑ e ∈ J.edges, (J.inner.filter (fun u => u ∈ G₁.ends e)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have h1 : ∑ u ∈ J.inner, (J.edges.filter (fun e => u ∈ G₁.ends e)).card = 2 * J.inner.card := by
    calc ∑ u ∈ J.inner, (J.edges.filter (fun e => u ∈ G₁.ends e)).card
        = ∑ _u ∈ J.inner, 2 := Finset.sum_congr rfl fun u hu => J.inner_deg u hu
      _ = 2 * J.inner.card := by simp [Nat.mul_comm]
  have h2 : ∑ e ∈ J.edges, (J.inner.filter (fun u => u ∈ G₁.ends e)).card = J.edges.card := by
    calc ∑ e ∈ J.edges, (J.inner.filter (fun u => u ∈ G₁.ends e)).card
        = ∑ _e ∈ J.edges, 1 := Finset.sum_congr rfl fun e he => card_filter_inner_ends_duality J he
      _ = J.edges.card := by simp
  omega

lemma sum_outer_deg_eq_edges_card_duality {V₁ E₁ : Type} [Fintype V₁] [DecidableEq V₁]
    [Fintype E₁] [DecidableEq E₁] {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁}
    (J : PathsTreesFlowers.Duality.AltTree G₁) :
    ∑ w ∈ J.outer, (J.edges.filter (fun e => w ∈ G₁.ends e)).card = J.edges.card := by
  have hcomm : ∑ w ∈ J.outer, (J.edges.filter (fun e => w ∈ G₁.ends e)).card =
      ∑ e ∈ J.edges, (J.outer.filter (fun w => w ∈ G₁.ends e)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  calc ∑ w ∈ J.outer, (J.edges.filter (fun e => w ∈ G₁.ends e)).card
      = ∑ e ∈ J.edges, (J.outer.filter (fun w => w ∈ G₁.ends e)).card := hcomm
    _ = ∑ _e ∈ J.edges, 1 := Finset.sum_congr rfl fun e he => card_filter_outer_ends_duality J he
    _ = J.edges.card := by simp

lemma outer_card_eq_inner_card_add_one_duality {V₁ E₁ : Type} [Fintype V₁] [DecidableEq V₁]
    [Fintype E₁] [DecidableEq E₁] {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁}
    (J : PathsTreesFlowers.Duality.AltTree G₁) :
    J.outer.card = J.inner.card + 1 := by
  have hverts : (J.inner ∪ J.outer).card = J.inner.card + J.outer.card :=
    Finset.card_union_of_disjoint J.disjoint
  have hcard := J.card_verts
  have hedges := edges_card_eq_two_mul_inner_duality J
  omega

lemma outer_deg_pos_duality {V₁ E₁ : Type} [Fintype V₁] [DecidableEq V₁]
    [Fintype E₁] [DecidableEq E₁] {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁}
    (J : PathsTreesFlowers.Duality.AltTree G₁) {u_any : V₁} (hu_any : u_any ∈ J.inner)
    {x : V₁} (hx : x ∈ J.outer) :
    1 ≤ (J.edges.filter (fun e => x ∈ G₁.ends e)).card := by
  have hx_verts : x ∈ J.inner ∪ J.outer := Finset.mem_union_right _ hx
  have hu_verts : u_any ∈ J.inner ∪ J.outer := Finset.mem_union_left _ hu_any
  have hpath := J.connected.2 x hx_verts u_any hu_verts
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => exact False.elim (ne_of_mem_inner_of_mem_outer_duality J hu_any hx rfl)
  | head hstep _ _ =>
    rcases hstep with ⟨e, he, hends⟩
    exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, by rw [hends]; simp⟩⟩

lemma exists_leaf_outer_ne_duality {V₁ E₁ : Type} [Fintype V₁] [DecidableEq V₁]
    [Fintype E₁] [DecidableEq E₁] {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁}
    (J : PathsTreesFlowers.Duality.AltTree G₁) {k : ℕ}
    (hinner : J.inner.card = k + 1) {v : V₁} (hv : v ∈ J.outer) :
    ∃ w₀ ∈ J.outer, w₀ ≠ v ∧ (J.edges.filter (fun e => w₀ ∈ G₁.ends e)).card = 1 := by
  obtain ⟨u_any, hu_any⟩ := Finset.card_pos.mp (by omega : 0 < J.inner.card)
  let deg : V₁ → ℕ := fun x => (J.edges.filter (fun e => x ∈ G₁.ends e)).card
  have hsum_all : ∑ x ∈ J.outer, deg x = 2 * (k + 1) := by
    rw [sum_outer_deg_eq_edges_card_duality J, edges_card_eq_two_mul_inner_duality J, hinner]
  have hsum_erase : deg v + ∑ x ∈ J.outer.erase v, deg x = 2 * (k + 1) := by
    rw [Finset.add_sum_erase J.outer deg hv, hsum_all]
  have hdeg_v : 1 ≤ deg v := outer_deg_pos_duality J hu_any hv
  have hcard_erase : (J.outer.erase v).card = k + 1 := by
    have hout := outer_card_eq_inner_card_add_one_duality J
    have herase := Finset.card_erase_of_mem hv
    omega
  have hsum_two : ∑ _x ∈ J.outer.erase v, 2 = 2 * (k + 1) := by
    rw [Finset.sum_const, hcard_erase, smul_eq_mul, Nat.mul_comm]
  have hlt : ∑ x ∈ J.outer.erase v, deg x < ∑ _x ∈ J.outer.erase v, 2 := by
    rw [hsum_two]
    omega
  obtain ⟨w₀, hw₀_erase, hw₀_lt⟩ := Finset.exists_lt_of_sum_lt hlt
  have hw₀_ne : w₀ ≠ v := (Finset.mem_erase.mp hw₀_erase).1
  have hw₀_out : w₀ ∈ J.outer := (Finset.mem_erase.mp hw₀_erase).2
  have hw₀_ge : 1 ≤ deg w₀ := outer_deg_pos_duality J hu_any hw₀_out
  refine ⟨w₀, hw₀_out, hw₀_ne, ?_⟩
  change deg w₀ = 1
  omega

def pruneAltTreeDuality {V₁ E₁ : Type} [Fintype V₁] [DecidableEq V₁]
    [Fintype E₁] [DecidableEq E₁] {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁}
    (J : PathsTreesFlowers.Duality.AltTree G₁)
    (u₀ w₀ w₁ : V₁) (e₀ e₁ : E₁)
    (hu₀ : u₀ ∈ J.inner) (hw₀ : w₀ ∈ J.outer) (hw₁ : w₁ ∈ J.outer)
    (he₀ : e₀ ∈ J.edges) (he₁ : e₁ ∈ J.edges) (he₁_ne_e₀ : e₁ ≠ e₀)
    (hends_e₀ : G₁.ends e₀ = s(u₀, w₀)) (hends_e₁ : G₁.ends e₁ = s(u₀, w₁))
    (he₀_uniq : ∀ e ∈ J.edges, w₀ ∈ G₁.ends e → e = e₀)
    (hu₀_edges : ∀ e ∈ J.edges, u₀ ∈ G₁.ends e → e = e₀ ∨ e = e₁) :
    PathsTreesFlowers.Duality.AltTree G₁ where
  inner := J.inner.erase u₀
  outer := J.outer.erase w₀
  edges := (J.edges.erase e₀).erase e₁
  disjoint := J.disjoint.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
  edge_ends := fun e he => by
    have he_ne_e₁ : e ≠ e₁ := (Finset.mem_erase.mp he).1
    have he_er₀ : e ∈ J.edges.erase e₀ := (Finset.mem_erase.mp he).2
    have he_ne_e₀ : e ≠ e₀ := (Finset.mem_erase.mp he_er₀).1
    have he_J : e ∈ J.edges := (Finset.mem_erase.mp he_er₀).2
    obtain ⟨u, hu, w, hw, hends⟩ := J.edge_ends e he_J
    have hu_ne : u ≠ u₀ := by
      rintro rfl
      have hu_mem : u ∈ G₁.ends e := by rw [hends]; simp
      rcases hu₀_edges e he_J hu_mem with rfl | rfl
      · exact he_ne_e₀ rfl
      · exact he_ne_e₁ rfl
    have hw_ne : w ≠ w₀ := by
      rintro rfl
      have hw_mem : w ∈ G₁.ends e := by rw [hends]; simp
      exact he_ne_e₀ (he₀_uniq e he_J hw_mem)
    exact ⟨u, Finset.mem_erase.mpr ⟨hu_ne, hu⟩, w, Finset.mem_erase.mpr ⟨hw_ne, hw⟩, hends⟩
  inner_deg := fun u hu => by
    have hu_ne : u ≠ u₀ := (Finset.mem_erase.mp hu).1
    have hu_in : u ∈ J.inner := (Finset.mem_erase.mp hu).2
    have hfilt : ((J.edges.erase e₀).erase e₁).filter (fun e => u ∈ G₁.ends e) =
        J.edges.filter (fun e => u ∈ G₁.ends e) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨_, _, he⟩, hue⟩
        exact ⟨he, hue⟩
      · rintro ⟨he, hue⟩
        refine ⟨⟨?_, ?_, he⟩, hue⟩
        · rintro rfl
          rw [hends_e₁, Sym2.mem_iff] at hue
          rcases hue with rfl | rfl
          · exact hu_ne rfl
          · exact ne_of_mem_inner_of_mem_outer_duality J hu_in hw₁ rfl
        · rintro rfl
          rw [hends_e₀, Sym2.mem_iff] at hue
          rcases hue with rfl | rfl
          · exact hu_ne rfl
          · exact ne_of_mem_inner_of_mem_outer_duality J hu_in hw₀ rfl
    rw [hfilt]
    exact J.inner_deg u hu_in
  connected := by
    have hw₁_ne_w₀ : w₁ ≠ w₀ := by
      rintro rfl
      have hw₁_mem : w₁ ∈ G₁.ends e₁ := by rw [hends_e₁]; simp
      exact he₁_ne_e₀ (he₀_uniq e₁ he₁ hw₁_mem)
    have hw₁_mem : w₁ ∈ J.inner.erase u₀ ∪ J.outer.erase w₀ :=
      Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hw₁_ne_w₀, hw₁⟩)
    refine ⟨⟨w₁, hw₁_mem⟩, fun a ha b hb => ?_⟩
    let proj : V₁ → V₁ := fun x => if x = u₀ ∨ x = w₀ then w₁ else x
    have hproj_id : ∀ x ∈ J.inner.erase u₀ ∪ J.outer.erase w₀, proj x = x := by
      intro x hx
      dsimp [proj]
      rw [if_neg]
      rintro (rfl | rfl)
      · rcases Finset.mem_union.mp hx with hx_in | hx_out
        · exact (Finset.mem_erase.mp hx_in).1 rfl
        · exact not_mem_outer_of_mem_inner_duality J hu₀ (Finset.mem_erase.mp hx_out).2
      · rcases Finset.mem_union.mp hx with hx_in | hx_out
        · exact not_mem_inner_of_mem_outer_duality J hw₀ (Finset.mem_erase.mp hx_in).2
        · exact (Finset.mem_erase.mp hx_out).1 rfl
    have hstep : ∀ x y : V₁, (∃ e ∈ J.edges, G₁.ends e = s(x, y)) →
        Relation.ReflTransGen
          (fun p q => ∃ e ∈ (J.edges.erase e₀).erase e₁, G₁.ends e = s(p, q))
          (proj x) (proj y) := by
      rintro x y ⟨e, he, hends⟩
      by_cases he₀_eq : e = e₀
      · subst he₀_eq
        have hxy : (x = u₀ ∧ y = w₀) ∨ (x = w₀ ∧ y = u₀) := by
          rw [← Sym2.eq_iff, ← hends, hends_e₀]
        rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        · have hx_p : proj x = w₁ := if_pos (by tauto)
          have hy_p : proj y = w₁ := if_pos (by tauto)
          rw [hx_p, hy_p]
      · by_cases he₁_eq : e = e₁
        · subst he₁_eq
          have hxy : (x = u₀ ∧ y = w₁) ∨ (x = w₁ ∧ y = u₀) := by
            rw [← Sym2.eq_iff, ← hends, hends_e₁]
          have hw₁_p : proj w₁ = w₁ := by dsimp [proj]; split_ifs <;> rfl
          have hu₀_p : proj u₀ = w₁ := if_pos (Or.inl rfl)
          rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          · rw [hu₀_p, hw₁_p]
        · have he_pruned : e ∈ (J.edges.erase e₀).erase e₁ :=
            Finset.mem_erase.mpr ⟨he₁_eq, Finset.mem_erase.mpr ⟨he₀_eq, he⟩⟩
          have hx_not : ¬ (x = u₀ ∨ x = w₀) := by
            rintro (rfl | rfl)
            · have hx_mem : x ∈ G₁.ends e := by rw [hends]; simp
              rcases hu₀_edges e he hx_mem with rfl | rfl
              · exact he₀_eq rfl
              · exact he₁_eq rfl
            · have hx_mem : x ∈ G₁.ends e := by rw [hends]; simp
              exact he₀_eq (he₀_uniq e he hx_mem)
          have hy_not : ¬ (y = u₀ ∨ y = w₀) := by
            rintro (rfl | rfl)
            · have hy_mem : y ∈ G₁.ends e := by rw [hends]; simp
              rcases hu₀_edges e he hy_mem with rfl | rfl
              · exact he₀_eq rfl
              · exact he₁_eq rfl
            · have hy_mem : y ∈ G₁.ends e := by rw [hends]; simp
              exact he₀_eq (he₀_uniq e he hy_mem)
          have hx_p : proj x = x := if_neg hx_not
          have hy_p : proj y = y := if_neg hy_not
          rw [hx_p, hy_p]
          exact Relation.ReflTransGen.single ⟨e, he_pruned, hends⟩
    have hwalk : ∀ x y : V₁,
        Relation.ReflTransGen (fun p q => ∃ e ∈ J.edges, G₁.ends e = s(p, q)) x y →
        Relation.ReflTransGen
          (fun p q => ∃ e ∈ (J.edges.erase e₀).erase e₁, G₁.ends e = s(p, q))
          (proj x) (proj y) := by
      intro x y hxy
      induction hxy using Relation.ReflTransGen.head_induction_on with
      | refl => exact Relation.ReflTransGen.refl
      | head hst _ ih => exact Relation.ReflTransGen.trans (hstep _ _ hst) ih
    have ha_J : a ∈ J.inner ∪ J.outer :=
      Finset.union_subset_union (Finset.erase_subset _ _) (Finset.erase_subset _ _) ha
    have hb_J : b ∈ J.inner ∪ J.outer :=
      Finset.union_subset_union (Finset.erase_subset _ _) (Finset.erase_subset _ _) hb
    have h_ab := hwalk a b (J.connected.2 a ha_J b hb_J)
    rwa [hproj_id a ha, hproj_id b hb] at h_ab
  card_verts := by
    have hdisj' : Disjoint (J.inner.erase u₀) (J.outer.erase w₀) :=
      J.disjoint.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
    have hverts' : (J.inner.erase u₀ ∪ J.outer.erase w₀).card =
        (J.inner.erase u₀).card + (J.outer.erase w₀).card :=
      Finset.card_union_of_disjoint hdisj'
    have hverts : (J.inner ∪ J.outer).card = J.inner.card + J.outer.card :=
      Finset.card_union_of_disjoint J.disjoint
    have hin_er : (J.inner.erase u₀).card = J.inner.card - 1 := Finset.card_erase_of_mem hu₀
    have hout_er : (J.outer.erase w₀).card = J.outer.card - 1 := Finset.card_erase_of_mem hw₀
    have hin_pos : 1 ≤ J.inner.card := Finset.card_pos.mpr ⟨u₀, hu₀⟩
    have hout_pos : 1 ≤ J.outer.card := Finset.card_pos.mpr ⟨w₀, hw₀⟩
    have he₁_er₀ : e₁ ∈ J.edges.erase e₀ := Finset.mem_erase.mpr ⟨he₁_ne_e₀, he₁⟩
    have hed_er₁ : ((J.edges.erase e₀).erase e₁).card = (J.edges.erase e₀).card - 1 :=
      Finset.card_erase_of_mem he₁_er₀
    have hed_er₀ : (J.edges.erase e₀).card = J.edges.card - 1 :=
      Finset.card_erase_of_mem he₀
    have hed_pos : 2 ≤ J.edges.card := by
      have := edges_card_eq_two_mul_inner_duality J
      omega
    have hcard := J.card_verts
    omega

lemma exists_pruned_plantedTree {V₁ E₁ : Type} [Fintype V₁] [DecidableEq V₁]
    [Fintype E₁] [DecidableEq E₁] {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁}
    {M₁ : Finset E₁} (hM₁ : IsMatching G₁ M₁) {J : AltTree G₁} {r : V₁}
    (hpl : IsPlantedTree G₁ M₁ J r) {k : ℕ} (hinner : J.inner.card = k + 1) :
    ∃ (u₀ w₀ w₁ : V₁) (e₀ e₁ : E₁) (J' : AltTree G₁),
      u₀ ∈ J.inner ∧ w₀ ∈ J.outer ∧ w₀ ≠ r ∧ w₁ ∈ J'.outer ∧ u₀ ≠ w₀ ∧
      e₀ ∈ M₁ ∧ e₁ ∉ M₁ ∧ G₁.ends e₁ = s(w₁, u₀) ∧ G₁.ends e₀ = s(u₀, w₀) ∧
      J'.inner = J.inner.erase u₀ ∧ J'.outer = J.outer.erase w₀ ∧
      J'.verts = J.inner.erase u₀ ∪ J.outer.erase w₀ ∧
      J'.inner.card = k ∧ u₀ ∉ J'.verts ∧ w₀ ∉ J'.verts ∧ J'.verts ⊆ J.verts ∧
      IsPlantedTree G₁ M₁ J' r := by
  let JD := toDualityAltTree J
  obtain ⟨r₀, hr₀_out, hexp_iff⟩ := (lemma_4_2 G₁ J).2.2 (M₁ ∩ J.edges) hpl.max_in
  have hr_eq : r = r₀ := (hexp_iff r hpl.root_mem).mp hpl.root_exposed_in
  have hr_out : r ∈ JD.outer := hr_eq ▸ hr₀_out
  obtain ⟨w₀, hw₀, hw₀_ne_r, hdeg_w₀⟩ := exists_leaf_outer_ne_duality JD hinner hr_out
  obtain ⟨e₀, he₀_filt⟩ := Finset.card_eq_one.mp hdeg_w₀
  have he₀_mem_filt : e₀ ∈ JD.edges.filter (fun e => w₀ ∈ G₁.ends e) := by
    rw [he₀_filt]; exact Finset.mem_singleton_self e₀
  have he₀ : e₀ ∈ JD.edges := (Finset.mem_filter.mp he₀_mem_filt).1
  have hw₀_e₀ : w₀ ∈ G₁.ends e₀ := (Finset.mem_filter.mp he₀_mem_filt).2
  have he₀_uniq : ∀ e ∈ JD.edges, w₀ ∈ G₁.ends e → e = e₀ := by
    intro e he hwe
    have hmem : e ∈ JD.edges.filter (fun f => w₀ ∈ G₁.ends f) := Finset.mem_filter.mpr ⟨he, hwe⟩
    rw [he₀_filt, Finset.mem_singleton] at hmem
    exact hmem
  obtain ⟨u₀, hu₀, w₀', hw₀', hends_e₀'⟩ := JD.edge_ends e₀ he₀
  have hw₀'_eq : w₀' = w₀ := by
    have hmem := hw₀_e₀
    rw [hends_e₀', Sym2.mem_iff] at hmem
    rcases hmem with rfl | rfl
    · exact False.elim (ne_of_mem_inner_of_mem_outer_duality JD hu₀ hw₀ rfl)
    · rfl
  have hends_e₀ : G₁.ends e₀ = s(u₀, w₀) := hw₀'_eq ▸ hends_e₀'
  have hu₀_e₀ : u₀ ∈ G₁.ends e₀ := by rw [hends_e₀]; simp
  have he₀_u₀_filt : e₀ ∈ JD.edges.filter (fun e => u₀ ∈ G₁.ends e) :=
    Finset.mem_filter.mpr ⟨he₀, hu₀_e₀⟩
  have hcard_u₀_erase : ((JD.edges.filter (fun e => u₀ ∈ G₁.ends e)).erase e₀).card = 1 := by
    rw [Finset.card_erase_of_mem he₀_u₀_filt, JD.inner_deg u₀ hu₀]
  obtain ⟨e₁, he₁_filt⟩ := Finset.card_eq_one.mp hcard_u₀_erase
  have he₁_mem_erase : e₁ ∈ (JD.edges.filter (fun e => u₀ ∈ G₁.ends e)).erase e₀ := by
    rw [he₁_filt]; exact Finset.mem_singleton_self e₁
  have he₁_ne_e₀ : e₁ ≠ e₀ := (Finset.mem_erase.mp he₁_mem_erase).1
  have he₁_u₀_filt : e₁ ∈ JD.edges.filter (fun e => u₀ ∈ G₁.ends e) :=
    (Finset.mem_erase.mp he₁_mem_erase).2
  have he₁ : e₁ ∈ JD.edges := (Finset.mem_filter.mp he₁_u₀_filt).1
  have hu₀_e₁ : u₀ ∈ G₁.ends e₁ := (Finset.mem_filter.mp he₁_u₀_filt).2
  have hu₀_edges : ∀ e ∈ JD.edges, u₀ ∈ G₁.ends e → e = e₀ ∨ e = e₁ := by
    intro e he hue
    by_cases he_e₀ : e = e₀
    · exact Or.inl he_e₀
    · have hmem : e ∈ (JD.edges.filter (fun f => u₀ ∈ G₁.ends f)).erase e₀ :=
        Finset.mem_erase.mpr ⟨he_e₀, Finset.mem_filter.mpr ⟨he, hue⟩⟩
      rw [he₁_filt, Finset.mem_singleton] at hmem
      exact Or.inr hmem
  obtain ⟨u₀', hu₀', w₁, hw₁, hends_e₁'⟩ := JD.edge_ends e₁ he₁
  have hu₀'_eq : u₀' = u₀ := by
    have hmem := hu₀_e₁
    rw [hends_e₁', Sym2.mem_iff] at hmem
    rcases hmem with rfl | rfl
    · rfl
    · exact False.elim (ne_of_mem_inner_of_mem_outer_duality JD hu₀ hw₁ rfl)
  have hends_e₁ : G₁.ends e₁ = s(u₀, w₁) := hu₀'_eq ▸ hends_e₁'
  let JD' := pruneAltTreeDuality JD u₀ w₀ w₁ e₀ e₁ hu₀ hw₀ hw₁ he₀ he₁ he₁_ne_e₀
    hends_e₀ hends_e₁ he₀_uniq hu₀_edges
  let J' := ofDualityAltTree JD'
  have hw₁_ne_w₀ : w₁ ≠ w₀ := by
    rintro rfl
    have hw₁_mem : w₁ ∈ G₁.ends e₁ := by rw [hends_e₁]; simp
    exact he₁_ne_e₀ (he₀_uniq e₁ he₁ hw₁_mem)
  have hw₁_J' : w₁ ∈ J'.outer := Finset.mem_erase.mpr ⟨hw₁_ne_w₀, hw₁⟩
  have hu₀_ne_w₀ : u₀ ≠ w₀ := ne_of_mem_inner_of_mem_outer_duality JD hu₀ hw₀
  have hw₀_verts : w₀ ∈ J.verts := by
    rw [J.verts_eq]; exact Finset.mem_union_right _ hw₀
  have hnot_exp_w₀ : ¬ PathsTreesFlowers.Duality.IsExposed G₁ (M₁ ∩ J.edges) w₀ :=
    fun hexp => hw₀_ne_r ((hexp_iff w₀ hw₀_verts).mp hexp ▸ hr_eq.symm)
  simp only [PathsTreesFlowers.Duality.IsExposed, not_forall, not_not] at hnot_exp_w₀
  rcases hnot_exp_w₀ with ⟨f, hf, hwf⟩
  have hf_eq_e₀ : f = e₀ := he₀_uniq f (Finset.mem_inter.mp hf).2 hwf
  have he₀_MJ : e₀ ∈ M₁ ∩ J.edges := hf_eq_e₀ ▸ hf
  have he₀_M₁ : e₀ ∈ M₁ := (Finset.mem_inter.mp he₀_MJ).1
  have he₁_not_M₁ : e₁ ∉ M₁ := by
    intro he₁_M₁
    exact hM₁ e₁ he₁_M₁ e₀ he₀_M₁ he₁_ne_e₀ u₀ hu₀_e₁ hu₀_e₀
  have hinter_J' : M₁ ∩ J'.edges = (M₁ ∩ J.edges).erase e₀ := by
    ext e
    change e ∈ M₁ ∩ ((J.edges.erase e₀).erase e₁) ↔ e ∈ (M₁ ∩ J.edges).erase e₀
    simp only [Finset.mem_inter, Finset.mem_erase]
    constructor
    · rintro ⟨heM, _, he_ne₀, heJ⟩
      exact ⟨he_ne₀, heM, heJ⟩
    · rintro ⟨he_ne₀, heM, heJ⟩
      have he_ne₁ : e ≠ e₁ := fun h => he₁_not_M₁ (h ▸ heM)
      exact ⟨heM, he_ne₁, he_ne₀, heJ⟩
  have hu₀_not_J' : u₀ ∉ J'.verts := by
    change u₀ ∉ J.inner.erase u₀ ∪ J.outer.erase w₀
    rw [Finset.mem_union, Finset.mem_erase, Finset.mem_erase]
    rintro (⟨hne, _⟩ | ⟨_, hmem⟩)
    · exact hne rfl
    · exact not_mem_outer_of_mem_inner_duality JD hu₀ hmem
  have hw₀_not_J' : w₀ ∉ J'.verts := by
    change w₀ ∉ J.inner.erase u₀ ∪ J.outer.erase w₀
    rw [Finset.mem_union, Finset.mem_erase, Finset.mem_erase]
    rintro (⟨_, hmem⟩ | ⟨hne, _⟩)
    · exact not_mem_inner_of_mem_outer_duality JD hw₀ hmem
    · exact hne rfl
  have hverts_sub : J'.verts ⊆ J.verts := by
    rw [J.verts_eq]
    exact Finset.union_subset_union (Finset.erase_subset _ _) (Finset.erase_subset _ _)
  have hJ'_inner_card : J'.inner.card = k := by
    change (JD.inner.erase u₀).card = k
    rw [Finset.card_erase_of_mem hu₀]
    change J.inner.card - 1 = k
    omega
  have hpl' : IsPlantedTree G₁ M₁ J' r := by
    refine ⟨⟨Finset.inter_subset_right, ?_, ?_⟩, ?_, ?_, hpl.root_exposed⟩
    · intro a ha b hb
      exact hM₁ a (Finset.mem_inter.mp ha).1 b (Finset.mem_inter.mp hb).1
    · intro N' hN'_sub hN'_match
      have hu₀_exp_N' : PathsTreesFlowers.Duality.IsExposed G₁ N' u₀ := by
        intro e he hue
        exact hu₀_not_J' (J'.toSub.ends_mem e (hN'_sub he) u₀ hue)
      have hw₀_exp_N' : PathsTreesFlowers.Duality.IsExposed G₁ N' w₀ := by
        intro e he hwe
        exact hw₀_not_J' (J'.toSub.ends_mem e (hN'_sub he) w₀ hwe)
      obtain ⟨he₀_not_N', hins_match, hins_card⟩ :=
        isMatching_insert_of_isExposed hN'_match hends_e₀ hu₀_exp_N' hw₀_exp_N'
      have hins_sub : insert e₀ N' ⊆ J.edges := by
        intro e he
        rcases Finset.mem_insert.mp he with rfl | heN'
        · exact he₀
        · have heJ' : e ∈ (J.edges.erase e₀).erase e₁ := hN'_sub heN'
          exact (Finset.mem_erase.mp (Finset.mem_erase.mp heJ').2).2
      have hle := hpl.max_in.2.2 (insert e₀ N') hins_sub hins_match
      have hcard_er := Finset.card_erase_add_one he₀_MJ
      rw [hinter_J']
      omega
    · change r ∈ J.inner.erase u₀ ∪ J.outer.erase w₀
      exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hw₀_ne_r.symm, hr_out⟩)
    · intro e he
      rw [hinter_J'] at he
      exact hpl.root_exposed_in e (Finset.mem_erase.mp he).2
  exact ⟨u₀, w₀, w₁, e₀, e₁, J', hu₀, hw₀, hw₀_ne_r, hw₁_J', hu₀_ne_w₀,
    he₀_M₁, he₁_not_M₁, hends_e₁.trans Sym2.eq_swap, hends_e₀,
    rfl, rfl, rfl, hJ'_inner_card, hu₀_not_J', hw₀_not_J', hverts_sub, hpl'⟩

lemma isPath_append_one {V₁ E₁ : Type} [DecidableEq V₁] [DecidableEq E₁]
    {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁} :
    ∀ {vs : List V₁} {es : List E₁} {w z : V₁} {e : E₁},
      PathsTreesFlowers.Duality.IsPath G₁ vs es →
      vs.getLast? = some w →
      z ∉ vs →
      G₁.ends e = s(w, z) →
      PathsTreesFlowers.Duality.IsPath G₁ (vs ++ [z]) (es ++ [e])
  | [], _, _, _, _, _, hlast, _, _ => by cases hlast
  | [a], [], w, z, e, _, hlast, hz_not, hends => by
    simp only [List.getLast?_singleton, Option.some.injEq] at hlast
    subst hlast
    have hne : a ≠ z := fun h => hz_not (h ▸ List.mem_singleton.mpr rfl)
    refine ⟨?_, rfl, ?_⟩
    · simp [hne]
    · simp [hends]
  | [_], _ :: _, _, _, _, hP, _, _, _ => by
    have := hP.2.1; simp at this
  | _ :: _ :: _, [], _, _, _, hP, _, _, _ => by
    have := hP.2.1; simp at this
  | a :: b :: vs', f :: es', w, z, e, hP, hlast, hz_not, hends => by
    have hnodup_cons := List.nodup_cons.mp hP.1
    have ha_not_vs : a ∉ b :: vs' := hnodup_cons.1
    have hnodup_tail : (b :: vs').Nodup := hnodup_cons.2
    have hlen_tail : (b :: vs').length = es'.length + 1 := by
      have := hP.2.1; simp only [List.length_cons] at this ⊢; omega
    have hmap_cons := hP.2.2
    simp only [List.map_cons, List.tail_cons, List.zipWith_cons_cons, List.cons.injEq] at hmap_cons
    have hP_tail : PathsTreesFlowers.Duality.IsPath G₁ (b :: vs') es' :=
      ⟨hnodup_tail, hlen_tail, hmap_cons.2⟩
    have hlast_tail : (b :: vs').getLast? = some w := by
      simpa using hlast
    have hz_not_tail : z ∉ b :: vs' := fun h => hz_not (List.mem_cons_of_mem a h)
    have ha_ne_z : a ≠ z := fun h => hz_not (h ▸ List.mem_cons_self)
    have ih := isPath_append_one hP_tail hlast_tail hz_not_tail hends
    change PathsTreesFlowers.Duality.IsPath G₁ (a :: ((b :: vs') ++ [z])) (f :: (es' ++ [e]))
    refine ⟨List.nodup_cons.mpr ⟨?_, ih.1⟩, ?_, ?_⟩
    · intro ha_mem
      rcases List.mem_append.mp ha_mem with h1 | h2
      · exact ha_not_vs h1
      · simp only [List.mem_singleton] at h2
        exact ha_ne_z h2
    · simp only [List.length_cons, ih.2.1]
    · change G₁.ends f :: (es' ++ [e]).map G₁.ends =
        s(a, b) :: List.zipWith (fun x y => s(x, y)) (b :: vs' ++ [z]) (b :: vs' ++ [z]).tail
      rw [hmap_cons.1, ih.2.2]

lemma isChain_append_one {α : Type} {R : α → α → Prop} :
    ∀ {l : List α} {x : α},
      l.IsChain R →
      (∀ y ∈ l.getLast?, R y x) →
      (l ++ [x]).IsChain R
  | [], _, _, _ => List.IsChain.singleton _
  | [a], x, _, h => List.IsChain.cons_cons (h a rfl) (List.IsChain.singleton x)
  | _ :: _ :: _, _, List.IsChain.cons_cons hab hbt, h =>
    List.IsChain.cons_cons hab (isChain_append_one hbt h)

lemma isStem_append_two {V₁ E₁ : Type} [DecidableEq V₁] [DecidableEq E₁]
    {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁} {M₁ : Finset E₁}
    {svs : List V₁} {ses : List E₁} {w₁ u₀ w₀ : V₁} {e₁ e₀ : E₁}
    (hSt : PathsTreesFlowers.Duality.IsStem G₁ M₁ svs ses)
    (hlast : svs.getLast? = some w₁)
    (hu₀_not : u₀ ∉ svs) (hw₀_not : w₀ ∉ svs) (huw : u₀ ≠ w₀)
    (hends₁ : G₁.ends e₁ = s(w₁, u₀)) (hends₀ : G₁.ends e₀ = s(u₀, w₀))
    (he₁_not : e₁ ∉ M₁) (he₀_mem : e₀ ∈ M₁) :
    PathsTreesFlowers.Duality.IsStem G₁ M₁ (svs ++ [u₀, w₀]) (ses ++ [e₁, e₀]) := by
  have hP₁ := isPath_append_one hSt.1.1 hlast hu₀_not hends₁
  have hlast₁ : (svs ++ [u₀]).getLast? = some u₀ := by simp
  have hw₀_not₁ : w₀ ∉ svs ++ [u₀] := by
    rw [List.mem_append, List.mem_singleton]
    rintro (h | rfl)
    · exact hw₀_not h
    · exact huw rfl
  have hP₂ := isPath_append_one hP₁ hlast₁ hw₀_not₁ hends₀
  have hC₁ : (ses ++ [e₁]).IsChain (fun a b => a ∈ M₁ ↔ b ∉ M₁) :=
    isChain_append_one hSt.1.2 fun y hy => by
      have hyM : y ∈ M₁ := hSt.2.2 y hy
      exact ⟨fun _ => he₁_not, fun _ => hyM⟩
  have hC₂ : ((ses ++ [e₁]) ++ [e₀]).IsChain (fun a b => a ∈ M₁ ↔ b ∉ M₁) :=
    isChain_append_one hC₁ fun y hy => by
      simp only [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil e₁ []),
        List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hy
      subst hy
      exact ⟨fun h => False.elim (he₁_not h), fun h => False.elim (h he₀_mem)⟩
  rw [List.append_assoc, List.append_assoc] at hP₂
  rw [List.append_assoc] at hC₂
  have hsvs_ne : svs ≠ [] := by
    rintro rfl; cases hlast
  refine ⟨⟨hP₂, hC₂⟩, ?_, ?_⟩
  · intro r hr
    rw [List.head?_append_of_ne_nil svs hsvs_ne] at hr
    exact hSt.2.1 r hr
  · intro e he
    have h_eq : (ses ++ [e₁, e₀]).getLast? = some e₀ := by
      change (ses ++ ([e₁] ++ [e₀])).getLast? = some e₀
      rw [← List.append_assoc]
      simp
    rw [h_eq, Option.mem_def, Option.some.injEq] at he
    exact he ▸ he₀_mem

lemma isExposed_of_mem_outer_of_inner_card_zero {V₁ E₁ : Type} [Fintype V₁] [DecidableEq V₁]
    [Fintype E₁] [DecidableEq E₁] {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁}
    {M₁ : Finset E₁} {J : AltTree G₁} {r : V₁}
    (hpl : IsPlantedTree G₁ M₁ J r) (hinner : J.inner.card = 0)
    {w : V₁} (hw : w ∈ J.outer) :
    w = r ∧ PathsTreesFlowers.Duality.IsExposed G₁ M₁ w := by
  obtain ⟨r₀, hr₀_out, hexp_iff⟩ := (lemma_4_2 G₁ J).2.2 (M₁ ∩ J.edges) hpl.max_in
  have hr_eq : r = r₀ := (hexp_iff r hpl.root_mem).mp hpl.root_exposed_in
  have hr_out : r ∈ J.outer := hr_eq ▸ hr₀_out
  have hout_card : J.outer.card = 1 := by
    rw [(lemma_4_2 G₁ J).1, hinner]
  have hwr : w = r := Finset.card_le_one.mp (by omega) w hw r hr_out
  exact ⟨hwr, hwr ▸ hpl.root_exposed⟩

lemma exists_stem_of_mem_outer_aux {V₁ E₁ : Type} [Fintype V₁] [DecidableEq V₁]
    [Fintype E₁] [DecidableEq E₁] {G₁ : EdmondsMatching65.Polyhedron.Graph V₁ E₁}
    {M₁ : Finset E₁} (hM₁ : IsMatching G₁ M₁) :
    ∀ (k : ℕ) (J : AltTree G₁) (r : V₁),
      IsPlantedTree G₁ M₁ J r →
      J.inner.card = k →
      ∀ w ∈ J.outer,
        ∃ (svs : List V₁) (ses : List E₁),
          PathsTreesFlowers.Duality.IsStem G₁ M₁ svs ses ∧
          svs.getLast? = some w ∧
          (∀ x ∈ svs, x ∈ J.verts)
  | 0, J, r, hpl, hinner, w, hw => by
    obtain ⟨hwr, hw_exp⟩ := isExposed_of_mem_outer_of_inner_card_zero hpl hinner hw
    subst hwr
    refine ⟨[w], [], isStem_singleton hw_exp, rfl, ?_⟩
    intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    exact hpl.root_mem
  | k + 1, J, r, hpl, hinner, w, hw => by
    obtain ⟨u₀, w₀, w₁, e₀, e₁, J', hu₀, hw₀, _hw₀_ne_r, hw₁_J', huw,
      he₀_M₁, he₁_not_M₁, hends_e₁, hends_e₀,
      _hJ'_in, hJ'_out, _hJ'_verts, hJ'_card, hu₀_not_J', hw₀_not_J', hverts_sub, hpl'⟩ :=
      exists_pruned_plantedTree hM₁ hpl hinner
    by_cases hww₀ : w = w₀
    · subst hww₀
      obtain ⟨svs₁, ses₁, hSt₁, hlast₁, hsub₁⟩ :=
        exists_stem_of_mem_outer_aux hM₁ k J' r hpl' hJ'_card w₁ hw₁_J'
      have hu₀_not_svs : u₀ ∉ svs₁ := fun h => hu₀_not_J' (hsub₁ u₀ h)
      have hw₀_not_svs : w ∈ J.outer ∧ w ∉ svs₁ := ⟨hw₀, fun h => hw₀_not_J' (hsub₁ w h)⟩
      have hSt := isStem_append_two hSt₁ hlast₁ hu₀_not_svs hw₀_not_svs.2 huw
        hends_e₁ hends_e₀ he₁_not_M₁ he₀_M₁
      refine ⟨svs₁ ++ [u₀, w], ses₁ ++ [e₁, e₀], hSt, by simp, ?_⟩
      intro x hx
      rcases List.mem_append.mp hx with hx₁ | hx₂
      · exact hverts_sub (hsub₁ x hx₁)
      · rw [J.verts_eq]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx₂
        rcases hx₂ with rfl | rfl
        · exact Finset.mem_union_left _ hu₀
        · exact Finset.mem_union_right _ hw₀
    · have hw_J' : w ∈ J'.outer := by
        rw [hJ'_out]; exact Finset.mem_erase.mpr ⟨hww₀, hw⟩
      obtain ⟨svs, ses, hSt, hlast, hsub⟩ :=
        exists_stem_of_mem_outer_aux hM₁ k J' r hpl' hJ'_card w hw_J'
      exact ⟨svs, ses, hSt, hlast, fun x hx => hverts_sub (hsub x hx)⟩

lemma lemma_4_15_ext_aux {G : EdmondsMatching65.Polyhedron.Graph V E}
    {M : Finset E} (hM : IsMatching G M) (n : ℕ) :
    ∀ (K : ℕ) (P : Finpartition (Finset.univ : Finset V))
      (J : Fin n → AltTree (shrink G P)),
      (∑ i : Fin n, (J i).inner.card) = K →
      (∀ U ∈ P.parts, 1 < U.card →
        ∃ u ∈ U, ∀ w ∈ U, (PathsTreesFlowers.Duality.IsExposed G (M ∩ (induced G U).edges) w ↔ w = u)) →
      PathsTreesFlowers.Duality.IsMaxMatching (shrink G P) (shrinkMatching G P M) →
      (∀ i, ∃ r, IsPlantedTree (shrink G P) (shrinkMatching G P M) (J i) r) →
      (∀ i j, i ≠ j → Disjoint (J i).verts (J j).verts) →
      (∀ (U : Finset V) (hU : U ∈ P.parts), 1 < U.card → ∃ i, ⟨U, hU⟩ ∈ (J i).outer) →
      PathsTreesFlowers.Duality.IsMaxMatching G M
  | 0, P, J, hK, h1, h2, hJ, _hdisj, h3 => by
    have hzero : ∀ i : Fin n, (J i).inner.card = 0 :=
      fun i => Finset.sum_eq_zero_iff.mp hK i (Finset.mem_univ i)
    refine isMaxMatching_of_all_gt_one_exposed_aux hM
      (P.parts.filter (fun U => 1 < U.card)).card P rfl h1 h2 ?_
    intro U hU hU_card
    obtain ⟨i, hi⟩ := h3 U hU hU_card
    obtain ⟨r, hpl⟩ := hJ i
    exact (isExposed_of_mem_outer_of_inner_card_zero hpl (hzero i) hi).2
  | K + 1, P, J, hK, h1, h2, hJ, hdisj, h3 => by
    have hpos : ∃ i ∈ (Finset.univ : Finset (Fin n)), 0 < (J i).inner.card := by
      by_contra hnot
      have h0 : ∑ i : Fin n, (J i).inner.card = 0 :=
        Finset.sum_eq_zero fun i hi => Nat.eq_zero_of_not_pos fun hp => hnot ⟨i, hi, hp⟩
      omega
    rcases hpos with ⟨i₀, _, hi₀_pos⟩
    obtain ⟨r₀, hpl₀⟩ := hJ i₀
    have hk₀ : (J i₀).inner.card = ((J i₀).inner.card - 1) + 1 := by omega
    obtain ⟨u₀, w₀, w₁, e₀, e₁, J'₀, _hu₀, hw₀, _hw₀_ne_r, _hw₁_J', _huw,
      _he₀_M₁, _he₁_not_M₁, _hends_e₁, _hends_e₀,
      _hJ'_in, hJ'_out, _hJ'_verts, hJ'_card, _hu₀_not_J', hw₀_not_J', hverts_sub, hpl'₀⟩ :=
      exists_pruned_plantedTree h2.1 hpl₀ hk₀
    let J₁ : Fin n → AltTree (shrink G P) := fun i => if i = i₀ then J'₀ else J i
    have hK₁ : (∑ i : Fin n, (J₁ i).inner.card) = K := by
      have hsum_er := Finset.add_sum_erase (Finset.univ : Finset (Fin n))
        (fun i => (J₁ i).inner.card) (Finset.mem_univ i₀)
      have hsum_er_J := Finset.add_sum_erase (Finset.univ : Finset (Fin n))
        (fun i => (J i).inner.card) (Finset.mem_univ i₀)
      have hcongr : ∑ i ∈ Finset.univ.erase i₀, (J₁ i).inner.card =
          ∑ i ∈ Finset.univ.erase i₀, (J i).inner.card := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hne : i ≠ i₀ := (Finset.mem_erase.mp hi).1
        dsimp [J₁]; rw [if_neg hne]
      have hJ₁_i₀ : (J₁ i₀).inner.card = (J i₀).inner.card - 1 := by
        dsimp [J₁]; rw [if_pos rfl, hJ'_card]
      omega
    have hJ₁_pl : ∀ i, ∃ r, IsPlantedTree (shrink G P) (shrinkMatching G P M) (J₁ i) r := by
      intro i
      by_cases hi : i = i₀
      · subst hi; dsimp [J₁]; rw [if_pos rfl]; exact ⟨r₀, hpl'₀⟩
      · dsimp [J₁]; rw [if_neg hi]; exact hJ i
    have hJ₁_sub : ∀ i, (J₁ i).verts ⊆ (J i).verts := by
      intro i
      by_cases hi : i = i₀
      · subst hi; dsimp [J₁]; rw [if_pos rfl]; exact hverts_sub
      · dsimp [J₁]; rw [if_neg hi]
    have hJ₁_disj : ∀ i j, i ≠ j → Disjoint (J₁ i).verts (J₁ j).verts :=
      fun i j hij => (hdisj i j hij).mono (hJ₁_sub i) (hJ₁_sub j)
    have hw₀_not_J₁ : ∀ i, w₀ ∉ (J₁ i).verts := by
      intro i
      by_cases hi : i = i₀
      · subst hi; dsimp [J₁]; rw [if_pos rfl]; exact hw₀_not_J'
      · intro hmem
        have hw₀_i₀ : w₀ ∈ (J i₀).verts := by
          rw [(J i₀).verts_eq]; exact Finset.mem_union_right _ hw₀
        exact Finset.disjoint_left.mp (hdisj i₀ i (Ne.symm hi)) hw₀_i₀ (hJ₁_sub i hmem)
    have hJ₁_outer_of_ne : ∀ i (w : {U // U ∈ P.parts}), w ≠ w₀ → w ∈ (J i).outer → w ∈ (J₁ i).outer := by
      intro i w hne hw
      by_cases hi : i = i₀
      · subst hi; dsimp [J₁]; rw [if_pos rfl, hJ'_out]; exact Finset.mem_erase.mpr ⟨hne, hw⟩
      · dsimp [J₁]; rw [if_neg hi]; exact hw
    by_cases hcard_w₀ : 1 < w₀.1.card
    · let U₀ := w₀.1
      have hU₀ : U₀ ∈ P.parts := w₀.2
      have hw₀_eq : (⟨U₀, hU₀⟩ : {W // W ∈ P.parts}) = w₀ := rfl
      obtain ⟨svs, ses, hSt, hlast, _⟩ :=
        exists_stem_of_mem_outer_aux h2.1 (J i₀).inner.card (J i₀) r₀ hpl₀ rfl w₀ hw₀
      have h2' := isMaxMatching_splitPart_of_stem hU₀ hM (h1 U₀ hU₀ hcard_w₀) h2 hSt hlast
      let J₂ : Fin n → AltTree (shrink G (splitPart P U₀)) :=
        fun i => liftAltTree P hU₀ (J₁ i) (hw₀_not_J₁ i)
      have hK₂ : (∑ i : Fin n, (J₂ i).inner.card) = K := by
        rw [← hK₁]
        refine Finset.sum_congr rfl fun i _ => ?_
        change ((J₁ i).inner.map _).card = (J₁ i).inner.card
        exact Finset.card_map _
      have h1' : ∀ W ∈ (splitPart P U₀).parts, 1 < W.card →
          ∃ u ∈ W, ∀ w ∈ W,
            (PathsTreesFlowers.Duality.IsExposed G (M ∩ (induced G W).edges) w ↔ w = u) := by
        intro W hW hW_card
        have hW_filt : W ∈ (splitPart P U₀).parts.filter (fun X => 1 < X.card) :=
          Finset.mem_filter.mpr ⟨hW, hW_card⟩
        rw [splitPart_parts_filter_one_lt_card P hU₀] at hW_filt
        exact h1 W (Finset.mem_filter.mp (Finset.mem_erase.mp hW_filt).2).1 hW_card
      have hJ₂_pl : ∀ i, ∃ r, IsPlantedTree (shrink G (splitPart P U₀))
          (shrinkMatching G (splitPart P U₀) M) (J₂ i) r := by
        intro i
        obtain ⟨r, hpl⟩ := hJ₁_pl i
        exact ⟨liftPart P hU₀ r, isPlantedTree_liftAltTree P hU₀ (J₁ i) (hw₀_not_J₁ i) hpl⟩
      have hJ₂_disj : ∀ i j, i ≠ j → Disjoint (J₂ i).verts (J₂ j).verts := by
        intro i j hij
        change Disjoint ((J₁ i).verts.map _) ((J₁ j).verts.map _)
        rw [Finset.disjoint_left]
        intro z hz₁ hz₂
        rcases Finset.mem_map.mp hz₁ with ⟨x₁, hx₁, rfl⟩
        rcases Finset.mem_map.mp hz₂ with ⟨x₂, hx₂, heq⟩
        rw [liftPart_injective P hU₀ heq] at hx₂
        exact Finset.disjoint_left.mp (hJ₁_disj i j hij) hx₁ hx₂
      have h3' : ∀ (W : Finset V) (hW : W ∈ (splitPart P U₀).parts), 1 < W.card →
          ∃ i, ⟨W, hW⟩ ∈ (J₂ i).outer := by
        intro W hW hW_card
        have hW_filt : W ∈ (splitPart P U₀).parts.filter (fun X => 1 < X.card) :=
          Finset.mem_filter.mpr ⟨hW, hW_card⟩
        rw [splitPart_parts_filter_one_lt_card P hU₀] at hW_filt
        have hW_ne : W ≠ U₀ := (Finset.mem_erase.mp hW_filt).1
        have hWP : W ∈ P.parts := (Finset.mem_filter.mp (Finset.mem_erase.mp hW_filt).2).1
        obtain ⟨i, hi⟩ := h3 W hWP hW_card
        have hsub_ne : (⟨W, hWP⟩ : {X // X ∈ P.parts}) ≠ w₀ :=
          fun h => hW_ne (congrArg Subtype.val h)
        have hi₁ : ⟨W, hWP⟩ ∈ (J₁ i).outer := hJ₁_outer_of_ne i ⟨W, hWP⟩ hsub_ne hi
        have h_lift_eq : liftPart P hU₀ ⟨W, hWP⟩ = ⟨W, hW⟩ :=
          Subtype.ext (liftPart_val_of_ne P hU₀ hsub_ne)
        refine ⟨i, ?_⟩
        change ⟨W, hW⟩ ∈ (J₁ i).outer.map ⟨liftPart P hU₀, liftPart_injective P hU₀⟩
        rw [← h_lift_eq]
        exact Finset.mem_map_of_mem _ hi₁
      exact lemma_4_15_ext_aux hM n K (splitPart P U₀) J₂ hK₂ h1' h2' hJ₂_pl hJ₂_disj h3'
    · refine lemma_4_15_ext_aux hM n K P J₁ hK₁ h1 h2 hJ₁_pl hJ₁_disj ?_
      intro U hU hU_card
      obtain ⟨i, hi⟩ := h3 U hU hU_card
      have hne : (⟨U, hU⟩ : {W // W ∈ P.parts}) ≠ w₀ := by
        intro h
        exact hcard_w₀ (congrArg Subtype.val h ▸ hU_card)
      exact ⟨i, hJ₁_outer_of_ne i ⟨U, hU⟩ hne hi⟩

end SolPathsTreesFlowersLemma415Ext

open EdmondsMatching65.Polyhedron (IsMatching)
open PathsTreesFlowers.Invariance

/-- 4.15, extension (p. 459), in the forest form of 4.20 (p. 460). Let `M` be a matching of `G`
and let the parts of `P` with more than one vertex be the disjoint subgraphs `P₁, …, Pₙ`, each
inducing a connected subgraph, such that (1) `M ∩ Pᵢ⁺` leaves exactly one exposed vertex in `Pᵢ`,
(2) `M/P` is a maximum matching of `G/P`, and (3) the vertices `Pᵢ/Pᵢ` are outer vertices of a
planted forest for `(G/P, M/P)`. Then `M` is a maximum matching of `G`. -/
theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (M : Finset E) (hM : IsMatching G M) (P : Finpartition (Finset.univ : Finset V))
    (_hconn : ∀ U ∈ P.parts, (induced G U).Connected)
    (h1 : ∀ U ∈ P.parts, 1 < U.card →
      ∃ u ∈ U, ∀ w ∈ U, (PathsTreesFlowers.Duality.IsExposed G (M ∩ (induced G U).edges) w ↔ w = u))
    (h2 : PathsTreesFlowers.Duality.IsMaxMatching (shrink G P) (shrinkMatching G P M))
    (n : ℕ) (J : Fin n → AltTree (shrink G P))
    (hJ : ∀ i, ∃ r, IsPlantedTree (shrink G P) (shrinkMatching G P M) (J i) r)
    (hdisj : ∀ i j, i ≠ j → Disjoint (J i).verts (J j).verts)
    (h3 : ∀ (U : Finset V) (hU : U ∈ P.parts), 1 < U.card → ∃ i, ⟨U, hU⟩ ∈ (J i).outer) :
    PathsTreesFlowers.Duality.IsMaxMatching G M :=
  SolPathsTreesFlowersLemma415Ext.lemma_4_15_ext_aux hM n
    (∑ i : Fin n, (J i).inner.card) P J rfl h1 h2 hJ hdisj h3


