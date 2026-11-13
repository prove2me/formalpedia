-- Prove2me | solution 1 for TangleStructTree.corollary_3_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:55:41.883214+00:00
-- url     : https://prove2.me/submissions/a61f3ddb-afdd-44ef-885f-41af3abe50cf

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsOrientation
import Definitions.Def_TangleStructTree_IsConsistent
import Definitions.Def_TangleStructTree_sepClosure
import Definitions.Def_TangleStructTree_SepTree

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TangleStructTree.Dev.Base

open TangleStructTree SepSystem

variable {E : Type*} [PartialOrder E] [SepSystem E]

lemma pairwise_path (T : SepTree E) :
    ∀ v ∈ T.nodes, v.Pairwise (fun a b => a ≠ b ∧ a ≠ rev b) := by
  intro v
  induction v with
  | nil => intro _; exact List.Pairwise.nil
  | cons x u ih =>
    intro h
    have hu := T.parent_mem x u h
    refine List.pairwise_cons.mpr ⟨?_, ih hu⟩
    obtain ⟨s, hs, hy⟩ := T.split u hu ⟨x, h⟩
    intro y hy'
    have hxs := (hs x).mp h
    obtain ⟨h1, h2⟩ := hy y hy'
    rcases hxs with rfl | rfl
    · exact ⟨fun h => h1 h.symm, fun h => h2 (by rw [h, rev_rev])⟩
    · refine ⟨fun h => h2 h.symm, fun h => h1 ?_⟩
      have := congrArg rev h
      simp only [rev_rev] at this
      exact this.symm

end TangleStructTree.Dev.Base
end

section
set_option autoImplicit false

namespace TangleStructTree.Dev.C35

open TangleStructTree SepSystem TangleStructTree.Dev.Base

variable {E : Type*} [PartialOrder E] [SepSystem E]

lemma length_le [Finite E] (T : SepTree E) {v : List E} (hv : v ∈ T.nodes) :
    v.length ≤ (Unoriented E).ncard := by
  classical
  have hpw := pairwise_path T v hv
  let f : E → Set E := fun x => ({x, rev x} : Set E)
  have hnd : (v.map f).Nodup := by
    refine List.Pairwise.map f (fun a b h hab => ?_) hpw
    have hb' : b ∈ ({a, rev a} : Set E) := by
      rw [show ({a, rev a} : Set E) = f a from rfl, hab]; simp [f]
    rcases hb' with h' | h'
    · exact h.1 h'.symm
    · exact h.2 (by rw [h', rev_rev])
  have hsub : ((v.map f).toFinset : Set (Set E)) ⊆ Unoriented E := by
    intro s hs
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map] at hs
    obtain ⟨x, -, rfl⟩ := hs
    exact ⟨x, rfl⟩
  have hfin : (Unoriented E).Finite := Set.finite_range _
  have := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, List.length_map] at this
  exact this

lemma fiber_le (T : SepTree E) (u : List E) (hu : u ∈ T.nodes) [DecidableEq E] :
    (T.nodes.filter fun v => v.tail = u ∧ v ≠ []).card ≤ 2 := by
  by_cases hex : ∃ x, x :: u ∈ T.nodes
  · obtain ⟨s, hs, -⟩ := T.split u hu hex
    refine (Finset.card_le_card (t := {s :: u, rev s :: u}) ?_).trans Finset.card_le_two
    intro v hv
    simp only [Finset.mem_filter] at hv
    obtain ⟨hvn, hvt, hne⟩ := hv
    obtain ⟨x, w, rfl⟩ := List.exists_cons_of_ne_nil hne
    simp only [List.tail_cons] at hvt
    subst hvt
    have := (hs x).mp hvn
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases this with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])
  · push_neg at hex
    have : (T.nodes.filter fun v => v.tail = u ∧ v ≠ []) = ∅ := by
      ext v
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hvn hvt hne
      obtain ⟨x, w, rfl⟩ := List.exists_cons_of_ne_nil hne
      simp only [List.tail_cons] at hvt
      subst hvt
      exact hex x hvn
    rw [this]; simp


section counting
open Classical

/-- nodes of length `d` -/
noncomputable def lev (T : SepTree E) (d : ℕ) : Finset (List E) := T.nodes.filter fun v => v.length = d

/-- internal nodes of length `d` -/
noncomputable def inte (T : SepTree E) (d : ℕ) : Finset (List E) :=
  (lev T d).filter fun v => ∃ x, x :: v ∈ T.nodes

/-- leaves of length `d` -/
noncomputable def lvs (T : SepTree E) (d : ℕ) : Finset (List E) :=
  (lev T d).filter fun v => ¬ ∃ x, x :: v ∈ T.nodes

lemma lev_succ_le (T : SepTree E) (d : ℕ) : (lev T (d + 1)).card ≤ 2 * (inte T d).card := by
  classical
  have hfib : ∀ a ∈ (lev T (d + 1)).image List.tail,
      ((lev T (d + 1)).filter fun x => x.tail = a).card ≤ 2 := by
    intro a ha
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp ha
    have hwn : w ∈ T.nodes := (Finset.mem_filter.mp hw).1
    have hw1 : w.length = d + 1 := (Finset.mem_filter.mp hw).2
    obtain ⟨x, u, rfl⟩ := List.exists_cons_of_ne_nil (show w ≠ [] by rintro rfl; simp at hw1)
    have hu := T.parent_mem x u hwn
    refine le_trans (Finset.card_le_card ?_) (fiber_le T u hu)
    intro v hv
    simp only [Finset.mem_filter, lev] at hv ⊢
    obtain ⟨⟨hvn, hvl⟩, hvt⟩ := hv
    refine ⟨hvn, by simpa using hvt, ?_⟩
    rintro rfl; simp at hvl
  have := Finset.card_le_mul_card_image (lev T (d + 1)) 2 hfib
  refine this.trans (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))
  intro u hu
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
  have hwn : w ∈ T.nodes := (Finset.mem_filter.mp hw).1
  have hw1 : w.length = d + 1 := (Finset.mem_filter.mp hw).2
  obtain ⟨x, u, rfl⟩ := List.exists_cons_of_ne_nil (show w ≠ [] by rintro rfl; simp at hw1)
  simp only [inte, lev, Finset.mem_filter, List.tail_cons]
  exact ⟨⟨T.parent_mem x u hwn, by simpa using hw1⟩, x, hwn⟩

lemma lev_split (T : SepTree E) (d : ℕ) : (lev T d).card = (inte T d).card + (lvs T d).card := by
  unfold inte lvs
  rw [Finset.card_filter_add_card_filter_not]

noncomputable def Lf (T : SepTree E) (d : ℕ) : ℕ := ∑ j ∈ Finset.range d, (lvs T j).card

lemma B_le (T : SepTree E) : ∀ d, (lev T d).card + Lf T d ≤ 2 ^ d := by
  intro d
  induction d with
  | zero =>
    have : (lev T 0).card ≤ 1 := by
      refine le_trans (Finset.card_le_card (t := {[]}) ?_) (by simp)
      intro v hv
      simp only [lev, Finset.mem_filter] at hv
      simpa using hv.2
    simp [Lf]; omega
  | succ d ih =>
    have h1 := lev_succ_le T d
    have h2 := lev_split T d
    have h3 : Lf T (d + 1) = Lf T d + (lvs T d).card := by
      unfold Lf; rw [Finset.sum_range_succ]
    rw [h3, pow_succ]
    omega

lemma geom (k : ℕ) : (∑ i ∈ Finset.range k, 2 ^ i) + 1 = 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, pow_succ]; omega

lemma lvs_le_lev (T : SepTree E) (d : ℕ) : (lvs T d).card ≤ (lev T d).card :=
  Finset.card_le_card (Finset.filter_subset _ _)

lemma nodes_card [Finite E] (T : SepTree E) :
    T.nodes.card < 2 ^ ((Unoriented E).ncard + 1) := by
  have h := Finset.card_eq_sum_card_fiberwise (s := T.nodes) (t := Finset.range ((Unoriented E).ncard + 1))
    (f := List.length) (fun v hv => Finset.mem_range.mpr (Nat.lt_succ_of_le (length_le T hv)))
  have h2 : ∀ d ∈ Finset.range ((Unoriented E).ncard + 1),
      (T.nodes.filter fun v => v.length = d).card ≤ 2 ^ d := fun d _ =>
    le_trans (Nat.le_add_right _ _) (B_le T d)
  have h3 := Finset.sum_le_sum h2
  have h4 := geom ((Unoriented E).ncard + 1)
  omega

lemma leaves_card [Finite E] (T : SepTree E) :
    {ℓ : List E | T.IsLeaf ℓ}.ncard ≤ 2 ^ (Unoriented E).ncard := by
  set n := (Unoriented E).ncard
  have hset : {ℓ : List E | T.IsLeaf ℓ} =
      ↑(T.nodes.filter fun ℓ => ¬ ∃ x, x :: ℓ ∈ T.nodes) := by
    ext ℓ
    simp [SepTree.IsLeaf]
  rw [hset, Set.ncard_coe_finset]
  have h := Finset.card_eq_sum_card_fiberwise
    (s := T.nodes.filter fun ℓ => ¬ ∃ x, x :: ℓ ∈ T.nodes) (t := Finset.range (n + 1))
    (f := List.length) (fun v hv => Finset.mem_range.mpr
      (Nat.lt_succ_of_le (length_le T (Finset.mem_filter.mp hv).1)))
  have h2 : ∀ d, ((T.nodes.filter fun ℓ => ¬ ∃ x, x :: ℓ ∈ T.nodes).filter fun v => v.length = d)
      = lvs T d := by
    intro d
    unfold lvs lev
    rw [Finset.filter_filter, Finset.filter_filter]
    apply Finset.filter_congr
    intro v _
    tauto
  simp only [h2] at h
  have h3 : ∑ d ∈ Finset.range (n + 1), (lvs T d).card = Lf T n + (lvs T n).card := by
    unfold Lf; rw [Finset.sum_range_succ]
  have := B_le T n
  have := lvs_le_lev T n
  omega

end counting

end TangleStructTree.Dev.C35

namespace TangleStructTree
open TangleStructTree.Dev.C35

variable {E : Type*} [PartialOrder E] [SepSystem E]

theorem chk_corollary_3_5 [Finite E] (T : SepTree E) :
    {ℓ : List E | T.IsLeaf ℓ}.ncard ≤ 2 ^ (Unoriented E).ncard ∧
      T.nodes.card < 2 ^ ((Unoriented E).ncard + 1) :=
  ⟨leaves_card T, nodes_card T⟩

end TangleStructTree
end

theorem solution : type_of% @TangleStructTree.chk_corollary_3_5 := @TangleStructTree.chk_corollary_3_5
