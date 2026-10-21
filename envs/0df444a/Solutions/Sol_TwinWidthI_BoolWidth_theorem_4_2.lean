-- Prove2me | solution 1 for TwinWidthI.BoolWidth.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-20T08:40:16.511861+00:00
-- url     : https://prove2.me/submissions/8acfed95-6c33-41c5-b271-c0eb5d5bd9b6

/-
SPDX-License-Identifier: Apache-2.0
Original Lean proof of Twin-width I, Theorem 4.2.
Mathematical source: Bonnet, Kim, Thomasse, and Watrigant, Twin-width I:
Tractable FO Model Checking, Theorem 4.2 and its proof (author PDF page 14).
Native Prove2Me definitions are imported unchanged. No accepted proof source is copied.
The proof expands the contraction invariant using uniformity to original outside vertices.
-/
import Mathlib
import Definitions.Def_TwinWidthI_BoolWidth_Setting

-- BEGIN PartitionCore
namespace TwinWidthProof

open Finset

section Partitions

variable {α : Type*} [DecidableEq α] {S T : Finset α}

/-- The literal native binary-merge relation, with arbitrary underlying finite set. -/
def MergeStep (P Q : Finpartition S) : Prop :=
  ∃ X ∈ P.parts, ∃ Y ∈ P.parts, X ≠ Y ∧
    Q.parts = insert (X ∪ Y) ((P.parts.erase X).erase Y)

/-- Replace two parts by their union. Distinctness is required for a genuine merge step. -/
def merge (P : Finpartition S) {X Y : Finset α}
    (hX : X ∈ P.parts) (hY : Y ∈ P.parts) : Finpartition S where
  parts := insert (X ∪ Y) ((P.parts.erase X).erase Y)
  supIndep := by
    apply Finset.supIndep_iff_pairwiseDisjoint.mpr
    intro A hA B hB hAB
    simp only [Finset.mem_coe, mem_insert, mem_erase] at hA hB
    rcases hA with rfl | ⟨hAY, hAX, hA⟩
    · rcases hB with rfl | ⟨hBY, hBX, hB⟩
      · exact False.elim (hAB rfl)
      · exact Finset.disjoint_union_left.mpr
          ⟨P.disjoint hX hB hBX.symm, P.disjoint hY hB hBY.symm⟩
    · rcases hB with rfl | ⟨hBY, hBX, hB⟩
      · exact Finset.disjoint_union_right.mpr
          ⟨P.disjoint hA hX hAX, P.disjoint hA hY hAY⟩
      · exact P.disjoint hA hB hAB
  sup_parts := by
    ext a
    simp only [Finset.mem_sup, id_eq]
    constructor
    · rintro ⟨Z, hZ, ha⟩
      rcases mem_insert.mp hZ with rfl | hZ
      · rcases mem_union.mp ha with ha | ha
        · exact P.subset hX ha
        · exact P.subset hY ha
      · exact P.subset (mem_erase.mp (mem_erase.mp hZ).2).2 ha
    · intro ha
      obtain ⟨Z, hZ, haz⟩ := P.exists_mem ha
      by_cases hZX : Z = X
      · subst Z
        exact ⟨X ∪ Y, mem_insert_self _ _, mem_union_left _ haz⟩
      by_cases hZY : Z = Y
      · subst Z
        exact ⟨X ∪ Y, mem_insert_self _ _, mem_union_right _ haz⟩
      exact ⟨Z, mem_insert_of_mem (mem_erase.mpr ⟨hZY, mem_erase.mpr ⟨hZX, hZ⟩⟩), haz⟩
  bot_notMem := by
    intro h
    rcases mem_insert.mp h with h | h
    · exact P.ne_empty hX (Finset.union_eq_empty.mp h.symm).1
    · exact P.empty_notMem_parts (mem_erase.mp (mem_erase.mp h).2).2

@[simp]
theorem merge_parts (P : Finpartition S) {X Y : Finset α}
    (hX : X ∈ P.parts) (hY : Y ∈ P.parts) :
    (merge P hX hY).parts = insert (X ∪ Y) ((P.parts.erase X).erase Y) := rfl

@[simp]
theorem mem_merge (P : Finpartition S) {X Y Z : Finset α}
    (hX : X ∈ P.parts) (hY : Y ∈ P.parts) :
    Z ∈ (merge P hX hY).parts ↔ Z = X ∪ Y ∨ Z ≠ Y ∧ Z ≠ X ∧ Z ∈ P.parts := by
  simp only [merge_parts, mem_insert, mem_erase]

theorem merge_step (P : Finpartition S) {X Y : Finset α}
    (hX : X ∈ P.parts) (hY : Y ∈ P.parts) (hXY : X ≠ Y) :
    MergeStep P (merge P hX hY) :=
  ⟨X, hX, Y, hY, hXY, rfl⟩

theorem union_notMem_erased (P : Finpartition S) {X Y : Finset α}
    (hX : X ∈ P.parts) :
    X ∪ Y ∉ (P.parts.erase X).erase Y := by
  intro h
  obtain ⟨hne, hmem⟩ := mem_erase.mp (mem_erase.mp h).2
  obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hX
  exact Finset.disjoint_left.mp (P.disjoint hX hmem hne.symm)
    hx (mem_union_left _ hx)

theorem card_merge_add_one (P : Finpartition S) {X Y : Finset α}
    (hX : X ∈ P.parts) (hY : Y ∈ P.parts) (hXY : X ≠ Y) :
    (merge P hX hY).parts.card + 1 = P.parts.card := by
  rw [merge_parts, card_insert_of_notMem (union_notMem_erased P hX)]
  have h1 := card_erase_add_one hX
  have h2 := card_erase_add_one (mem_erase.mpr ⟨hXY.symm, hY⟩)
  omega

theorem card_merge (P : Finpartition S) {X Y : Finset α}
    (hX : X ∈ P.parts) (hY : Y ∈ P.parts) (hXY : X ≠ Y) :
    (merge P hX hY).parts.card = P.parts.card - 1 := by
  have := card_merge_add_one P hX hY hXY
  omega

theorem card_merge_lt (P : Finpartition S) {X Y : Finset α}
    (hX : X ∈ P.parts) (hY : Y ∈ P.parts) (hXY : X ≠ Y) :
    (merge P hX hY).parts.card < P.parts.card := by
  have := card_merge_add_one P hX hY hXY
  omega

/-- Disjoint union of partitions, retaining the original parts literally. -/
def disjUnion (P : Finpartition S) (Q : Finpartition T) (hST : Disjoint S T) :
    Finpartition (S ∪ T) where
  parts := P.parts ∪ Q.parts
  supIndep := P.supIndep.union Q.supIndep (by simpa only [P.sup_parts, Q.sup_parts] using hST)
  sup_parts := by rw [Finset.sup_union, P.sup_parts, Q.sup_parts]; rfl
  bot_notMem := by
    simpa only [mem_union, not_or] using And.intro P.bot_notMem Q.bot_notMem

@[simp]
theorem disjUnion_parts (P : Finpartition S) (Q : Finpartition T) (hST : Disjoint S T) :
    (disjUnion P Q hST).parts = P.parts ∪ Q.parts := rfl

@[simp]
theorem mem_disjUnion (P : Finpartition S) (Q : Finpartition T)
    (hST : Disjoint S T) (X : Finset α) :
    X ∈ (disjUnion P Q hST).parts ↔ X ∈ P.parts ∨ X ∈ Q.parts :=
  mem_union

theorem parts_disjoint (P : Finpartition S) (Q : Finpartition T) (hST : Disjoint S T) :
    Disjoint P.parts Q.parts := by
  apply Finset.disjoint_left.mpr
  intro X hX hX'
  obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hX
  exact Finset.disjoint_left.mp hST (P.subset hX hx) (Q.subset hX' hx)

@[simp]
theorem card_disjUnion (P : Finpartition S) (Q : Finpartition T)
    (hST : Disjoint S T) :
    (disjUnion P Q hST).parts.card = P.parts.card + Q.parts.card := by
  exact card_union_of_disjoint (parts_disjoint P Q hST)

theorem disjUnion_bot (hST : Disjoint S T) :
    disjUnion (⊥ : Finpartition S) (⊥ : Finpartition T) hST = ⊥ := by
  apply Finpartition.ext
  ext X
  simp only [disjUnion_parts, mem_union, Finpartition.mem_bot_iff]
  constructor
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨x, Or.inl hx, rfl⟩
    · exact ⟨x, Or.inr hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    rcases hx with hx | hx
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩

theorem mergeStep_disjUnion_left {P P' : Finpartition S}
    (Q : Finpartition T) (hST : Disjoint S T) (h : MergeStep P P') :
    MergeStep (disjUnion P Q hST) (disjUnion P' Q hST) := by
  obtain ⟨X, hX, Y, hY, hXY, hp⟩ := h
  refine ⟨X, mem_union_left _ hX, Y, mem_union_left _ hY, hXY, ?_⟩
  simp only [disjUnion_parts]
  rw [hp]
  have hxq : X ∉ Q.parts := fun hq => Finset.disjoint_left.mp (parts_disjoint P Q hST) hX hq
  have hyq : Y ∉ Q.parts := fun hq => Finset.disjoint_left.mp (parts_disjoint P Q hST) hY hq
  ext Z
  by_cases hZX : Z = X
  · subst Z; simp [hxq]
  by_cases hZY : Z = Y
  · subst Z; simp [hyq]
  simp [hZX, hZY]

theorem mergeStep_disjUnion_right (P : Finpartition S)
    {Q Q' : Finpartition T} (hST : Disjoint S T) (h : MergeStep Q Q') :
    MergeStep (disjUnion P Q hST) (disjUnion P Q' hST) := by
  obtain ⟨X, hX, Y, hY, hXY, hq⟩ := h
  refine ⟨X, mem_union_right _ hX, Y, mem_union_right _ hY, hXY, ?_⟩
  simp only [disjUnion_parts]
  rw [hq]
  have hxp : X ∉ P.parts := fun hp => Finset.disjoint_left.mp (parts_disjoint P Q hST) hp hX
  have hyp : Y ∉ P.parts := fun hp => Finset.disjoint_left.mp (parts_disjoint P Q hST) hp hY
  ext Z
  by_cases hZX : Z = X
  · subst Z; simp [hxp]
  by_cases hZY : Z = Y
  · subst Z; simp [hyp]
  simp [hZX, hZY, or_comm]

theorem mergeStep_copy {P Q : Finpartition S} (hST : S = T) (h : MergeStep P Q) :
    MergeStep (P.copy hST) (Q.copy hST) := by
  exact h

@[simp]
theorem copy_bot (hST : S = T) :
    (⊥ : Finpartition S).copy hST = (⊥ : Finpartition T) := by
  subst T
  rfl

end Partitions

/-- A finite path whose initial and all subsequent states are valid. -/
inductive ValidPath {α : Type*} (Step : α → α → Prop) (Valid : α → Prop)
    (a : α) : α → Prop
  | refl (ha : Valid a) : ValidPath Step Valid a a
  | tail {b c : α} (path : ValidPath Step Valid a b)
      (step : Step b c) (valid : Valid c) : ValidPath Step Valid a c

namespace ValidPath

variable {α β : Type*} {Step : α → α → Prop} {Valid : α → Prop}
  {a b c : α}

theorem first_valid (h : ValidPath Step Valid a b) : Valid a := by
  induction h with
  | refl ha => exact ha
  | tail _ _ _ ih => exact ih

theorem last_valid (h : ValidPath Step Valid a b) : Valid b := by
  cases h with
  | refl ha => exact ha
  | tail _ _ hc => exact hc

theorem trans (hab : ValidPath Step Valid a b) (hbc : ValidPath Step Valid b c) :
    ValidPath Step Valid a c := by
  induction hbc with
  | refl _ => exact hab
  | tail _ hstep hvalid ih => exact ih.tail hstep hvalid

theorem single (ha : Valid a) (hab : Step a b) (hb : Valid b) :
    ValidPath Step Valid a b :=
  (ValidPath.refl ha).tail hab hb

theorem map {Step' : β → β → Prop} {Valid' : β → Prop}
    (f : α → β) (hstep : ∀ x y, Step x y → Step' (f x) (f y))
    (hvalid : ∀ x, Valid x → Valid' (f x))
    (h : ValidPath Step Valid a b) : ValidPath Step' Valid' (f a) (f b) := by
  induction h with
  | refl ha => exact .refl (hvalid _ ha)
  | tail _ hs hv ih => exact ih.tail (hstep _ _ hs) (hvalid _ hv)

theorem mono {Valid' : α → Prop} (hvalid : ∀ x, Valid x → Valid' x)
    (h : ValidPath Step Valid a b) : ValidPath Step Valid' a b :=
  h.map id (fun _ _ hs => hs) hvalid

/-- Convert the inductive path to the literal finite sequence required by twin-width. -/
theorem toFin (h : ValidPath Step Valid a b) :
    ∃ (n : ℕ) (p : Fin (n + 1) → α),
      p 0 = a ∧ p (Fin.last n) = b ∧
        (∀ i : Fin n, Step (p i.castSucc) (p i.succ)) ∧ ∀ i, Valid (p i) := by
  induction h with
  | refl ha =>
      exact ⟨0, fun _ => a, rfl, rfl, fun i => i.elim0, fun _ => ha⟩
  | @tail b c _ hbc hc ih =>
      obtain ⟨n, p, hp0, hpn, hsteps, hvalid⟩ := ih
      refine ⟨n + 1, Fin.snoc p c, ?_, ?_, ?_, ?_⟩
      · simpa only [Fin.snoc_apply_zero] using hp0
      · exact Fin.snoc_last _ _
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, hpn] using hbc
        · simpa only [Fin.succ_castSucc, Fin.snoc_castSucc] using hsteps j
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [Fin.snoc_last] using hc
        · simpa only [Fin.snoc_castSucc] using hvalid j

end ValidPath
end TwinWidthProof
-- END PartitionCore

-- BEGIN Foundation
open Finset TwinWidthI.BoolWidth

namespace TwinWidthProof

variable {V : Type*} [Fintype V] [DecidableEq V]

def UniformOutside (G : SimpleGraph V) (S X : Finset V) : Prop :=
  ∀ x ∈ X, ∀ x' ∈ X, ∀ z, z ∉ S → (G.Adj x z ↔ G.Adj x' z)

open Classical in
def LocalD (G : SimpleGraph V) {S : Finset V} (P : Finpartition S) (d : ℕ) : Prop :=
  ∀ X ∈ P.parts, #{Y ∈ P.parts | Y ≠ X ∧ ¬ Homogeneous G X Y} ≤ d

def Valid (G : SimpleGraph V) (S : Finset V) (d : ℕ) (P : Finpartition S) : Prop :=
  LocalD G P d ∧ ∀ X ∈ P.parts, UniformOutside G S X

end TwinWidthProof
-- END Foundation

-- BEGIN Uniformity
open Finset TwinWidthI.BoolWidth
namespace TwinWidthProof
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {S T X Y : Finset V}

omit [Fintype V] [DecidableEq V] in
theorem uniformOutside_mono (h : UniformOutside G S X) (hst : S ⊆ T) :
    UniformOutside G T X := by
  intro x hx x' hx' z hz
  exact h x hx x' hx' z (fun hzs => hz (hst hzs))

omit [Fintype V] [DecidableEq V] in
theorem uniformOutside_singleton (x : V) : UniformOutside G S {x} := by
  intro a ha b hb z _
  simp only [mem_singleton] at ha hb
  subst a; subst b
  rfl

omit [DecidableEq V] in
theorem uniformOutside_univ : UniformOutside G univ X := by
  intro x _ x' _ z hz
  exact False.elim (hz (mem_univ z))

omit [Fintype V] [DecidableEq V] in
theorem homogeneous_of_uniform (hx : UniformOutside G S X)
    (hy : UniformOutside G T Y) (hxs : X ⊆ S) (hyt : Y ⊆ T)
    (hst : Disjoint S T) : Homogeneous G X Y := by
  classical
  by_cases hxe : X.Nonempty
  · by_cases hye : Y.Nonempty
    · obtain ⟨x₀, hx₀⟩ := hxe
      obtain ⟨y₀, hy₀⟩ := hye
      have row : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y ↔ G.Adj x₀ y₀ := by
        intro x hxx y hyy
        have hyS : y ∉ S := fun h => (disjoint_left.mp hst) h (hyt hyy)
        have hxT : x₀ ∉ T := fun h => (disjoint_left.mp hst) (hxs hx₀) h
        exact (hx x hxx x₀ hx₀ y hyS).trans
          ((G.adj_comm x₀ y).trans ((hy y hyy y₀ hy₀ x₀ hxT).trans
            (G.adj_comm y₀ x₀)))
      by_cases he : G.Adj x₀ y₀
      · exact Or.inl (fun x hxx y hyy => (row x hxx y hyy).mpr he)
      · exact Or.inr (fun x hxx y hyy h => he ((row x hxx y hyy).mp h))
    · exact Or.inl (by intro x _ y hy'; exact False.elim (hye ⟨y, hy'⟩))
  · exact Or.inl (by intro x hx'; exact False.elim (hxe ⟨x, hx'⟩))

omit [Fintype V] in
theorem localD_of_card {P : Finpartition S} {d : ℕ} (h : P.parts.card ≤ d + 1) :
    LocalD G P d := by
  classical
  intro X hX
  have hs : {Y ∈ P.parts | Y ≠ X ∧ ¬ Homogeneous G X Y} ⊆ P.parts.erase X := by
    intro Y hY
    simp only [mem_filter] at hY
    exact mem_erase.mpr ⟨hY.2.1, hY.1⟩
  have hc := card_le_card hs
  rw [card_erase_of_mem hX] at hc
  omega

omit [Fintype V] in
theorem valid_bot (G : SimpleGraph V) (S : Finset V) (d : ℕ) :
    Valid G S d ⊥ := by
  classical
  constructor
  · intro X hX
    obtain ⟨x, _, rfl⟩ := Finpartition.mem_bot_iff.mp hX
    have he : {Y ∈ (⊥ : Finpartition S).parts |
        Y ≠ {x} ∧ ¬ Homogeneous G {x} Y} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro Y hY
      obtain ⟨hy, _, hn⟩ := mem_filter.mp hY
      obtain ⟨y, _, rfl⟩ := Finpartition.mem_bot_iff.mp hy
      apply hn
      by_cases hxy : G.Adj x y
      · left; simpa using hxy
      · right; simpa using hxy
    rw [he]
    simp
  · intro X hX
    obtain ⟨x, _, rfl⟩ := Finpartition.mem_bot_iff.mp hX
    exact uniformOutside_singleton x

end TwinWidthProof
-- END Uniformity

-- BEGIN Profiles
open Finset TwinWidthI.BoolWidth
namespace TwinWidthProof
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def profile (S X : Finset V) : Finset V :=
  (univ \ S).filter (fun z => ∃ x ∈ X, G.Adj x z)

theorem profile_card_bound {S : Finset V} (P : Finpartition S) :
    (P.parts.image (profile G S)).card ≤ nbhdCount G S (univ \ S) := by
  apply card_le_card
  intro Z hZ
  obtain ⟨X, hX, rfl⟩ := mem_image.mp hZ
  exact mem_image.mpr ⟨X, mem_powerset.mpr (P.le hX), rfl⟩

theorem profile_mem_iff {S X : Finset V} (hX : UniformOutside G S X)
    {x : V} (hx : x ∈ X) {z : V} (hz : z ∉ S) :
    z ∈ profile G S X ↔ G.Adj x z := by
  simp only [profile, mem_filter, mem_sdiff, mem_univ, true_and]
  constructor
  · rintro ⟨_, y, hy, he⟩
    exact (hX y hy x hx z hz).mp he
  · intro he
    exact ⟨hz, x, hx, he⟩

theorem uniformOutside_union_same_profile {S X Y : Finset V}
    (hX : UniformOutside G S X) (hY : UniformOutside G S Y)
    (he : profile G S X = profile G S Y) : UniformOutside G S (X ∪ Y) := by
  intro x hx x' hx' z hz
  have cross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a z ↔ G.Adj b z := by
    intro a ha b hb
    rw [← profile_mem_iff G hX ha hz, ← profile_mem_iff G hY hb hz, he]
  rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hx' with hx' | hx'
  · exact hX x hx x' hx' z hz
  · exact cross x hx x' hx'
  · exact (cross x' hx' x hx).symm
  · exact hY x hx x' hx' z hz

theorem exists_equal_profile {S : Finset V} (P : Finpartition S) (N : ℕ)
    (hcut : nbhdCount G S (univ \ S) ≤ N) (hcard : N < P.parts.card) :
    ∃ X ∈ P.parts, ∃ Y ∈ P.parts, X ≠ Y ∧ profile G S X = profile G S Y := by
  have hc : (P.parts.image (profile G S)).card < P.parts.card :=
    lt_of_le_of_lt (le_trans (profile_card_bound G P) hcut) hcard
  exact exists_ne_map_eq_of_card_image_lt hc

omit [Fintype V] in
theorem nbhdCount_pos (S T : Finset V) : 0 < nbhdCount G S T := by
  apply card_pos.mpr
  exact ⟨T.filter (fun b => ∃ a ∈ (∅ : Finset V), G.Adj a b),
    mem_image.mpr ⟨∅, mem_powerset.mpr (empty_subset S), rfl⟩⟩

theorem nbhdCount_univ : nbhdCount G univ (univ \ (univ : Finset V)) = 1 := by
  have h : (univ : Finset V).powerset.Nonempty :=
    ⟨∅, mem_powerset.mpr (empty_subset _)⟩
  rw [nbhdCount, sdiff_self]
  change ((univ : Finset V).powerset.image (fun _ => (∅ : Finset V))).card = 1
  rw [image_const h, card_singleton]

end TwinWidthProof
-- END Profiles

-- BEGIN TreeFacts
open Finset TwinWidthI.BoolWidth
namespace TwinWidthProof
variable {V : Type*} [Fintype V] [DecidableEq V]

 omit [Fintype V] [DecidableEq V] in
 theorem tree_mem_subtrees (T : DTree V) : T ∈ T.subtrees := by
  cases T <;> simp [DTree.subtrees]

 omit [Fintype V] in
 theorem tree_leaves_nonempty (T : DTree V) : T.leaves.toFinset.Nonempty := by
  induction T with
  | leaf a => exact ⟨a, by simp [DTree.leaves]⟩
  | node l r ihl _ =>
    obtain ⟨a, ha⟩ := ihl
    exact ⟨a, by simp only [DTree.leaves, List.toFinset_append, mem_union]; exact Or.inl ha⟩

 omit [Fintype V] in
 theorem tree_node_disjoint {l r : DTree V} (hn : (DTree.node l r).leaves.Nodup) :
    Disjoint l.leaves.toFinset r.leaves.toFinset := by
  have hd := (List.nodup_append.mp hn).2.2
  apply disjoint_left.mpr
  intro x hx hy
  exact hd x (List.mem_toFinset.mp hx) x (List.mem_toFinset.mp hy) rfl

 omit [Fintype V] [DecidableEq V] in
 theorem tree_node_nodup {l r : DTree V} (hn : (DTree.node l r).leaves.Nodup) :
    l.leaves.Nodup ∧ r.leaves.Nodup := by
  exact ⟨(List.nodup_append.mp hn).1, (List.nodup_append.mp hn).2.1⟩

 theorem decomp_leaves_eq_univ {T : DTree V} (h : IsDecompTree T) :
    T.leaves.toFinset = univ := by
  apply eq_univ_of_forall
  intro x
  exact List.mem_toFinset.mpr (h.2 x)

 theorem boolWidth_zero_leaf (G : SimpleGraph V) [DecidableRel G.Adj]
    {T : DTree V} (h : ∀ S ∈ T.properSubtrees,
      nbhdCount G S.leaves.toFinset (univ \ S.leaves.toFinset) ≤ 0) :
    ∃ x, T = DTree.leaf x := by
  cases T with
  | leaf x => exact ⟨x, rfl⟩
  | node l r =>
    have hl : l ∈ (DTree.node l r).properSubtrees := by
      simp only [DTree.properSubtrees, List.mem_append]
      exact Or.inl (tree_mem_subtrees l)
    have hp := nbhdCount_pos G l.leaves.toFinset (univ \ l.leaves.toFinset)
    have hz := h l hl
    omega

end TwinWidthProof
-- END TreeFacts

-- BEGIN UnionValidity
open Finset TwinWidthI.BoolWidth
namespace TwinWidthProof
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {S T : Finset V} {d : ℕ}

omit [Fintype V] in
theorem localD_union_bound (P : Finpartition S) (Q : Finpartition T)
    (R : Finpartition (S ∪ T)) (hr : R.parts = P.parts ∪ Q.parts)
    (hp : LocalD G P d) (hq : LocalD G Q d)
    (hc : ∀ X ∈ P.parts, ∀ Y ∈ Q.parts, Homogeneous G X Y) : LocalD G R d := by
  classical
  intro X hX
  rw [hr] at hX
  rcases mem_union.mp hX with hX | hX
  · apply le_trans (card_le_card ?_) (hp X hX)
    intro Y hY
    obtain ⟨hy, hne, hn⟩ := mem_filter.mp hY
    rw [hr] at hy
    rcases mem_union.mp hy with hy | hy
    · exact mem_filter.mpr ⟨hy, hne, hn⟩
    · exact False.elim (hn (hc X hX Y hy))
  · apply le_trans (card_le_card ?_) (hq X hX)
    intro Y hY
    obtain ⟨hy, hne, hn⟩ := mem_filter.mp hY
    rw [hr] at hy
    rcases mem_union.mp hy with hy | hy
    · apply False.elim
      apply hn
      rcases hc Y hy X hX with he | he
      · left
        intro x hx y hy'
        exact (he y hy' x hx).symm
      · right
        intro x hx y hy' hxy
        exact he y hy' x hx hxy.symm
    · exact mem_filter.mpr ⟨hy, hne, hn⟩

omit [Fintype V] in
theorem valid_union (P : Finpartition S) (Q : Finpartition T)
    (R : Finpartition (S ∪ T)) (hr : R.parts = P.parts ∪ Q.parts)
    (hst : Disjoint S T) (hp : Valid G S d P) (hq : Valid G T d Q) :
    Valid G (S ∪ T) d R := by
  constructor
  · apply localD_union_bound P Q R hr hp.1 hq.1
    intro X hX Y hY
    exact homogeneous_of_uniform (hp.2 X hX) (hq.2 Y hY) (P.le hX) (Q.le hY) hst
  · intro X hX
    rw [hr] at hX
    rcases mem_union.mp hX with hX | hX
    · exact uniformOutside_mono (hp.2 X hX) subset_union_left
    · exact uniformOutside_mono (hq.2 X hX) subset_union_right

end TwinWidthProof
-- END UnionValidity

-- BEGIN Compression
open Finset TwinWidthI.BoolWidth
namespace TwinWidthProof
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem valid_merge_same_profile {S : Finset V} {P : Finpartition S} {d : ℕ}
    (hp : Valid G S d P) {X Y : Finset V} (hX : X ∈ P.parts) (hY : Y ∈ P.parts)
    (hXY : X ≠ Y) (he : profile G S X = profile G S Y)
    (hc : P.parts.card ≤ d + 1) : Valid G S d (merge P hX hY) := by
  constructor
  · apply localD_of_card
    have hm := card_merge_add_one P hX hY hXY
    omega
  · intro Z hZ
    rw [merge_parts] at hZ
    rcases mem_insert.mp hZ with hZ | hZ
    · subst Z
      exact uniformOutside_union_same_profile G (hp.2 X hX) (hp.2 Y hY) he
    · exact hp.2 Z (mem_of_mem_erase (mem_of_mem_erase hZ))

theorem compress_partition {S : Finset V} (P : Finpartition S) (N d : ℕ)
    (hp : Valid G S d P) (hc : P.parts.card ≤ d + 1)
    (hcut : nbhdCount G S (univ \ S) ≤ N) :
    ∃ Q : Finpartition S, ValidPath MergeStep (Valid G S d) P Q ∧ Q.parts.card ≤ N := by
  classical
  induction hn : P.parts.card using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases hsmall : P.parts.card ≤ N
    · exact ⟨P, .refl hp, hsmall⟩
    · obtain ⟨X, hX, Y, hY, hXY, he⟩ := exists_equal_profile G P N hcut (by omega)
      let Q := merge P hX hY
      have hq : Valid G S d Q := valid_merge_same_profile G hp hX hY hXY he hc
      have hlt : Q.parts.card < n := by
        simpa only [← hn] using card_merge_lt P hX hY hXY
      have hqc : Q.parts.card ≤ d + 1 := by
        have hlt' := card_merge_lt P hX hY hXY
        change (merge P hX hY).parts.card ≤ d + 1
        omega
      obtain ⟨R, hpath, hr⟩ := ih Q.parts.card hlt Q hq hqc rfl
      exact ⟨R, (ValidPath.single hp (merge_step P hX hY hXY) hq).trans hpath, hr⟩

end TwinWidthProof
-- END Compression

-- BEGIN TreeContraction
open Finset TwinWidthI.BoolWidth
namespace TwinWidthProof
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem contract_tree (N : ℕ) (hN : 0 < N) (T : DTree V)
    (hn : T.leaves.Nodup)
    (hb : ∀ U ∈ T.subtrees,
      nbhdCount G U.leaves.toFinset (univ \ U.leaves.toFinset) ≤ N) :
    ∃ Q : Finpartition T.leaves.toFinset,
      ValidPath MergeStep (Valid G T.leaves.toFinset (2 * N - 1)) ⊥ Q ∧
      Q.parts.card ≤ N := by
  induction T with
  | leaf x =>
    refine ⟨⊥, .refl (valid_bot G _ _), ?_⟩
    change (⊥ : Finpartition ({x} : Finset V)).parts.card ≤ N
    rw [Finpartition.card_bot, card_singleton]
    omega
  | node l r ihl ihr =>
    have hnodup := tree_node_nodup hn
    have hdis := tree_node_disjoint hn
    have hbl : ∀ U ∈ l.subtrees,
        nbhdCount G U.leaves.toFinset (univ \ U.leaves.toFinset) ≤ N := by
      intro U hU
      apply hb U
      simp only [DTree.subtrees, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inl hU)
    have hbr : ∀ U ∈ r.subtrees,
        nbhdCount G U.leaves.toFinset (univ \ U.leaves.toFinset) ≤ N := by
      intro U hU
      apply hb U
      simp only [DTree.subtrees, List.mem_cons, List.mem_append]
      exact Or.inr (Or.inr hU)
    obtain ⟨Ql, hl, hcl⟩ := ihl hnodup.1 hbl
    obtain ⟨Qr, hr, hcr⟩ := ihr hnodup.2 hbr
    let R := disjUnion Ql Qr hdis
    have hleft : ValidPath MergeStep
        (Valid G (l.leaves.toFinset ∪ r.leaves.toFinset) (2*N-1))
        (disjUnion ⊥ ⊥ hdis) (disjUnion Ql ⊥ hdis) := by
      apply ValidPath.map (fun P => disjUnion P ⊥ hdis) _ _ hl
      · intro P P' hstep
        exact mergeStep_disjUnion_left _ hdis hstep
      · intro P hp
        exact valid_union P ⊥ _ (disjUnion_parts _ _ _) hdis hp (valid_bot G _ _)
    have hright : ValidPath MergeStep
        (Valid G (l.leaves.toFinset ∪ r.leaves.toFinset) (2*N-1))
        (disjUnion Ql ⊥ hdis) R := by
      apply ValidPath.map (fun P => disjUnion Ql P hdis) _ _ hr
      · intro P P' hstep
        exact mergeStep_disjUnion_right _ hdis hstep
      · intro P hp
        exact valid_union Ql P _ (disjUnion_parts _ _ _) hdis hl.last_valid hp
    have hp : ValidPath MergeStep
        (Valid G (l.leaves.toFinset ∪ r.leaves.toFinset) (2*N-1)) ⊥ R := by
      simpa only [disjUnion_bot] using hleft.trans hright
    have hcard : R.parts.card ≤ (2*N-1)+1 := by
      have he := card_disjUnion Ql Qr hdis
      change (disjUnion Ql Qr hdis).parts.card ≤ (2*N-1)+1
      omega
    have hcut : nbhdCount G (l.leaves.toFinset ∪ r.leaves.toFinset)
        (univ \ (l.leaves.toFinset ∪ r.leaves.toFinset)) ≤ N := by
      simpa only [DTree.leaves, List.toFinset_append] using
        hb (DTree.node l r) (tree_mem_subtrees _)
    obtain ⟨Q, hq, hcq⟩ := compress_partition G R N (2*N-1) hp.last_valid hcard hcut
    have hfinal := hp.trans hq
    rw [DTree.leaves, List.toFinset_append]
    exact ⟨Q, hfinal, hcq⟩

end TwinWidthProof
-- END TreeContraction

-- BEGIN NativeRoot
open Finset TwinWidthI.BoolWidth
namespace TwinWidthProof
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem native_of_path (G : SimpleGraph V) (d : ℕ)
    {Q : Finpartition (univ : Finset V)}
    (hp : ValidPath MergeStep (Valid G univ d) ⊥ Q) (hq : Q.parts.card ≤ 1) :
    TwinWidthLE G d := by
  obtain ⟨n, p, hp0, hpn, hsteps, hvalid⟩ := hp.toFin
  refine ⟨n, p, hp0, ?_, ?_, ?_⟩
  · simpa only [hpn] using hq
  · exact hsteps
  · intro i
    exact (hvalid i).1

theorem boolean_contraction (G : SimpleGraph V) [DecidableRel G.Adj]
    (N : ℕ) (hN : BoolWidthLE G N) : TwinWidthLE G (2*N-1) := by
  obtain ⟨T, hT, hcuts⟩ := hN
  by_cases hzero : N = 0
  · subst N
    obtain ⟨x, rfl⟩ := boolWidth_zero_leaf G hcuts
    have hu : (univ : Finset V) = {x} := by
      simpa only [DTree.leaves, List.toFinset_cons, List.toFinset_nil,
        insert_empty_eq] using (decomp_leaves_eq_univ hT).symm
    apply native_of_path G _ (ValidPath.refl (valid_bot G univ _))
    simp [hu]
  · have hn : 0 < N := Nat.pos_of_ne_zero hzero
    have hall : ∀ U ∈ T.subtrees,
        nbhdCount G U.leaves.toFinset (univ \ U.leaves.toFinset) ≤ N := by
      intro U hU
      by_cases he : U = T
      · subst U
        rw [decomp_leaves_eq_univ hT, nbhdCount_univ G]
        omega
      · apply hcuts U
        cases T with
        | leaf x => simp [DTree.subtrees] at hU; exact False.elim (he hU)
        | node l r =>
          simp only [DTree.subtrees, List.mem_cons] at hU
          exact hU.resolve_left he
    have hex : ∃ Q : Finpartition (univ : Finset V),
        ValidPath MergeStep (Valid G univ (2*N-1)) ⊥ Q ∧ Q.parts.card ≤ N := by
      have hc := contract_tree G N hn T hT.1 hall
      have he : T.leaves.toFinset = (univ : Finset V) := decomp_leaves_eq_univ hT
      rw [he] at hc
      exact hc
    obtain ⟨Q, hq, hc⟩ := hex
    have hcard : Q.parts.card ≤ (2*N-1)+1 := by omega
    have hrootcut : nbhdCount G univ (univ \ (univ : Finset V)) ≤ 1 := by
      rw [nbhdCount_univ]
    obtain ⟨R, hr, hcr⟩ := compress_partition G Q 1 (2*N-1) hq.last_valid hcard hrootcut
    exact native_of_path G _ (hq.trans hr) hcr

end TwinWidthProof

namespace TwinWidthI.BoolWidth

open Finset

theorem theorem_4_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (N : ℕ) (hN : BoolWidthLE G N) : TwinWidthLE G (2 * N - 1) := by
  exact TwinWidthProof.boolean_contraction G N hN

end TwinWidthI.BoolWidth
-- END NativeRoot

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (N : ℕ) (hN : TwinWidthI.BoolWidth.BoolWidthLE G N) :
    TwinWidthI.BoolWidth.TwinWidthLE G (2 * N - 1) :=
  TwinWidthI.BoolWidth.theorem_4_2 G N hN
