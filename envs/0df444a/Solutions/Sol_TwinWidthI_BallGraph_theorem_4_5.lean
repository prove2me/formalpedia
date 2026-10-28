-- Prove2me | solution 1 for TwinWidthI.BallGraph.theorem_4_5
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-27T05:56:09.738706+00:00
-- url     : https://prove2.me/submissions/d676d5ce-0687-47af-a6b4-dfa3228f7445

import Mathlib
import Definitions.Def_TwinWidthI_BallGraph_Setting
import Definitions.Def_TwinWidthI_BoolWidth_Setting


-- Complete module: TWBProof.PartitionMerge

namespace TwinWidthI.BallGraph.TWFresh
open Finset TwinWidthI.BoolWidth
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def mergedParts (P : Finpartition (univ : Finset V)) (X Y : Finset V) :
    Finset (Finset V) := insert (X ∪ Y) ((P.parts.erase X).erase Y)

lemma mem_mergedParts (P : Finpartition (univ : Finset V)) (X Y Z : Finset V) :
    Z ∈ mergedParts P X Y ↔ Z = X ∪ Y ∨ Z ∈ P.parts ∧ Z ≠ X ∧ Z ≠ Y := by
  classical
  simp only [mergedParts, mem_insert, mem_erase]
  tauto

noncomputable def mergePartition (P : Finpartition (univ : Finset V)) (X Y : Finset V)
    (hX : X ∈ P.parts) (hY : Y ∈ P.parts) : Finpartition (univ : Finset V) := by
  classical
  apply Finpartition.ofExistsUnique (mergedParts P X Y) (fun _ _ => subset_univ _)
  · intro v hv
    obtain ⟨Z, ⟨hZ,hvZ⟩, huniq⟩ := P.existsUnique_mem hv
    by_cases hxy : Z = X ∨ Z = Y
    · refine ⟨X ∪ Y, ⟨(mem_mergedParts P X Y _).mpr (Or.inl rfl), ?_⟩, ?_⟩
      · rcases hxy with rfl | rfl
        · exact mem_union_left _ hvZ
        · exact mem_union_right _ hvZ
      · intro T hT
        rcases (mem_mergedParts P X Y T).mp hT.1 with rfl | ⟨hTp,hTX,hTY⟩
        · rfl
        · have he := P.eq_of_mem_parts hTp hZ hT.2 hvZ
          rcases hxy with h | h
          · exact (hTX (he.trans h)).elim
          · exact (hTY (he.trans h)).elim
    · refine ⟨Z, ⟨(mem_mergedParts P X Y _).mpr (Or.inr ⟨hZ, ?_, ?_⟩), hvZ⟩, ?_⟩
      · exact fun h => hxy (Or.inl h)
      · exact fun h => hxy (Or.inr h)
      · intro T hT
        rcases (mem_mergedParts P X Y T).mp hT.1 with rfl | ⟨hTpart, _, _⟩
        · rcases mem_union.mp hT.2 with hvX | hvY
          · exact (hxy (Or.inl (P.eq_of_mem_parts hZ hX hvZ hvX))).elim
          · exact (hxy (Or.inr (P.eq_of_mem_parts hZ hY hvZ hvY))).elim
        · exact P.eq_of_mem_parts hTpart hZ hT.2 hvZ
  · intro he
    rcases (mem_mergedParts P X Y ∅).mp he with he | ⟨he, _, _⟩
    · have hn := P.nonempty_of_mem_parts hX
      obtain ⟨v,hv⟩ := hn
      have : v ∈ (∅ : Finset V) := he ▸ mem_union_left Y hv
      simp at this
    · exact P.bot_notMem he

lemma mergePartition_parts (P : Finpartition (univ : Finset V)) (X Y : Finset V)
    (hX : X ∈ P.parts) (hY : Y ∈ P.parts) :
    (mergePartition P X Y hX hY).parts = mergedParts P X Y := rfl

lemma mergePartition_step (P : Finpartition (univ : Finset V)) (X Y : Finset V)
    (hX : X ∈ P.parts) (hY : Y ∈ P.parts) (hne : X ≠ Y) :
    IsMergeStep P (mergePartition P X Y hX hY) :=
  ⟨X,hX,Y,hY,hne,rfl⟩

lemma mergePartition_card (P : Finpartition (univ : Finset V)) (X Y : Finset V)
    (hX : X ∈ P.parts) (hY : Y ∈ P.parts) (hne : X ≠ Y) :
    (mergePartition P X Y hX hY).parts.card + 1 = P.parts.card := by
  classical
  rw [mergePartition_parts, mergedParts]
  have hnot : X ∪ Y ∉ (P.parts.erase X).erase Y := by
    intro h
    have hp := (mem_erase.mp (mem_erase.mp h).2).2
    obtain ⟨v,hv⟩ := P.nonempty_of_mem_parts hX
    have he := P.eq_of_mem_parts hp hX (mem_union_left Y hv) hv
    exact (mem_erase.mp (mem_erase.mp h).2).1 he
  rw [card_insert_of_notMem hnot, card_erase_of_mem]
  · rw [card_erase_of_mem hX]
    have h2 : 2 ≤ P.parts.card := by
      exact one_lt_card.mpr ⟨X,hX,Y,hY,hne⟩
    omega
  · exact mem_erase.mpr ⟨hne.symm,hY⟩

end TwinWidthI.BallGraph.TWFresh

-- Complete module: TWBProof.RefinementMerge

namespace TwinWidthI.BallGraph.TWFresh
open Finset TwinWidthI.BoolWidth
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma le_mergePartition (P : Finpartition (univ : Finset V)) (X Y : Finset V)
    (hX : X ∈ P.parts) (hY : Y ∈ P.parts) : P ≤ mergePartition P X Y hX hY := by
  intro Z hZ
  by_cases h : Z = X ∨ Z = Y
  · refine ⟨X ∪ Y, ?_, ?_⟩
    · rw [mergePartition_parts, mem_mergedParts]; exact Or.inl rfl
    · rcases h with rfl | rfl
      · exact subset_union_left
      · exact subset_union_right
  · refine ⟨Z, ?_, le_rfl⟩
    rw [mergePartition_parts, mem_mergedParts]
    exact Or.inr ⟨hZ,fun he => h (Or.inl he),fun he => h (Or.inr he)⟩

lemma mergePartition_le {P Q : Finpartition (univ : Finset V)} (hPQ : P ≤ Q)
    (X Y Z : Finset V) (hX : X ∈ P.parts) (hY : Y ∈ P.parts)
    (hZ : Z ∈ Q.parts) (hXZ : X ⊆ Z) (hYZ : Y ⊆ Z) :
    mergePartition P X Y hX hY ≤ Q := by
  intro A hA
  rw [mergePartition_parts, mem_mergedParts] at hA
  rcases hA with rfl | ⟨hA,_,_⟩
  · exact ⟨Z,hZ,union_subset hXZ hYZ⟩
  · exact hPQ hA

lemma exists_merge_of_refines {P Q : Finpartition (univ : Finset V)}
    (hPQ : P ≤ Q) (hne : P ≠ Q) :
    ∃ X ∈ P.parts, ∃ Y ∈ P.parts, X ≠ Y ∧ ∃ Z ∈ Q.parts, X ⊆ Z ∧ Y ⊆ Z := by
  classical
  by_contra hn
  have hall : ∀ X ∈ P.parts, ∀ Y ∈ P.parts, ∀ Z ∈ Q.parts,
      X ⊆ Z → Y ⊆ Z → X = Y := by
    intro X hX Y hY Z hZ hXZ hYZ
    by_contra hxy
    exact hn ⟨X,hX,Y,hY,hxy,Z,hZ,hXZ,hYZ⟩
  apply hne
  apply le_antisymm hPQ
  intro Z hZ
  obtain ⟨v,hv⟩ := Q.nonempty_of_mem_parts hZ
  obtain ⟨X,hX,hvX⟩ := P.exists_mem (mem_univ v)
  obtain ⟨Z',hZ',hXZ'⟩ := hPQ hX
  have he : Z' = Z := Q.eq_of_mem_parts hZ' hZ (hXZ' hvX) hv
  subst Z'
  refine ⟨X,hX,fun w hw => ?_⟩
  obtain ⟨Y,hY,hwY⟩ := P.exists_mem (mem_univ w)
  obtain ⟨T,hT,hYT⟩ := hPQ hY
  have heT : T = Z := Q.eq_of_mem_parts hT hZ (hYT hwY) hw
  subst T
  rw [hall Y hY X hX Z hZ hYT hXZ'] at hwY
  exact hwY

def GoodMerge (good : Finpartition (univ : Finset V) → Prop)
    (P Q : Finpartition (univ : Finset V)) : Prop := IsMergeStep P Q ∧ good Q

def MergeReach (good : Finpartition (univ : Finset V) → Prop)
    (P Q : Finpartition (univ : Finset V)) : Prop := Relation.ReflTransGen (GoodMerge good) P Q

lemma refinement_reach (P Q : Finpartition (univ : Finset V)) (hPQ : P ≤ Q)
    (good : Finpartition (univ : Finset V) → Prop)
    (hg : ∀ R, P ≤ R → R ≤ Q → good R) : MergeReach good P Q := by
  have aux : ∀ n : ℕ, ∀ R : Finpartition (univ : Finset V), R.parts.card = n →
      P ≤ R → R ≤ Q → MergeReach good R Q := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro R hn hPR hRQ
      by_cases he : R = Q
      · subst R; exact Relation.ReflTransGen.refl
      obtain ⟨X,hX,Y,hY,hne,Z,hZ,hXZ,hYZ⟩ := exists_merge_of_refines hRQ he
      let R' := mergePartition R X Y hX hY
      have hRR' : R ≤ R' := le_mergePartition R X Y hX hY
      have hR'Q : R' ≤ Q := mergePartition_le hRQ X Y Z hX hY hZ hXZ hYZ
      have hc : R'.parts.card < n := by
        have hc := mergePartition_card R X Y hX hY hne
        change R'.parts.card + 1 = R.parts.card at hc
        omega
      exact Relation.ReflTransGen.head ⟨mergePartition_step R X Y hX hY hne,
        hg R' (hPR.trans hRR') hR'Q⟩ (ih _ hc R' rfl (hPR.trans hRR') hR'Q)
  exact aux _ P rfl le_rfl hPQ

end TwinWidthI.BallGraph.TWFresh

-- Complete module: TWBProof.FiberPartition

namespace TwinWidthI.BallGraph.TWFresh
open Finset TwinWidthI.BoolWidth
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {L : Type*}

noncomputable def fiberPartition (f : V → L) : Finpartition (univ : Finset V) := by
  classical
  exact Finpartition.ofSetoid (Setoid.ker f)

def RefinesLabel (P : Finpartition (univ : Finset V)) (f : V → L) : Prop :=
  ∀ A ∈ P.parts, ∃ z, ∀ v ∈ A, f v = z

lemma fiber_part_mem_iff (f : V → L) (u v : V) :
    v ∈ (fiberPartition f).part u ↔ f u = f v := by
  classical
  exact Finpartition.mem_part_ofSetoid_iff_rel

lemma refinesLabel_iff (P : Finpartition (univ : Finset V)) (f : V → L) :
    RefinesLabel P f ↔ P ≤ fiberPartition f := by
  constructor
  · intro h A hA
    obtain ⟨z,hz⟩ := h A hA
    obtain ⟨u,hu⟩ := P.nonempty_of_mem_parts hA
    refine ⟨(fiberPartition f).part u, (fiberPartition f).part_mem.mpr (mem_univ u), ?_⟩
    intro v hv
    exact (fiber_part_mem_iff f u v).mpr ((hz u hu).trans (hz v hv).symm)
  · intro h A hA
    obtain ⟨B,hB,hAB⟩ := h hA
    obtain ⟨u,hu⟩ := (fiberPartition f).nonempty_of_mem_parts hB
    refine ⟨f u, fun v hv => ?_⟩
    have he := (fiberPartition f).part_eq_of_mem hB hu
    have hm : v ∈ (fiberPartition f).part u := by rw [he]; exact hAB hv
    exact ((fiber_part_mem_iff f u v).mp hm).symm

lemma fiber_refines (f : V → L) : RefinesLabel (fiberPartition f) f :=
  (refinesLabel_iff _ _).mpr le_rfl

lemma fiber_comp_le {K : Type*} (f : V → L) (g : L → K) :
    fiberPartition f ≤ fiberPartition (g ∘ f) := by
  apply (refinesLabel_iff _ _).mp
  intro A hA
  obtain ⟨z,hz⟩ := fiber_refines f A hA
  exact ⟨g z,fun v hv => congrArg g (hz v hv)⟩

lemma eq_label_of_same_part (f : V → L) (P : Finpartition (univ : Finset V))
    (hP : P ≤ fiberPartition f) {A : Finset V} (hA : A ∈ P.parts)
    {u v : V} (hu : u ∈ A) (hv : v ∈ A) : f u = f v := by
  obtain ⟨z,hz⟩ := (refinesLabel_iff P f).mpr hP A hA
  exact (hz u hu).trans (hz v hv).symm

lemma same_label_same_part (f : V → L) (P : Finpartition (univ : Finset V))
    (hP : fiberPartition f ≤ P) {A B : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts)
    {u v : V} (hu : u ∈ A) (hv : v ∈ B) (he : f u = f v) : A = B := by
  have hf : (fiberPartition f).part u ∈ (fiberPartition f).parts :=
    (fiberPartition f).part_mem.mpr (mem_univ u)
  obtain ⟨C,hC,hfC⟩ := hP hf
  have huC : u ∈ C := hfC ((fiberPartition f).mem_part (mem_univ u))
  have hvC : v ∈ C := hfC ((fiber_part_mem_iff f u v).mpr he)
  exact (P.eq_of_mem_parts hA hC hu huC).trans (P.eq_of_mem_parts hC hB hvC hv)

end TwinWidthI.BallGraph.TWFresh

-- Complete module: TWBProof.PartCounting

namespace TwinWidthI.BallGraph.TWFresh
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma parts_card_le_vertices (P : Finpartition (univ : Finset V)) (A : Finset (Finset V))
    (hA : A ⊆ P.parts) (T : Finset V) (hT : ∀ B ∈ A, B ⊆ T) : A.card ≤ T.card := by
  classical
  have hn (B : A) := P.nonempty_of_mem_parts (hA B.property)
  choose v hv using hn
  let f : A → T := fun B => ⟨v B,hT B B.property (hv B)⟩
  have hf : Function.Injective f := by
    intro B C he
    have he' : v B = v C := congrArg Subtype.val he
    apply Subtype.ext
    exact P.eq_of_mem_parts (hA B.property) (hA C.property) (hv B) (he' ▸ hv C)
  simpa using Fintype.card_le_of_injective f hf

lemma parts_card_le_labels {L : Type*} [DecidableEq L] (f : V → L)
    (P : Finpartition (univ : Finset V)) (hP : fiberPartition f ≤ P)
    (A : Finset (Finset V)) (hA : A ⊆ P.parts) (T : Finset L)
    (hT : ∀ B ∈ A, ∃ v ∈ B, f v ∈ T) : A.card ≤ T.card := by
  classical
  have hn (B : A) := hT B B.property
  choose v hv ht using hn
  let g : A → T := fun B => ⟨f (v B),ht B⟩
  have hg : Function.Injective g := by
    intro B C he
    apply Subtype.ext
    exact same_label_same_part f P hP (hA B.property) (hA C.property)
      (hv B) (hv C) (congrArg Subtype.val he)
  simpa using Fintype.card_le_of_injective g hg

lemma red_degree_le_labels {L : Type*} [DecidableEq L] (H : SimpleGraph V) (f : V → L)
    (P : Finpartition (univ : Finset V)) (hP : fiberPartition f ≤ P)
    (D : ℕ) (hbound : ∀ A ∈ P.parts, ∃ T : Finset L, T.card ≤ D ∧
      ∀ B ∈ P.parts, B ≠ A → SomeEdge H A B → ∃ v ∈ B, f v ∈ T) :
    IsRedDPartition H P D := by
  classical
  intro A hA
  obtain ⟨T,hcard,hT⟩ := hbound A hA
  apply le_trans (parts_card_le_labels f P hP _ (filter_subset _ _) T ?_) hcard
  intro B hB
  exact hT B (mem_filter.mp hB).1 (mem_filter.mp hB).2.1 (mem_filter.mp hB).2.2

lemma red_degree_le_vertices (H : SimpleGraph V) (P : Finpartition (univ : Finset V))
    (D : ℕ) (hbound : ∀ A ∈ P.parts, ∃ T : Finset V, T.card ≤ D ∧
      ∀ B ∈ P.parts, B ≠ A → SomeEdge H A B → B ⊆ T) :
    IsRedDPartition H P D := by
  classical
  intro A hA
  obtain ⟨T,hcard,hT⟩ := hbound A hA
  apply le_trans (parts_card_le_vertices P _ (filter_subset _ _) T ?_) hcard
  intro B hB
  exact hT B (mem_filter.mp hB).1 (mem_filter.mp hB).2.1 (mem_filter.mp hB).2.2

lemma label_union_card {L : Type*} [DecidableEq L] (f : V → L) (T : Finset L)
    (C : ℕ) (hc : ∀ z ∈ T, (univ.filter (fun v => f v = z)).card ≤ C) :
    (univ.filter (fun v => f v ∈ T)).card ≤ T.card * C := by
  classical
  have he : univ.filter (fun v => f v ∈ T) = T.biUnion (fun z => univ.filter (fun v => f v = z)) := by
    ext v; simp
  rw [he]
  apply le_trans (card_biUnion_le) ?_
  calc
    ∑ z ∈ T, (univ.filter (fun v => f v = z)).card ≤ ∑ _z ∈ T, C := sum_le_sum hc
    _ = T.card * C := by simp

end TwinWidthI.BallGraph.TWFresh

-- Complete module: TWBProof.DyadicLabels

namespace TwinWidthI.BallGraph.TWFresh
open Finset

def halveLabel {d : ℕ} (i : Fin d) (z : Fin d → ℕ) : Fin d → ℕ := Function.update z i (z i / 2)

lemma halveLabel_same {d : ℕ} (i : Fin d) (z : Fin d → ℕ) : halveLabel i z i = z i / 2 := by
  simp [halveLabel]

lemma halveLabel_other {d : ℕ} (i j : Fin d) (z : Fin d → ℕ) (h : j ≠ i) :
    halveLabel i z j = z j := by simp [halveLabel,h]

def LabelsClose {d : ℕ} (x y : Fin d → ℕ) : Prop := ∀ i, x i ≤ y i + 1 ∧ y i ≤ x i + 1

lemma halve_close {d : ℕ} (i : Fin d) {x y : Fin d → ℕ} (h : LabelsClose x y) :
    LabelsClose (halveLabel i x) (halveLabel i y) := by
  intro j
  by_cases hj : j = i
  · subst j
    simp only [halveLabel_same]
    have h := h i
    omega
  · simpa [halveLabel_other i j _ hj] using h j

noncomputable def phaseWindow {d : ℕ} (i : Fin d) (z : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset (fun j => if j = i then Icc (2*z j-1) (2*z j+2) else Icc (z j-1) (z j+1))

lemma phaseWindow_mem {d : ℕ} (i : Fin d) (z u v : Fin d → ℕ)
    (hu : halveLabel i u = z) (hclose : LabelsClose u v) : v ∈ phaseWindow i z := by
  apply Fintype.mem_piFinset.mpr
  intro j
  have he := congrFun hu j
  have hc := hclose j
  by_cases hj : j = i
  · subst j
    rw [if_pos rfl]
    rw [mem_Icc]
    rw [halveLabel_same] at he
    omega
  · simp only [if_neg hj, mem_Icc]
    rw [halveLabel_other i j u hj] at he
    omega

lemma phaseWindow_card {d : ℕ} (i : Fin d) (z : Fin d → ℕ) :
    (phaseWindow i z).card ≤ 2 * 3 ^ d := by
  classical
  rw [phaseWindow, Fintype.card_piFinset]
  have hbound (j : Fin d) :
      (if j = i then Icc (2*z j-1) (2*z j+2) else Icc (z j-1) (z j+1)).card ≤
      if j = i then 6 else 3 := by
    by_cases hj : j = i <;> simp only [hj, if_true, if_false, Nat.card_Icc] <;> omega
  apply le_trans (prod_le_prod (fun _ _ => Nat.zero_le _) (fun j _ => hbound j))
  rw [← prod_erase_mul _ _ (mem_univ i)]
  simp only [if_true]
  have he : ∏ j ∈ univ.erase i, (if j = i then 6 else 3 : ℕ) = 3 ^ (d - 1) := by
    calc
      _ = ∏ _j ∈ univ.erase i, (3 : ℕ) := by
        apply prod_congr rfl
        intro j hj
        exact if_neg (mem_erase.mp hj).1
      _ = 3 ^ (d - 1) := by simp
  rw [he]
  have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hd' : d - 1 + 1 = d := by omega
  have hp := pow_succ 3 (d-1)
  rw [hd'] at hp
  rw [hp]
  omega

end TwinWidthI.BallGraph.TWFresh

-- Complete module: TWBProof.DyadicPhase

namespace TwinWidthI.BallGraph.TWFresh
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

lemma dyadic_phase_good (H : SimpleGraph V) (q : V → Fin d → ℕ)
    (hclose : ∀ u v, H.Adj u v → LabelsClose (q u) (q v)) (i : Fin d)
    (P : Finpartition (univ : Finset V))
    (hlo : fiberPartition q ≤ P) (hhi : P ≤ fiberPartition (halveLabel i ∘ q)) :
    IsRedDPartition H P (2 * 3 ^ d) := by
  apply red_degree_le_labels H q P hlo
  intro A hA
  obtain ⟨z,hz⟩ := (refinesLabel_iff P (halveLabel i ∘ q)).mpr hhi A hA
  refine ⟨phaseWindow i z, phaseWindow_card i z, ?_⟩
  intro B hB hne he
  obtain ⟨u,hu,v,hv,huv⟩ := he
  exact ⟨v,hv,phaseWindow_mem i z (q u) (q v) (hz u hu) (hclose u v huv)⟩

lemma dyadic_phase_reach (H : SimpleGraph V) (q : V → Fin d → ℕ)
    (hclose : ∀ u v, H.Adj u v → LabelsClose (q u) (q v)) (i : Fin d) :
    MergeReach (fun P => IsRedDPartition H P (2 * 3 ^ d))
      (fiberPartition q) (fiberPartition (halveLabel i ∘ q)) := by
  apply refinement_reach _ _ (fiber_comp_le q (halveLabel i))
  exact fun P hlo hhi => dyadic_phase_good H q hclose i P hlo hhi

lemma constant_fiber_card {L : Type*} (q : V → L) (h : ∀ u v, q u = q v) :
    (fiberPartition q).parts.card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro A hA B hB
  obtain ⟨u,hu⟩ := (fiberPartition q).nonempty_of_mem_parts hA
  obtain ⟨v,hv⟩ := (fiberPartition q).nonempty_of_mem_parts hB
  exact same_label_same_part q (fiberPartition q) le_rfl hA hB hu hv (h u v)

omit [DecidableEq V] in
lemma label_mass_halve_lt (q : V → Fin d → ℕ) (v : V) (i : Fin d) (hi : 0 < q v i) :
    (∑ u, ∑ j, halveLabel i (q u) j) < ∑ u, ∑ j, q u j := by
  have hle (u : V) (j : Fin d) : halveLabel i (q u) j ≤ q u j := by
    by_cases hj : j = i
    · subst j; rw [halveLabel_same]; exact Nat.div_le_self _ _
    · rw [halveLabel_other i j _ hj]
  apply sum_lt_sum (fun u _ => sum_le_sum (fun j _ => hle u j))
  refine ⟨v,mem_univ _,?_⟩
  apply sum_lt_sum (fun j _ => hle v j)
  refine ⟨i,mem_univ _,?_⟩
  rw [halveLabel_same]
  exact Nat.div_lt_self hi (by omega)

lemma dyadic_reach_end (H : SimpleGraph V) (q : V → Fin d → ℕ)
    (hclose : ∀ u v, H.Adj u v → LabelsClose (q u) (q v)) :
    ∃ Q : Finpartition (univ : Finset V), Q.parts.card ≤ 1 ∧
      MergeReach (fun P => IsRedDPartition H P (2 * 3 ^ d)) (fiberPartition q) Q := by
  have aux : ∀ n : ℕ, ∀ q : V → Fin d → ℕ, (∑ v, ∑ i, q v i) = n →
      (∀ u v, H.Adj u v → LabelsClose (q u) (q v)) →
      ∃ Q : Finpartition (univ : Finset V), Q.parts.card ≤ 1 ∧
        MergeReach (fun P => IsRedDPartition H P (2 * 3 ^ d)) (fiberPartition q) Q := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro q hn hclose
      by_cases hz : ∀ v i, q v i = 0
      · refine ⟨fiberPartition q,constant_fiber_card q ?_,Relation.ReflTransGen.refl⟩
        intro u v; funext i; rw [hz u i,hz v i]
      · push Not at hz
        obtain ⟨v,i,hvi⟩ := hz
        have hm := label_mass_halve_lt q v i (Nat.pos_of_ne_zero hvi)
        rw [hn] at hm
        obtain ⟨Q,hQ,hpath⟩ := ih _ hm (halveLabel i ∘ q) rfl
          (fun u v huv => halve_close i (hclose u v huv))
        exact ⟨Q,hQ,(dyadic_phase_reach H q hclose i).trans hpath⟩
  exact aux _ q rfl hclose

end TwinWidthI.BallGraph.TWFresh

-- Complete module: TWBProof.IntegerLabels

namespace TwinWidthI.BallGraph.TWFresh
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}

def labelOffset (q : V → Fin d → ℤ) (i : Fin d) : ℤ := ∑ v, |q v i|
def natLabel (q : V → Fin d → ℤ) (v : V) (i : Fin d) : ℕ := (q v i + labelOffset q i).toNat

omit [DecidableEq V] in
lemma label_shift_nonneg (q : V → Fin d → ℤ) (v : V) (i : Fin d) :
    0 ≤ q v i + labelOffset q i := by
  have h : |q v i| ≤ labelOffset q i := single_le_sum (fun w _ => abs_nonneg (q w i)) (mem_univ v)
  have h' := neg_abs_le (q v i)
  omega

omit [DecidableEq V] in
lemma natLabel_cast (q : V → Fin d → ℤ) (v : V) (i : Fin d) :
    (natLabel q v i : ℤ) = q v i + labelOffset q i :=
  Int.toNat_of_nonneg (label_shift_nonneg q v i)

omit [DecidableEq V] in
lemma natLabel_eq_iff (q : V → Fin d → ℤ) (u v : V) : natLabel q u = natLabel q v ↔ q u = q v := by
  constructor
  · intro h
    funext i
    have he := congrArg (fun f : Fin d → ℕ => (f i : ℤ)) h
    rw [natLabel_cast,natLabel_cast] at he
    omega
  · intro h
    funext i
    simp only [natLabel,h]

omit [DecidableEq V] in
lemma natLabel_close (q : V → Fin d → ℤ) {u v : V}
    (h : ∀ i, |q u i - q v i| ≤ 1) : LabelsClose (natLabel q u) (natLabel q v) := by
  intro i
  have h := abs_le.mp (h i)
  have hu := natLabel_cast q u i
  have hv := natLabel_cast q v i
  omega

lemma fiber_le_of_kernel {L K : Type*} (f : V → L) (g : V → K)
    (h : ∀ u v, f u = f v → g u = g v) : fiberPartition f ≤ fiberPartition g := by
  apply (refinesLabel_iff _ _).mp
  intro A hA
  obtain ⟨u,hu⟩ := (fiberPartition f).nonempty_of_mem_parts hA
  refine ⟨g u,fun v hv => ?_⟩
  exact h v u (eq_label_of_same_part f (fiberPartition f) le_rfl hA hv hu)

lemma natLabel_fiber (q : V → Fin d → ℤ) : fiberPartition (natLabel q) = fiberPartition q := by
  apply le_antisymm
  · exact fiber_le_of_kernel _ _ (fun u v => (natLabel_eq_iff q u v).mp)
  · exact fiber_le_of_kernel _ _ (fun u v => (natLabel_eq_iff q u v).mpr)

lemma integer_labels_reach (H : SimpleGraph V) (q : V → Fin d → ℤ)
    (hclose : ∀ u v, H.Adj u v → ∀ i, |q u i - q v i| ≤ 1) :
    ∃ Q : Finpartition (univ : Finset V), Q.parts.card ≤ 1 ∧
      MergeReach (fun P => IsRedDPartition H P (2 * 3 ^ d)) (fiberPartition q) Q := by
  obtain ⟨Q,hQ,hpath⟩ := dyadic_reach_end H (natLabel q) (fun u v huv => natLabel_close q (hclose u v huv))
  rw [natLabel_fiber] at hpath
  exact ⟨Q,hQ,hpath⟩

end TwinWidthI.BallGraph.TWFresh

-- Complete module: TWBProof.FloorGeometry

namespace TwinWidthI.BallGraph.TWFresh

noncomputable def coarseCoord (x : ℝ) : ℤ := ⌊x / 2⌋
noncomputable def fineCoord (r : ℕ) (x : ℝ) : ℤ := ⌊(r : ℝ) * x / 2⌋

theorem coarseCoord_bounds (x : ℝ) :
    2 * (coarseCoord x : ℝ) ≤ x ∧ x < 2 * ((coarseCoord x : ℝ) + 1) := by
  have h1 := Int.floor_le (x / 2)
  have h2 := Int.lt_floor_add_one (x / 2)
  dsimp [coarseCoord]
  constructor <;> linarith

theorem coarseCoord_le_succ {x y : ℝ} (hxy : x - y ≤ 2) :
    coarseCoord x ≤ coarseCoord y + 1 := by
  by_contra h
  have hz : coarseCoord y + 2 ≤ coarseCoord x := by omega
  have hr : (coarseCoord y : ℝ) + 2 ≤ (coarseCoord x : ℝ) := by exact_mod_cast hz
  have hx := (coarseCoord_bounds x).1
  have hy := (coarseCoord_bounds y).2
  linarith

theorem coarseCoord_close {x y : ℝ} (hxy : |x - y| ≤ 2) :
    |coarseCoord x - coarseCoord y| ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hxy
  have h1 := coarseCoord_le_succ hhi
  have h2 := coarseCoord_le_succ (show y - x ≤ 2 by linarith)
  rw [abs_le]
  omega

theorem fineCoord_bounds (r : ℕ) (x : ℝ) :
    2 * (fineCoord r x : ℝ) ≤ (r : ℝ) * x ∧
      (r : ℝ) * x < 2 * ((fineCoord r x : ℝ) + 1) := by
  have h1 := Int.floor_le ((r : ℝ) * x / 2)
  have h2 := Int.lt_floor_add_one ((r : ℝ) * x / 2)
  dsimp [fineCoord]
  constructor <;> linarith

theorem fineCoord_same_distance {r : ℕ} (hr : 0 < r) {x y : ℝ}
    (h : fineCoord r x = fineCoord r y) : |x - y| ≤ 2 / (r : ℝ) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hx := fineCoord_bounds r x
  have hy := fineCoord_bounds r y
  rw [h] at hx
  have h1 : x - y ≤ 2 / (r : ℝ) := (le_div_iff₀ hr').mpr (by nlinarith)
  have h2 : y - x ≤ 2 / (r : ℝ) := (le_div_iff₀ hr').mpr (by nlinarith)
  exact abs_le.mpr ⟨by linarith, h1⟩

theorem fineCoord_remainder_bounds {r : ℕ} (hr : 0 < r) (x : ℝ) :
    0 ≤ fineCoord r x - (r : ℤ) * coarseCoord x ∧
      fineCoord r x - (r : ℤ) * coarseCoord x < r := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hc := coarseCoord_bounds x
  have hlo : (r : ℤ) * coarseCoord x ≤ fineCoord r x := by
    apply Int.le_floor.mpr
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hc.1 hr'.le]
  have hhi : fineCoord r x < (r : ℤ) * coarseCoord x + r := by
    apply Int.floor_lt.mpr
    push_cast
    nlinarith [mul_lt_mul_of_pos_left hc.2 hr']
  omega

end TwinWidthI.BallGraph.TWFresh

-- Complete module: TWBProof.CellGeometry

namespace TwinWidthI.BallGraph.TWFresh

noncomputable def coarseLabel {V : Type*} {d : ℕ}
    (c : V → EuclideanSpace ℝ (Fin d)) (v : V) : Fin d → ℤ :=
  fun i => coarseCoord (c v i)

noncomputable def fineLabel {V : Type*} {d : ℕ} (r : ℕ)
    (c : V → EuclideanSpace ℝ (Fin d)) (v : V) : Fin d → ℤ :=
  fun i => fineCoord r (c v i)

theorem ceil_sqrt_pos {d : ℕ} (hd : 0 < d) : 0 < ⌈Real.sqrt d⌉₊ := by
  apply Nat.ceil_pos.mpr
  exact Real.sqrt_pos.mpr (by exact_mod_cast hd)

theorem le_ceil_sqrt_sq (d : ℕ) : (d : ℝ) ≤ (⌈Real.sqrt d⌉₊ : ℝ) ^ 2 := by
  have h := Nat.le_ceil (Real.sqrt (d : ℝ))
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ d by positivity)
  have hn := Real.sqrt_nonneg (d : ℝ)
  nlinarith

theorem coordinate_dist_le {d : ℕ} (x y : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    |x i - y i| ≤ dist x y := by
  simpa only [dist_eq_norm, PiLp.sub_apply, Real.norm_eq_abs] using
    (PiLp.norm_apply_le (x - y) i)

theorem coarseLabel_edge_close {V : Type*} {d : ℕ}
    (c : V → EuclideanSpace ℝ (Fin d)) {u v : V}
    (h : (ballGraph c).Adj u v) (i : Fin d) :
    |coarseLabel c u i - coarseLabel c v i| ≤ 1 := by
  exact coarseCoord_close ((coordinate_dist_le (c u) (c v) i).trans h.2)

theorem fineLabel_distance {V : Type*} {d r : ℕ}
    (c : V → EuclideanSpace ℝ (Fin d)) (hr : 0 < r)
    (hdr : (d : ℝ) ≤ (r : ℝ) ^ 2) {u v : V}
    (h : fineLabel r c u = fineLabel r c v) : dist (c u) (c v) ≤ 2 := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hcoord (i : Fin d) : ((c u - c v) i) ^ 2 ≤ (2 / (r : ℝ)) ^ 2 := by
    have hi := fineCoord_same_distance hr (congrFun h i)
    have hs := mul_self_le_mul_self (abs_nonneg _) hi
    simpa only [PiLp.sub_apply, ← sq, sq_abs] using hs
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hcoord i)
  have hnorm : ‖c u - c v‖ ^ 2 ≤ (d : ℝ) * (2 / (r : ℝ)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa using hsum
  have hbound : (d : ℝ) * (2 / (r : ℝ)) ^ 2 ≤ 4 := by
    have hm := mul_le_mul_of_nonneg_right hdr (sq_nonneg (2 / (r : ℝ)))
    have he : (r : ℝ) ^ 2 * (2 / (r : ℝ)) ^ 2 = 4 := by
      field_simp
      ring
    exact hm.trans_eq he
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (c u - c v)]

end TwinWidthI.BallGraph.TWFresh

-- Complete module: TWBProof.CellCardinality

namespace TwinWidthI.BallGraph.TWFresh

open Finset

theorem clique_card_le {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {k : ℕ} (hK : G.CliqueFree (k + 1)) {s : Finset V} (hs : G.IsClique s) :
    s.card ≤ k := by
  by_contra h
  obtain ⟨t, hts, ht⟩ := Finset.exists_subset_card_eq (show k + 1 ≤ s.card by omega)
  exact hK t ⟨hs.subset hts, ht⟩

theorem fineLabel_clique {V : Type*} [DecidableEq V] {d r : ℕ}
    (c : V → EuclideanSpace ℝ (Fin d)) (hr : 0 < r)
    (hdr : (d : ℝ) ≤ (r : ℝ) ^ 2) {s : Finset V} {z : Fin d → ℤ}
    (hs : ∀ v ∈ s, fineLabel r c v = z) : (ballGraph c).IsClique s := by
  intro u hu v hv huv
  exact ⟨huv, fineLabel_distance c hr hdr ((hs u hu).trans (hs v hv).symm)⟩

noncomputable def fineResidue {V : Type*} {d r : ℕ}
    (c : V → EuclideanSpace ℝ (Fin d)) (hr : 0 < r) (v : V) : Fin d → Fin r :=
  fun i => ⟨(fineCoord r (c v i) - (r : ℤ) * coarseCoord (c v i)).toNat,
    by
      have h := fineCoord_remainder_bounds hr (c v i)
      omega⟩

theorem fineLabel_eq_of_residue_eq {V : Type*} {d r : ℕ}
    (c : V → EuclideanSpace ℝ (Fin d)) (hr : 0 < r) {u v : V}
    (hc : coarseLabel c u = coarseLabel c v)
    (hf : fineResidue c hr u = fineResidue c hr v) :
    fineLabel r c u = fineLabel r c v := by
  funext i
  have hc' := congrFun hc i
  have hf' := congrArg Fin.val (congrFun hf i)
  have hu := fineCoord_remainder_bounds hr (c u i)
  have hv := fineCoord_remainder_bounds hr (c v i)
  change coarseCoord (c u i) = coarseCoord (c v i) at hc'
  change (fineCoord r (c u i) - (r : ℤ) * coarseCoord (c u i)).toNat =
    (fineCoord r (c v i) - (r : ℤ) * coarseCoord (c v i)).toNat at hf'
  change fineCoord r (c u i) = fineCoord r (c v i)
  rw [hc'] at hu hf'
  omega

theorem coarse_fiber_card_le {V : Type*} [DecidableEq V] {d r k : ℕ}
    (c : V → EuclideanSpace ℝ (Fin d)) (hr : 0 < r)
    (hdr : (d : ℝ) ≤ (r : ℝ) ^ 2) (hK : (ballGraph c).CliqueFree (k + 1))
    (s : Finset V) (z : Fin d → ℤ) (hs : ∀ v ∈ s, coarseLabel c v = z) :
    s.card ≤ r ^ d * k := by
  classical
  have hf (a : Fin d → Fin r) : (s.filter (fun v => fineResidue c hr v = a)).card ≤ k := by
    apply clique_card_le (ballGraph c) hK
    intro u hu v hv huv
    have hu' := mem_filter.mp hu
    have hv' := mem_filter.mp hv
    exact ⟨huv, fineLabel_distance c hr hdr (fineLabel_eq_of_residue_eq c hr
      ((hs u hu'.1).trans (hs v hv'.1).symm) (hu'.2.trans hv'.2.symm))⟩
  calc
    s.card = ∑ a : Fin d → Fin r, (s.filter (fun v => fineResidue c hr v = a)).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
    _ ≤ ∑ _a : Fin d → Fin r, k := sum_le_sum (fun a _ => hf a)
    _ = r ^ d * k := by simp

end TwinWidthI.BallGraph.TWFresh

-- Complete module: TWBProof.NeighborLabels

namespace TwinWidthI.BallGraph.TWFresh

open Finset

noncomputable def neighborLabels {d : ℕ} (z : Fin d → ℤ) : Finset (Fin d → ℤ) :=
  Finset.univ.image (fun a : Fin d → Fin 3 => fun i => z i + (a i : ℕ) - 1)

theorem neighborLabels_card {d : ℕ} (z : Fin d → ℤ) :
    (neighborLabels z).card ≤ 3 ^ d := by
  classical
  exact (card_image_le).trans_eq (by simp)

theorem mem_neighborLabels {d : ℕ} {z w : Fin d → ℤ}
    (h : ∀ i, |w i - z i| ≤ 1) : w ∈ neighborLabels z := by
  classical
  let a : Fin d → Fin 3 := fun i => ⟨(w i - z i + 1).toNat, by
    have hi := abs_le.mp (h i)
    omega⟩
  apply mem_image.mpr
  refine ⟨a, mem_univ _, ?_⟩
  funext i
  have hi := abs_le.mp (h i)
  change z i + (((w i - z i + 1).toNat : ℕ) : ℤ) - 1 = w i
  omega

theorem neighborLabels_close {d : ℕ} {z w : Fin d → ℤ}
    (h : w ∈ neighborLabels z) (i : Fin d) : |w i - z i| ≤ 1 := by
  classical
  obtain ⟨a, _, rfl⟩ := mem_image.mp h
  have ha := (a i).isLt
  change |z i + ((a i : ℕ) : ℤ) - 1 - z i| ≤ 1
  rw [abs_le]
  constructor <;> omega

end TwinWidthI.BallGraph.TWFresh

-- Complete module: TWBProof.InitialRedBound

namespace TwinWidthI.BallGraph.TWFresh

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem initial_red_bound {d r k : ℕ} (c : V → EuclideanSpace ℝ (Fin d))
    (hr : 0 < r) (hdr : (d : ℝ) ≤ (r : ℝ) ^ 2)
    (hK : (ballGraph c).CliqueFree (k + 1)) (H : SimpleGraph V) (hH : H ≤ ballGraph c)
    (P : Finpartition (univ : Finset V)) (hP : RefinesLabel P (coarseLabel c)) :
    IsRedDPartition H P ((3 * r) ^ d * k) := by
  classical
  apply red_degree_le_vertices H P
  intro A hA
  obtain ⟨z, hz⟩ := hP A hA
  let T := univ.filter (fun v => coarseLabel c v ∈ neighborLabels z)
  refine ⟨T, ?_, ?_⟩
  · have hc (w : Fin d → ℤ) (_hw : w ∈ neighborLabels z) :
        (univ.filter (fun v => coarseLabel c v = w)).card ≤ r ^ d * k := by
      apply coarse_fiber_card_le c hr hdr hK _ w
      intro v hv
      exact (mem_filter.mp hv).2
    have ht := label_union_card (coarseLabel c) (neighborLabels z) (r ^ d * k) hc
    have hn := Nat.mul_le_mul_right (r ^ d * k) (neighborLabels_card z)
    exact ht.trans (hn.trans_eq (by rw [mul_pow]; ring))
  · intro B hB _hBA hedge v hv
    obtain ⟨u, hu, w, hw, huw⟩ := hedge
    obtain ⟨q, hq⟩ := hP B hB
    apply mem_filter.mpr
    refine ⟨mem_univ _, mem_neighborLabels (fun i => ?_)⟩
    have he := coarseLabel_edge_close c (hH huw) i
    have hu' := congrFun (hz u hu) i
    have hw' := congrFun (hq w hw) i
    have hv' := congrFun (hq v hv) i
    rw [hu', hw'] at he
    rw [hv', abs_sub_comm]
    exact he

theorem initial_red_bound_ceil {d k : ℕ} (hd : 0 < d)
    (c : V → EuclideanSpace ℝ (Fin d))
    (hK : (ballGraph c).CliqueFree (k + 1)) (H : SimpleGraph V) (hH : H ≤ ballGraph c)
    (P : Finpartition (univ : Finset V)) (hP : RefinesLabel P (coarseLabel c)) :
    IsRedDPartition H P ((3 * ⌈Real.sqrt d⌉₊) ^ d * k) :=
  initial_red_bound c (ceil_sqrt_pos hd) (le_ceil_sqrt_sq d) hK H hH P hP

end TwinWidthI.BallGraph.TWFresh

-- Complete module: TWBProof.PathSequence

namespace TwinWidthI.BallGraph.TWFresh
open Finset TwinWidthI.BoolWidth
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma reach_sequence (good : Finpartition (univ : Finset V) → Prop)
    {P Q : Finpartition (univ : Finset V)} (hP : good P) (h : MergeReach good P Q) :
    ∃ N : ℕ, ∃ seq : Fin (N + 1) → Finpartition (univ : Finset V),
      seq 0 = P ∧ seq (Fin.last N) = Q ∧
      (∀ i : Fin N, IsMergeStep (seq i.castSucc) (seq i.succ)) ∧ ∀ i, good (seq i) := by
  induction h with
  | refl =>
    refine ⟨0, fun _ => P, rfl, rfl, ?_, fun _ => hP⟩
    intro i; exact Fin.elim0 i
  | @tail R Q hprev hstep ih =>
    obtain ⟨N, seq, hstart, hend, hsteps, hgood⟩ := ih
    let seq' : Fin (N + 1 + 1) → Finpartition (univ : Finset V) := Fin.lastCases Q seq
    refine ⟨N + 1, seq', ?_, ?_, ?_, ?_⟩
    · change Fin.lastCases Q seq (Fin.castSucc (0 : Fin (N + 1))) = P
      rw [Fin.lastCases_castSucc]
      exact hstart
    · simp [seq']
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have hs : IsMergeStep (seq (Fin.last N)) Q := by rw [hend]; exact hstep.1
        change IsMergeStep (Fin.lastCases Q seq (Fin.last N).castSucc) (Fin.lastCases Q seq (Fin.last N).succ)
        rw [Fin.succ_last, Fin.lastCases_castSucc, Fin.lastCases_last]
        exact hs
      · change IsMergeStep (Fin.lastCases Q seq j.castSucc.castSucc) (Fin.lastCases Q seq j.succ.castSucc)
        rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc]
        exact hsteps j
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [seq', Fin.lastCases_last] using hstep.2
      · simpa only [seq', Fin.lastCases_castSucc] using hgood j

lemma red_implies_graph (H : SimpleGraph V) (P : Finpartition (univ : Finset V)) (D : ℕ)
    (h : IsRedDPartition H P D) : IsDPartition H P D := by
  classical
  intro A hA
  apply le_trans (card_le_card ?_) (h A hA)
  intro B hB
  simp only [mem_filter] at hB ⊢
  refine ⟨hB.1,hB.2.1,?_⟩
  by_contra hn
  apply hB.2.2
  right
  intro u hu v hv hadj
  exact hn ⟨u,hu,v,hv,hadj⟩

lemma native_of_red_reach (H : SimpleGraph V) (D : ℕ)
    (Q : Finpartition (univ : Finset V)) (hQ : Q.parts.card ≤ 1)
    (hbot : IsRedDPartition H ⊥ D)
    (h : MergeReach (fun P => IsRedDPartition H P D) ⊥ Q) : TwinWidthLE H D := by
  obtain ⟨N,seq,hstart,hend,hsteps,hgood⟩ := reach_sequence _ hbot h
  exact ⟨N,seq,hstart,by simpa [hend] using hQ,hsteps,
    fun i => red_implies_graph H (seq i) D (hgood i)⟩

end TwinWidthI.BallGraph.TWFresh

-- Complete module: TWBProof.GeometricAssembly

namespace TwinWidthI.BallGraph.TWFresh
open Finset TwinWidthI.BoolWidth
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma red_bound_mono (H : SimpleGraph V) (P : Finpartition (univ : Finset V))
    {a b : ℕ} (hab : a ≤ b) (h : IsRedDPartition H P a) : IsRedDPartition H P b :=
  fun A hA => (h A hA).trans hab

lemma mergeReach_mono {good good' : Finpartition (univ : Finset V) → Prop}
    (hg : ∀ P, good P → good' P) {P Q : Finpartition (univ : Finset V)}
    (h : MergeReach good P Q) : MergeReach good' P Q := by
  induction h with
  | refl => exact .refl
  | tail hprev hstep ih => exact ih.tail ⟨hstep.1, hg _ hstep.2⟩

lemma dyadic_bound_le {d r k : ℕ} (hr : 1 ≤ r) (hk : 2 ≤ k) :
    2 * 3 ^ d ≤ (3 * r) ^ d * k := by
  have hp : 3 ^ d ≤ (3 * r) ^ d := Nat.pow_le_pow_left (by omega) d
  calc
    2 * 3 ^ d = 3 ^ d * 2 := Nat.mul_comm _ _
    _ ≤ (3 * r) ^ d * k := Nat.mul_le_mul hp hk

theorem positive_geometry_twinWidth {d k : ℕ} (hd : 0 < d) (hk : 2 ≤ k)
    (c : V → EuclideanSpace ℝ (Fin d)) (hK : (ballGraph c).CliqueFree (k + 1))
    (H : SimpleGraph V) (hH : H ≤ ballGraph c) :
    TwinWidthLE H ((3 * ⌈Real.sqrt d⌉₊) ^ d * k) := by
  let D := (3 * ⌈Real.sqrt d⌉₊) ^ d * k
  let P := fiberPartition (coarseLabel c)
  have hgood (R : Finpartition (univ : Finset V)) (hR : R ≤ P) : IsRedDPartition H R D :=
    initial_red_bound_ceil hd c hK H hH R ((refinesLabel_iff _ _).mpr hR)
  have hinit : MergeReach (fun R => IsRedDPartition H R D) ⊥ P :=
    refinement_reach ⊥ P bot_le _ (fun R _ hR => hgood R hR)
  obtain ⟨Q,hQ,hpath⟩ := integer_labels_reach H (coarseLabel c)
    (fun u v huv => coarseLabel_edge_close c (hH huv))
  have hb : 2 * 3 ^ d ≤ D := dyadic_bound_le (ceil_sqrt_pos hd) hk
  exact native_of_red_reach H D Q hQ (hgood ⊥ bot_le)
    (hinit.trans (mergeReach_mono (fun R hR => red_bound_mono H R hb hR) hpath))

end TwinWidthI.BallGraph.TWFresh

-- Complete module: TWBProof.GeometricGuards

namespace TwinWidthI.BallGraph.TWFresh

open Finset

theorem cliqueFree_one_isEmpty {V : Type*} (G : SimpleGraph V)
    (h : G.CliqueFree 1) : IsEmpty V := by
  refine ⟨fun v => ?_⟩
  exact h {v} ((SimpleGraph.isNClique_singleton).mpr rfl)

theorem cliqueFree_two_no_edge {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (h : G.CliqueFree 2) {u v : V} : ¬G.Adj u v := by
  intro huv
  have hc : G.IsClique ({u, v} : Finset V) := by
    simpa using (SimpleGraph.isClique_pair.mpr (fun _ => huv))
  have hn := clique_card_le G h hc
  have hu : u ≠ v := G.ne_of_adj huv
  rw [card_pair_eq_two_iff.mpr hu] at hn
  omega

theorem zero_dim_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → EuclideanSpace ℝ (Fin 0)) {k : ℕ}
    (hK : (ballGraph c).CliqueFree (k + 1)) : Fintype.card V ≤ k := by
  have hc : (ballGraph c).IsClique (univ : Finset V) := by
    intro u _ v _ huv
    refine ⟨huv, ?_⟩
    have he : c u = c v := Subsingleton.elim _ _
    rw [he, dist_self]
    norm_num
  simpa using clique_card_le (ballGraph c) hK hc

theorem ballGraph_restrict {V : Type*} {d : ℕ}
    (c : V → EuclideanSpace ℝ (Fin d)) (S : Set V) :
    ballGraph (fun v : S => c v) = (ballGraph c).induce S := by
  ext u v
  change (u ≠ v ∧ dist (c u) (c v) ≤ 2) ↔
    ((u : V) ≠ (v : V) ∧ dist (c u) (c v) ≤ 2)
  constructor
  · intro h
    exact ⟨fun he => h.1 (Subtype.ext he), h.2⟩
  · intro h
    exact ⟨fun he => h.1 (congrArg Subtype.val he), h.2⟩

theorem cliqueFree_ballGraph_restrict {V : Type*} {d k : ℕ}
    (c : V → EuclideanSpace ℝ (Fin d)) (S : Set V)
    (hK : (ballGraph c).CliqueFree k) :
    (ballGraph (fun v : S => c v)).CliqueFree k := by
  rw [ballGraph_restrict, SimpleGraph.cliqueFree_induce_iff]
  intro t _ht
  exact hK t

end TwinWidthI.BallGraph.TWFresh

-- Complete module: TWBProof.TrivialBounds

namespace TwinWidthI.BallGraph.TWFresh

open Finset TwinWidthI.BoolWidth

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem native_of_all_red_partitions (H : SimpleGraph V) (D : ℕ)
    (h : ∀ P : Finpartition (univ : Finset V), IsRedDPartition H P D) : TwinWidthLE H D := by
  classical
  have ht : (⊤ : Finpartition (univ : Finset V)).parts.card ≤ 1 := by
    exact (card_le_card (Finpartition.parts_top_subset (univ : Finset V))).trans_eq (card_singleton _)
  apply native_of_red_reach H D ⊤ ht (h ⊥)
  exact refinement_reach ⊥ ⊤ bot_le _ (fun P _ _ => h P)

theorem red_partition_of_card_le (H : SimpleGraph V) (D : ℕ)
    (hD : Fintype.card V ≤ D) (P : Finpartition (univ : Finset V)) :
    IsRedDPartition H P D := by
  apply red_degree_le_vertices H P
  intro A _hA
  refine ⟨univ, ?_, fun B _ _ _ => subset_univ B⟩
  simpa using hD

theorem native_of_card_le (H : SimpleGraph V) (D : ℕ) (hD : Fintype.card V ≤ D) :
    TwinWidthLE H D :=
  native_of_all_red_partitions H D (red_partition_of_card_le H D hD)

theorem red_partition_of_no_edges (H : SimpleGraph V) (D : ℕ)
    (hH : ∀ u v, ¬H.Adj u v) (P : Finpartition (univ : Finset V)) :
    IsRedDPartition H P D := by
  classical
  intro A _hA
  have he : (P.parts.filter (fun B => B ≠ A ∧ SomeEdge H A B)) = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro B _hB hB
    obtain ⟨u, _hu, v, _hv, huv⟩ := hB.2
    exact hH u v huv
  rw [he, card_empty]
  exact Nat.zero_le D

theorem native_of_no_edges (H : SimpleGraph V) (D : ℕ) (hH : ∀ u v, ¬H.Adj u v) :
    TwinWidthLE H D :=
  native_of_all_red_partitions H D (red_partition_of_no_edges H D hH)

end TwinWidthI.BallGraph.TWFresh

-- Complete module: TWBProof.NativeConclusion

namespace TwinWidthI.BallGraph.TWFresh
open Finset TwinWidthI.BoolWidth

 theorem geometry_twinWidth {V : Type*} [Fintype V] [DecidableEq V] (d k : ℕ)
    (c : V → EuclideanSpace ℝ (Fin d)) (hK : (ballGraph c).CliqueFree (k + 1))
    (H : SimpleGraph V) (hH : H ≤ ballGraph c) :
    TwinWidthLE H ((3 * ⌈Real.sqrt d⌉₊) ^ d * k) := by
  by_cases hd : d = 0
  · subst d
    have hc := zero_dim_card_le c hK
    apply native_of_card_le H _
    simpa using hc
  by_cases hk : k = 0
  · subst k
    let : IsEmpty V := cliqueFree_one_isEmpty (ballGraph c) hK
    apply native_of_card_le H _
    simp
  by_cases hk1 : k = 1
  · subst k
    exact native_of_no_edges H _ (fun u v huv => cliqueFree_two_no_edge (ballGraph c) hK (hH huv))
  exact positive_geometry_twinWidth (Nat.pos_of_ne_zero hd) (by omega) c hK H hH

 theorem native_theorem_4_5 (d k : ℕ) {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → EuclideanSpace ℝ (Fin d)) (hK : (ballGraph c).CliqueFree (k + 1))
    (S : Finset V) (H : SimpleGraph S) (hH : H ≤ (ballGraph c).induce (S : Set V)) :
    TwinWidthI.BoolWidth.TwinWidthLE H ((3 * ⌈Real.sqrt d⌉₊) ^ d * k) := by
  apply geometry_twinWidth d k (fun v : S => c v)
    (cliqueFree_ballGraph_restrict c (S : Set V) hK) H
  change H ≤ ballGraph (fun v : (S : Set V) => c v)
  rw [ballGraph_restrict]
  exact hH

end TwinWidthI.BallGraph.TWFresh

-- Complete module: TWBProof.FinalRoot

namespace TwinWidthI.BallGraph

/-- Theorem 4.5, p. 3:15: every subgraph `H` of a unit d-dimensional ball graph `G` with clique
number (at most) `k` has twin-width at most `(3⌈√d⌉)^d k`. -/
theorem theorem_4_5 (d k : ℕ) {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → EuclideanSpace ℝ (Fin d)) (hK : (ballGraph c).CliqueFree (k + 1))
    (S : Finset V) (H : SimpleGraph S) (hH : H ≤ (ballGraph c).induce (S : Set V)) :
    TwinWidthI.BoolWidth.TwinWidthLE H ((3 * ⌈Real.sqrt d⌉₊) ^ d * k) := by
  exact TWFresh.native_theorem_4_5 d k c hK S H hH

end TwinWidthI.BallGraph

open TwinWidthI.BallGraph

theorem solution (d k : ℕ) {V : Type*} [Fintype V] [DecidableEq V]
    (c : V → EuclideanSpace ℝ (Fin d)) (hK : (ballGraph c).CliqueFree (k + 1))
    (S : Finset V) (H : SimpleGraph S) (hH : H ≤ (ballGraph c).induce (S : Set V)) :
    TwinWidthI.BoolWidth.TwinWidthLE H ((3 * ⌈Real.sqrt d⌉₊) ^ d * k) := by
  exact theorem_4_5 d k c hK S H hH
