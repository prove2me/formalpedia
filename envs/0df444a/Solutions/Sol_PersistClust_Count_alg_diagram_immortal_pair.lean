-- Prove2me | solution 1 for PersistClust.Count.alg_diagram_immortal_pair
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-09T14:16:02.388999+00:00
-- url     : https://prove2.me/submissions/607668b0-e758-433a-83d8-b935fee5936e

import Mathlib
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_AlgBarcode
import Definitions.Def_PersistClust_Count_Rips

open PersistClust.Count
open Classical
open scoped ENNReal

/-!
# Immortal slice: `alg_diagram_immortal_pair` (ID 294b82cc)
-/

namespace AlgImmortal

abbrev fullConn {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (i j : Fin n) : Prop :=
  Relation.ReflTransGen (ripsGraph Dm δ).Adj i j

abbrev fullComp {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (i : Fin n) : Set (Fin n) :=
  {j | fullConn Dm δ i j}

abbrev fullComps {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ) : Set (Set (Fin n)) :=
  (fun i => fullComp Dm δ i) '' Set.univ

abbrev L {n : ℕ} (g : Fin n → ℝ) (s : ℝ) (i : Fin n) : Prop := s ≤ g i

abbrev classAt {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (t : ℝ)
    (i : Fin n) : Set (Fin n) := {j | ripsJoined Dm g δ t i j}

abbrev imgAt {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (s t : ℝ) :
    Set (Set (Fin n)) := (fun i => classAt g Dm δ t i) '' {i | L g s i}

def maxgIs {n : ℕ} (g : Fin n → ℝ) (b : ℝ) (C : Set (Fin n)) : Prop :=
  (∃ i ∈ C, g i = b) ∧ (∀ j ∈ C, (g j : ℝ) ≤ b)

def windowIs {n : ℕ} (g : Fin n → ℝ) (b ε : ℝ) (C : Set (Fin n)) : Prop :=
  (∃ i ∈ C, b - ε ≤ g i) ∧ (∀ j ∈ C, (g j : ℝ) < b + ε)

noncomputable def V_imm {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (b : ℝ) : ℕ∞ :=
  {C ∈ fullComps Dm δ | maxgIs g b C}.encard

/-! ### Generic relation helpers -/

lemma rtg_mono {α : Type*} {r p : α → α → Prop} (h : ∀ a b, r a b → p a b)
    {a b : α} (hrt : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b := by
  induction hrt with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.trans ih (Relation.ReflTransGen.single (h _ _ hstep))

lemma rtg_symm {α : Type*} {r : α → α → Prop} (hsymm : ∀ a b, r a b → r b a)
    {a b : α} (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprev hstep ih =>
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single (hsymm _ _ hstep)) ih

/-! ### Adjacency -/

lemma Adj_symm {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (i j : Fin n)
    (h : (ripsGraph Dm δ).Adj i j) : (ripsGraph Dm δ).Adj j i := by
  rw [ripsGraph, SimpleGraph.fromRel] at h ⊢
  exact ⟨h.1.symm, h.2.symm⟩

/-! ### ripsJoined as an equivalence class -/

lemma ripsStep_symm {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (t : ℝ)
    (a b : Fin n) : (t ≤ g a ∧ t ≤ g b ∧ (ripsGraph Dm δ).Adj a b) →
    (t ≤ g b ∧ t ≤ g a ∧ (ripsGraph Dm δ).Adj b a) :=
  fun h => ⟨h.2.1, h.1, Adj_symm Dm δ a b h.2.2⟩

lemma ripsJoined_symm {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (t : ℝ)
    {i j : Fin n} (hj : L g t j) (h : ripsJoined Dm g δ t i j) :
    ripsJoined Dm g δ t j i :=
  ⟨hj, rtg_symm (ripsStep_symm g Dm δ t) h.2⟩

lemma ripsJoined_mem_self {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (t : ℝ) {i : Fin n} (hi : L g t i) : i ∈ classAt g Dm δ t i :=
  ⟨hi, Relation.ReflTransGen.refl⟩

lemma ripsJoined_trans {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (t : ℝ)
    {i j k : Fin n} (hij : ripsJoined Dm g δ t i j) (hjk : ripsJoined Dm g δ t j k) :
    ripsJoined Dm g δ t i k :=
  ⟨hij.1, Relation.ReflTransGen.trans hij.2 hjk.2⟩

lemma L_of_rtg {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (t : ℝ)
    {a b : Fin n} (ha : L g t a)
    (hrt : Relation.ReflTransGen (fun x y => t ≤ g x ∧ t ≤ g y ∧ (ripsGraph Dm δ).Adj x y) a b) :
    L g t b := by
  induction hrt with
  | refl => exact ha
  | tail _ hstep _ => exact hstep.2.1

lemma classAt_eq_of_mem {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (t : ℝ) {i y : Fin n} (hi : i ∈ classAt g Dm δ t y) :
    classAt g Dm δ t i = classAt g Dm δ t y := by
  obtain ⟨hy, hrt⟩ := hi
  have hiL : L g t i := L_of_rtg g Dm δ t hy hrt
  ext j
  constructor
  · intro hij
    exact ⟨hy, Relation.ReflTransGen.trans hrt hij.2⟩
  · intro hjy
    exact ripsJoined_trans g Dm δ t (ripsJoined_symm g Dm δ t hiL ⟨hy, hrt⟩) hjy

/-! ### Low level `t`: ~_t classes are full-graph components -/

lemma ripsJoined_eq_fullConn {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (t : ℝ) (hlow : ∀ a : Fin n, L g t a) (i j : Fin n) :
    ripsJoined Dm g δ t i j ↔ fullConn Dm δ i j := by
  constructor
  · intro h
    exact rtg_mono (fun _ _ ha => ha.2.2) h.2
  · intro h
    exact ⟨hlow i, rtg_mono (fun a b ha => ⟨hlow a, hlow b, ha⟩) h⟩

lemma classAt_eq_fullComp {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (t : ℝ) (hlow : ∀ a : Fin n, L g t a) (i : Fin n) :
    classAt g Dm δ t i = fullComp Dm δ i := by
  ext j; exact ripsJoined_eq_fullConn g Dm δ t hlow i j

/-! ### Rank as an encard of an image -/

lemma ripsRank_eq {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (s t : ℝ) :
    ripsRank Dm g δ s t = (imgAt g Dm δ s t).encard := by
  simp only [ripsRank, rankFn, imgAt, L]

lemma imgAt_mono {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) {a a' t : ℝ}
    (h : a ≤ a') : imgAt g Dm δ a' t ⊆ imgAt g Dm δ a t := by
  rintro C ⟨x, hxLa, rfl⟩
  exact ⟨x, h.trans hxLa, rfl⟩

/-! ### "Meets a level" characterization -/

lemma meets_iff {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (t a : ℝ) (hta : t ≤ a) {y : Fin n} :
    classAt g Dm δ t y ∈ imgAt g Dm δ a t ↔ ∃ i ∈ classAt g Dm δ t y, a ≤ g i := by
  constructor
  · rintro ⟨x, hxLa, hx⟩
    refine ⟨x, ?_, hxLa⟩
    rw [← hx]
    exact ripsJoined_mem_self g Dm δ t (hta.trans hxLa)
  · rintro ⟨i, himem, hgi⟩
    exact ⟨i, hgi, classAt_eq_of_mem g Dm δ t himem⟩

/-! ### fullConn as an equivalence relation -/

lemma fullConn_symm {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ) {i j : Fin n}
    (h : fullConn Dm δ i j) : fullConn Dm δ j i := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprev hstep ih =>
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single (Adj_symm Dm δ _ _ hstep)) ih

lemma fullConn_refl {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (i : Fin n) :
    fullConn Dm δ i i := Relation.ReflTransGen.refl

lemma fullComp_eq_of_mem {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ) {i y : Fin n}
    (hi : i ∈ fullComp Dm δ y) : fullComp Dm δ i = fullComp Dm δ y := by
  have hi' : fullConn Dm δ y i := hi
  ext j
  constructor
  · intro hij
    exact Relation.ReflTransGen.trans hi' hij
  · intro hjy
    have hjy' : fullConn Dm δ y j := hjy
    exact Relation.ReflTransGen.trans (fullConn_symm Dm δ hi') hjy'

lemma classAt_subset_fullComp {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (t : ℝ) (i : Fin n) : classAt g Dm δ t i ⊆ fullComp Dm δ i := by
  intro j hj
  exact rtg_mono (fun _ _ ha => ha.2.2) hj.2

/-! ### The gap ε₀ and the low level t₀ -/

noncomputable def gaps {n : ℕ} (g : Fin n → ℝ) (b : ℝ) : Finset ℝ :=
  (Finset.univ.image (fun c : Fin n => |g c - b|)).filter (fun x => x ≠ 0)

noncomputable def ε₀ {n : ℕ} (g : Fin n → ℝ) (b : ℝ) : ℝ :=
  if h : (gaps g b).Nonempty then (gaps g b).min' h / 2 else 1

lemma ε₀_pos {n : ℕ} (g : Fin n → ℝ) (b : ℝ) : 0 < ε₀ g b := by
  unfold ε₀
  split_ifs with h
  · have hmem := (gaps g b).min'_mem h
    have h0 : (0:ℝ) < (gaps g b).min' h := by
      obtain ⟨himg, hne⟩ := Finset.mem_filter.mp hmem
      obtain ⟨c, _, heq⟩ := Finset.mem_image.mp himg
      rw [← heq] at hne ⊢
      exact lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
    positivity
  · exact one_pos

lemma windowMem {n : ℕ} (g : Fin n → ℝ) (b : ℝ) (c : Fin n) :
    (b - ε₀ g b ≤ g c ∧ g c < b + ε₀ g b) ↔ g c = b := by
  have hpos : 0 < ε₀ g b := ε₀_pos g b
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hne
    have habs : |g c - b| ≤ ε₀ g b := abs_le.mpr ⟨by linarith, by linarith⟩
    have hmem : |g c - b| ∈ gaps g b := by
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩
      · intro h0
        exact hne (sub_eq_zero.mp (abs_eq_zero.mp h0))
    have hne' : (gaps g b).Nonempty := ⟨_, hmem⟩
    have heps : ε₀ g b = (gaps g b).min' hne' / 2 := by
      unfold ε₀; rw [dif_pos hne']
    have hmin := (gaps g b).min'_le _ hmem
    rw [heps] at habs
    linarith
  · rintro rfl
    exact ⟨by linarith, by linarith⟩

lemma windowIs_maxg {n : ℕ} (g : Fin n → ℝ) (b : ℝ) (C : Set (Fin n))
    (hw : windowIs g b (ε₀ g b) C) : maxgIs g b C := by
  have hpos : 0 < ε₀ g b := ε₀_pos g b
  obtain ⟨⟨i, hiC, hgi⟩, hall⟩ := hw
  have hieq : g i = b := (windowMem g b i).mp ⟨hgi, hall i hiC⟩
  refine ⟨⟨i, hiC, hieq⟩, ?_⟩
  intro j hjC
  by_contra hge
  push Not at hge
  have : g j = b := (windowMem g b j).mp ⟨by linarith, hall j hjC⟩
  linarith [hge]

noncomputable def minG {n : ℕ} (g : Fin n → ℝ) (hn : 0 < n) : ℝ :=
  (Finset.univ.image g).min' (Finset.image_nonempty.mpr ⟨⟨0, hn⟩, Finset.mem_univ _⟩)

lemma minG_le {n : ℕ} (g : Fin n → ℝ) (hn : 0 < n) (a : Fin n) : minG g hn ≤ g a :=
  (Finset.univ.image g).min'_le (g a) (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)

noncomputable def t₀ {n : ℕ} (g : Fin n → ℝ) (hn : 0 < n) (b : ℝ) : ℝ :=
  min (minG g hn) (b - ε₀ g b) - 1

lemma exists_low {n : ℕ} (g : Fin n → ℝ) (b : ℝ) :
    ∃ t, t ≤ b - ε₀ g b ∧ ∀ a : Fin n, L g t a := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨b - ε₀ g b, le_refl _, fun a => a.elim0⟩
  · refine ⟨t₀ g hn b, ?_, ?_⟩
    · have h1 : t₀ g hn b ≤ (b - ε₀ g b) - 1 :=
        sub_le_sub_right (min_le_right (minG g hn) (b - ε₀ g b)) _
      show t₀ g hn b ≤ b - ε₀ g b
      linarith [ε₀_pos g b]
    · intro a
      have h1 : t₀ g hn b ≤ minG g hn - 1 :=
        sub_le_sub_right (min_le_left (minG g hn) (b - ε₀ g b)) _
      have h4 := minG_le g hn a
      show t₀ g hn b ≤ g a
      linarith

/-! ### Difference of ranks as an encard of a set difference -/

lemma diff_encard {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (b ε t : ℝ) (hε : 0 < ε) :
    (imgAt g Dm δ (b - ε) t).encard - (imgAt g Dm δ (b + ε) t).encard
      = (imgAt g Dm δ (b - ε) t \ imgAt g Dm δ (b + ε) t).encard := by
  have hsub := imgAt_mono (t := t) g Dm δ (show b - ε ≤ b + ε by linarith)
  exact (Set.encard_sdiff hsub (Set.toFinite _)).symm

/-! ### Choosing a max-g vertex in a component -/

noncomputable def pickB {n : ℕ} (g : Fin n → ℝ) (b : ℝ) (C : Set (Fin n)) :
    Option (Fin n) :=
  if h : ∃ i, i ∈ C ∧ g i = b then some h.choose else none

noncomputable def pickClass {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (t b : ℝ) (C : Set (Fin n)) : Set (Fin n) :=
  (pickB g b C).elim C (fun v => classAt g Dm δ t v)

lemma pickClass_spec {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (t b : ℝ) (C : Set (Fin n)) (hC : maxgIs g b C) :
    ∃ v : Fin n, v ∈ C ∧ g v = b ∧ pickClass g Dm δ t b C = classAt g Dm δ t v := by
  have h1 : ∃ i, i ∈ C ∧ g i = b := hC.1
  have hpos : pickB g b C = some h1.choose := dif_pos h1
  refine ⟨h1.choose, h1.choose_spec.1, h1.choose_spec.2, ?_⟩
  show (pickB g b C).elim C (fun v => classAt g Dm δ t v) = classAt g Dm δ t h1.choose
  rw [hpos]
  rfl

/-! ### The analytic lower bound -/

lemma lower_bound {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (b ε t : ℝ) (hε : 0 < ε) (ht : t ≤ b - ε) :
    V_imm g Dm δ b ≤ (imgAt g Dm δ (b - ε) t \ imgAt g Dm δ (b + ε) t).encard := by
  show ({C ∈ fullComps Dm δ | maxgIs g b C}).encard ≤
    (imgAt g Dm δ (b - ε) t \ imgAt g Dm δ (b + ε) t).encard
  refine Set.encard_le_encard_of_injOn
    (f := pickClass g Dm δ t b) ?_ ?_
  · rintro C ⟨hCcomps, hCmax⟩
    obtain ⟨v, hvC, hgv, hpick⟩ := pickClass_spec g Dm δ t b C hCmax
    obtain ⟨u, hu, huC⟩ := hCcomps
    have huCb : fullComp Dm δ u = C := huC
    rw [← huCb] at hvC
    have hCv : fullComp Dm δ v = C := (fullComp_eq_of_mem Dm δ hvC).trans huCb
    refine (Set.mem_sdiff _).mpr ⟨?_, ?_⟩
    · rw [hpick]; exact ⟨v, (show (b - ε) ≤ g v by linarith), rfl⟩
    · intro hmem
      rw [hpick] at hmem
      have hvLt : L g t v := show t ≤ g v by linarith
      obtain ⟨i, himem, hiL⟩ :=
        (meets_iff g Dm δ t (b + ε) (show t ≤ b + ε by linarith) (y := v)).mp hmem
      have hiC : i ∈ fullComp Dm δ v := classAt_subset_fullComp g Dm δ t v himem
      have hig : (g i : ℝ) ≤ b := hCmax.2 i (by rw [← hCv]; exact hiC)
      have : (b:ℝ) + ε ≤ g i := hiL
      linarith
  · intro C₁ hC₁ C₂ hC₂ heq
    obtain ⟨hC₁c, hC₁m⟩ := hC₁
    obtain ⟨hC₂c, hC₂m⟩ := hC₂
    obtain ⟨v₁, hv₁C, hg₁v, hp₁⟩ := pickClass_spec g Dm δ t b C₁ hC₁m
    obtain ⟨v₂, hv₂C, hg₂v, hp₂⟩ := pickClass_spec g Dm δ t b C₂ hC₂m
    rw [hp₁, hp₂] at heq
    have hv₁L : L g t v₁ := show t ≤ g v₁ by linarith
    have hv₁mem : v₁ ∈ classAt g Dm δ t v₁ := ripsJoined_mem_self g Dm δ t hv₁L
    have hv₁₂ : v₁ ∈ classAt g Dm δ t v₂ := heq ▸ hv₁mem
    have hfc : v₁ ∈ fullComp Dm δ v₂ := classAt_subset_fullComp g Dm δ t v₂ hv₁₂
    have hfull : fullComp Dm δ v₁ = fullComp Dm δ v₂ := fullComp_eq_of_mem Dm δ hfc
    have hC₁full : fullComp Dm δ v₁ = C₁ := by
      obtain ⟨u, _, hu⟩ := hC₁c
      have huCb : fullComp Dm δ u = C₁ := hu
      rw [← huCb] at hv₁C
      exact (fullComp_eq_of_mem Dm δ hv₁C).trans huCb
    have hC₂full : fullComp Dm δ v₂ = C₂ := by
      obtain ⟨u, _, hu⟩ := hC₂c
      have huCb : fullComp Dm δ u = C₂ := hu
      rw [← huCb] at hv₂C
      exact (fullComp_eq_of_mem Dm δ hv₂C).trans huCb
    exact hC₁full.symm.trans (hfull.trans hC₂full)

/-! ### The witness level -/

lemma witness_set_eq {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (b t : ℝ) (ht : t ≤ b - ε₀ g b) (hlow : ∀ a : Fin n, L g t a) :
    imgAt g Dm δ (b - ε₀ g b) t \ imgAt g Dm δ (b + ε₀ g b) t
      = {C ∈ fullComps Dm δ | maxgIs g b C} := by
  ext C
  constructor
  · rintro ⟨hA, hB⟩
    obtain ⟨x, hxL, hx⟩ := hA
    have hCt : classAt g Dm δ t x = C := hx
    have hxLt : L g t x := hlow x
    have hCfull : C = fullComp Dm δ x := by
      rw [← hCt]; exact classAt_eq_fullComp g Dm δ t hlow x
    refine ⟨?_, ?_⟩
    · exact (Set.mem_image (fun i => fullComp Dm δ i) Set.univ C).mpr
        ⟨x, Set.mem_univ x, hCfull.symm⟩
    · refine windowIs_maxg g b C ⟨⟨x, ?_, hxL⟩, ?_⟩
      · rw [← hCt]; exact ripsJoined_mem_self g Dm δ t hxLt
      · intro j hjC
        by_contra hge
        push Not at hge
        have hjrt : j ∈ classAt g Dm δ t x := by rw [← hCt] at hjC; exact hjC
        have hclass : classAt g Dm δ t j = C :=
          (classAt_eq_of_mem g Dm δ t hjrt).trans hCt
        exact hB ⟨j, hge, hclass⟩
  · rintro ⟨hCmem, hmaxg⟩
    obtain ⟨v, hvC, hgv⟩ := hmaxg.1
    obtain ⟨u, -, hu⟩ := hCmem
    have huCb : fullComp Dm δ u = C := hu
    rw [← huCb] at hvC
    have hCv : fullComp Dm δ v = C := (fullComp_eq_of_mem Dm δ hvC).trans huCb
    have hclassv : classAt g Dm δ t v = C := by
      rw [classAt_eq_fullComp g Dm δ t hlow, hCv]
    refine ⟨⟨v, (show b - ε₀ g b ≤ g v by linarith [ε₀_pos g b]), hclassv⟩, ?_⟩
    intro hmem
    rw [← hclassv] at hmem
    obtain ⟨i, himem, hiL⟩ :=
      (meets_iff g Dm δ t (b + ε₀ g b) (show t ≤ b + ε₀ g b by linarith [ε₀_pos g b])
        (y := v)).mp hmem
    have hiC : i ∈ C := by rw [← hclassv]; exact himem
    have : (g i : ℝ) ≤ b := hmaxg.2 i hiC
    have : (b:ℝ) + ε₀ g b ≤ g i := hiL
    linarith [ε₀_pos g b]

lemma witness_encard {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (b t : ℝ) (ht : t ≤ b - ε₀ g b) (hlow : ∀ a : Fin n, L g t a) :
    (imgAt g Dm δ (b - ε₀ g b) t).encard - (imgAt g Dm δ (b + ε₀ g b) t).encard
      = V_imm g Dm δ b := by
  rw [diff_encard g Dm δ b (ε₀ g b) t (ε₀_pos g b),
    witness_set_eq g Dm δ b t ht hlow]
  rfl

/-! ### Evaluation of `mult` at the immortal point -/

lemma mult_bot_eq {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (b : ℝ) :
    mult (ripsRank Dm g δ) ((b : EReal), ⊥) =
      ⨅ (ε : ℝ) (_ : 0 < ε), ⨅ (t : ℝ) (_ : t ≤ b - ε),
        (imgAt g Dm δ (b - ε) t).encard - (imgAt g Dm δ (b + ε) t).encard := by
  have hb' := EReal.coe_ne_bot b
  have ht' := EReal.coe_ne_top b
  have htr : ((b : EReal)).toReal = b := EReal.toReal_coe b
  simp only [mult, Prod.fst, Prod.snd]
  split_ifs with h1
  · simp only [htr, ripsRank_eq]
  · exact absurd ⟨hb', ht'⟩ h1

lemma mult_eq_V {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (b : ℝ) :
    mult (ripsRank Dm g δ) ((b : EReal), ⊥) = V_imm g Dm δ b := by
  obtain ⟨t, ht, hlow⟩ := exists_low g b
  rw [mult_bot_eq g Dm δ b]
  refine le_antisymm ?_ ?_
  · have hw := witness_encard g Dm δ b t ht hlow
    refine iInf_le_of_le (ε₀ g b)
      (iInf_le_of_le (ε₀_pos g b)
        (iInf_le_of_le t (iInf_le_of_le ht ?_)))
    rw [hw]
  · refine le_iInf fun ε => le_iInf fun hε => le_iInf fun t' => le_iInf fun ht' => ?_
    rw [diff_encard g Dm δ b ε t' hε]
    exact lower_bound g Dm δ b ε t' hε ht'

end AlgImmortal

/-!
## The sweep side
-/

namespace AlgBc

open AlgImmortal

/-! ### `firstProcessed` facts -/

lemma firstProcessed_mem {n : ℕ} (σ : Fin n ≃ Fin n) (S : Finset (Fin n)) (hS : S.Nonempty)
    (i₀ : Fin n) : firstProcessed σ S i₀ ∈ S := by
    rw [firstProcessed, dif_pos hS]
    obtain ⟨y, hyS, hy⟩ := Finset.mem_image.mp (Finset.max'_mem _ (hS.image σ.symm))
    rw [← hy, Equiv.apply_symm_apply]
    exact hyS

lemma firstProcessed_max {n : ℕ} (σ : Fin n ≃ Fin n) (S : Finset (Fin n)) (hS : S.Nonempty)
    (i₀ : Fin n) (q : Fin n) (hq : q ∈ S) :
    σ.symm q ≤ σ.symm (firstProcessed σ S i₀) := by
  have hmemq : σ.symm q ∈ S.image σ.symm := Finset.mem_image.mpr ⟨q, hq, rfl⟩
  have hcongr : (S.image σ.symm).max' (hS.image σ.symm) = (S.image σ.symm).max' ⟨σ.symm q, hmemq⟩ :=
    congrArg (Finset.max' (S.image σ.symm)) (Subsingleton.elim _ _)
  rw [firstProcessed, dif_pos hS, Equiv.symm_apply_apply, hcongr]
  exact Finset.le_max' (S.image σ.symm) (σ.symm q) hmemq

lemma g_le_of_symm_le {n : ℕ} (g : Fin n → ℝ) (σ : Fin n ≃ Fin n)
    (hσ : IsSortOrder g σ) {x y : Fin n} (h : σ.symm x ≤ σ.symm y) : g x ≤ g y := by
  have hm := hσ h
  rw [Function.comp] at hm
  rw [← Equiv.apply_symm_apply σ x, ← Equiv.apply_symm_apply σ y]
  exact hm

/-! ### Labels -/

noncomputable def roots {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) : Fin n → Option (Fin n) := (barRun g Dm δ σ).1

/-! ### `acc` at an immortal point is zero -/

lemma accZero_step {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (σ : Fin n ≃ Fin n)
    (st : UFState n × ((EReal × EReal) → ℕ∞)) (i : Fin n) (b : ℝ) :
    (barStep g Dm δ σ st i).2 ((b : EReal), ⊥) = st.2 ((b : EReal), ⊥) := by
  simp only [barStep]
  split_ifs with hS
  · rfl
  · simp only [Prod.snd]
    rw [Finset.sum_eq_zero (fun r _ => if_neg (fun h9 => by
        have h2 : (⊥ : EReal) = (g i : EReal) := (Prod.ext_iff.mp h9).2
        exact (EReal.coe_ne_bot (g i : ℝ)) h2.symm)), add_zero]

lemma accZero_run {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (σ : Fin n ≃ Fin n)
    (b : ℝ) : (barRun g Dm δ σ).2 ((b : EReal), ⊥) = 0 := by
  have h : ∀ (l : List (Fin n)) (st : UFState n × ((EReal × EReal) → ℕ∞)),
      st.2 ((b : EReal), ⊥) = 0 →
      (l.foldl (fun st k => barStep g Dm δ σ st (σ k)) st).2 ((b : EReal), ⊥) = 0 := by
    intro l
    induction l with
    | nil => intro st hst; simpa using hst
    | cons k ks ih =>
      intro st hst
      simp only [List.foldl_cons]
      exact ih _ (by rw [accZero_step]; exact hst)
  simp only [barRun]
  exact h _ _ rfl

/-! ### The sweep invariant -/

def SweepInv {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (σ : Fin n ≃ Fin n)
    (lab : UFState n) (P : Set (Fin n)) : Prop :=
  (∀ v, (lab v).isSome ↔ v ∈ P) ∧
  (∀ v r, lab v = some r → lab r = some r) ∧
  (∀ v r, lab v = some r → σ.symm r ≥ σ.symm v) ∧
  (∀ u v, (ripsGraph Dm δ).Adj u v → lab u = lab v ∨ ¬(lab u).isSome ∨ ¬(lab v).isSome) ∧
  (∀ v r, lab v = some r → fullConn Dm δ r v)

lemma init_inv {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (σ : Fin n ≃ Fin n) :
    SweepInv g Dm δ σ (fun _ => none) (∅ : Set (Fin n)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v; simp
  · intro v r h; exact absurd h (by simp)
  · intro v r h; exact absurd h (by simp)
  · intro u v _; exact Or.inr (Or.inl (by simp))
  · intro v r h; exact absurd h (by simp)

-- helper to extract the `S`-neighbour condition
lemma barStep_S_mem {n : ℕ} (lab : UFState n) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (i j : Fin n)
    (hj : j ∈ Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome)) :
    j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome := (Finset.mem_filter.mp hj).2

lemma graphAdj_iff {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (i j : Fin n) :
    (ripsGraph Dm δ).Adj i j ↔ i ≠ j ∧ (Dm i j ≤ δ ∨ Dm j i ≤ δ) := by
  simp [ripsGraph, SimpleGraph.fromRel]

lemma graphAdj_of_dm {n : ℕ} (Dm : Fin n → Fin n → ℝ) (hDm : ∀ i j, Dm i j = Dm j i) (δ : ℝ)
    (a b : Fin n) (hne : a ≠ b) (h : Dm a b ≤ δ) : (ripsGraph Dm δ).Adj a b := by
  rw [graphAdj_iff Dm δ]
  exact ⟨hne, Or.inl h⟩

lemma fullConn_single {n : ℕ} (Dm : Fin n → Fin n → ℝ) (δ : ℝ) {a b : Fin n}
    (h : (ripsGraph Dm δ).Adj a b) : fullConn Dm δ a b :=
  Relation.ReflTransGen.single h

lemma root_getD {n : ℕ} (lab : UFState n) (hptr : ∀ v r, lab v = some r → lab r = some r)
    (j r : Fin n) (hr : lab j = some r) :
    (lab j).getD j = r ∧ lab ((lab j).getD j) = some ((lab j).getD j) := by
  rw [hr]
  refine ⟨rfl, ?_⟩
  simpa only [Option.getD_some] using hptr j r hr

lemma barStep_inv {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i)
    (σ : Fin n ≃ Fin n) (st : UFState n × ((EReal × EReal) → ℕ∞)) (P : Set (Fin n)) (i : Fin n)
    (hinv : SweepInv g Dm δ σ st.1 P) (hiP : i ∉ P)
    (horder : ∀ v ∈ P, σ.symm i ≤ σ.symm v) :
    SweepInv g Dm δ σ (barStep g Dm δ σ st i).1 (insert i P) := by
  obtain ⟨hmem, hptr, helder, hedge, hcomp⟩ := hinv
  rw [barStep]
  set Sf : Finset (Fin n) :=
    Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (st.1 j).isSome) with hSf
  by_cases hS : Sf = ∅
  · -- Sf = ∅
    rw [if_pos hS]; simp only [Prod.fst]
    constructor
    · intro v
      rw [Function.update_apply]
      by_cases hv : v = i
      · rw [if_pos hv, hv]
        simp [hv, Set.mem_insert_iff]
      · rw [if_neg hv]
        rw [hmem v]
        simp [hv, Set.mem_insert_iff]
    constructor
    · intro v r hv
      rw [Function.update_apply] at hv
      by_cases hv' : v = i
      · rw [if_pos hv'] at hv
        injection hv with he
        rw [← he]
        rw [Function.update_apply, if_pos rfl]
      · rw [if_neg hv'] at hv
        rw [Function.update_apply]
        by_cases hr : r = i
        · rw [if_pos hr, ← hr]
        · rw [if_neg hr]
          exact hptr v r hv
    constructor
    · intro v r hv
      rw [Function.update_apply] at hv
      by_cases hv' : v = i
      · rw [if_pos hv'] at hv
        injection hv with he
        rw [hv', he]
      · rw [if_neg hv'] at hv
        exact helder v r hv
    constructor
    · intro u v huv
      rw [Function.update_apply, Function.update_apply]
      by_cases hu : u = i
      · rw [if_pos hu]
        by_cases hv : v = i
        · rw [if_pos hv]; exact Or.inl rfl
        · rw [if_neg hv]
          rw [hu] at huv
          have hvP : v ∉ P := by
            intro hvP
            have hvSf : v ∈ Sf := by
              rw [hSf, Finset.mem_filter]
              have hadj : Dm i v ≤ δ := by
                rcases (graphAdj_iff Dm δ i v).mp huv with ⟨_, h⟩
                rcases h with h | h
                · exact h
                · rw [hDm]; exact h
              exact ⟨Finset.mem_univ v, hv, hadj, (hmem v).mpr hvP⟩
            rw [hS] at hvSf
            exact (Finset.notMem_empty v) hvSf
          have hvn : st.1 v = none := by
            cases hh : st.1 v with
            | none => rfl
            | some r => exact absurd ((hmem v).mp (by simp [hh])) hvP
          right; right; simp [hvn]
      · by_cases hv : v = i
        · rw [if_neg hu, if_pos hv]
          rw [hv] at huv
          have huP : u ∉ P := by
            intro huP
            have huSf : u ∈ Sf := by
              rw [hSf, Finset.mem_filter]
              have hadj : Dm i u ≤ δ := by
                rcases (graphAdj_iff Dm δ u i).mp huv with ⟨_, h⟩
                rcases h with h | h
                · rw [hDm]; exact h
                · exact h
              exact ⟨Finset.mem_univ u, hu, hadj, (hmem u).mpr huP⟩
            rw [hS] at huSf
            exact (Finset.notMem_empty u) huSf
          have hun : st.1 u = none := by
            cases hh : st.1 u with
            | none => rfl
            | some r => exact absurd ((hmem u).mp (by simp [hh])) huP
          right; left; simp [hun]
        · rw [if_neg hu, if_neg hv]
          rcases hedge u v huv with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)

    · intro v r hv
      rw [Function.update_apply] at hv
      by_cases hv' : v = i
      · rw [if_pos hv'] at hv
        injection hv with he
        rw [hv', ← he]
      · rw [if_neg hv'] at hv
        exact hcomp v r hv
  · -- S ≠ ∅
    rw [if_neg hS]; simp only [Prod.fst]
    set root : Fin n → Fin n := fun j => (st.1 j).getD j with hroot
    set ri : Fin n := root (firstProcessed σ Sf i) with hri
    set M : Finset (Fin n) := insert ri (Sf.image root) with hM
    set R : Fin n := firstProcessed σ M ri with hR
    set lab2 : UFState n := fun v =>
      if v = i then some R
      else match st.1 v with
        | some r => if r ∈ M then some R else some r
        | none => none with hlab2
    change SweepInv g Dm δ σ lab2 (insert i P)
    have hSne : Sf.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    have hMne : M.Nonempty := ⟨ri, by rw [hM]; exact Finset.mem_insert_self _ _⟩
    have hRM : R ∈ M := by rw [hR]; exact firstProcessed_mem σ M hMne ri
    have hRmax : ∀ q ∈ M, σ.symm q ≤ σ.symm R := by
      intro q hq; rw [hR]; exact firstProcessed_max σ M hMne ri q hq
    -- membership characterisation of M and root
    have hroot_of : ∀ j, (st.1 j).isSome → root j = (st.1 j).getD j := fun j _ => rfl
    have hroot_mem_M : ∀ j ∈ Sf, root j ∈ M := by
      intro j hj; rw [hM]; exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
    have hroot_root : ∀ j, (st.1 j).isSome → st.1 (root j) = some (root j) := by
      intro j hj
      have hsome : ∃ r, st.1 j = some r := Option.isSome_iff_exists.mp hj
      obtain ⟨r, hr⟩ := hsome
      have : root j = r := by rw [hroot_of j hj, hr]; rfl
      rw [this]
      exact hptr j r hr
    have hroot_P : ∀ j ∈ Sf, root j ∈ P := by
      intro j hj
      have hj' := barStep_S_mem st.1 Dm δ i j hj
      have hsj : (st.1 j).isSome := hj'.2.2
      have := (hmem (root j)).mp (by rw [hroot_root j hsj]; rfl)
      exact this
    have hM_P : ∀ q ∈ M, q ∈ P := by
      intro q hq
      rw [hM] at hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · rw [hri]
        exact hroot_P _ (firstProcessed_mem σ Sf hSne i)
      · obtain ⟨j, hj, hjq⟩ := Finset.mem_image.mp hq
        rw [← hjq]; exact hroot_P j hj
    have hconn_i_M : ∀ q ∈ M, fullConn Dm δ q i := by
      intro q hq
      rw [hM] at hq
      rcases Finset.mem_insert.mp hq with hqi | hqg
      · -- q = ri = root of the first-processed neighbour of `i`
        have hj0 : firstProcessed σ Sf i ∈ Sf := firstProcessed_mem σ Sf hSne i
        obtain ⟨hjne, hdmj, hsj⟩ := barStep_S_mem st.1 Dm δ i _ hj0
        obtain ⟨r0, hr0lab⟩ := (Option.isSome_iff_exists.mp hsj)
        obtain ⟨hr0, hr1⟩ := root_getD st.1 hptr (firstProcessed σ Sf i) r0 hr0lab
        rw [hqi, hri, hroot_of (firstProcessed σ Sf i) hsj, hr0]
        exact Relation.ReflTransGen.trans (hcomp (firstProcessed σ Sf i) r0 hr0lab)
          (fullConn_single Dm δ (graphAdj_of_dm Dm hDm δ _ i hjne (hDm _ _ ▸ hdmj)))
      · obtain ⟨j, hj, hjq⟩ := Finset.mem_image.mp hqg
        obtain ⟨hjne, hdmj, hsj⟩ := barStep_S_mem st.1 Dm δ i j hj
        obtain ⟨r0, hr0lab⟩ := (Option.isSome_iff_exists.mp hsj)
        have hrootj : root j = r0 := by rw [hroot_of j hsj, hr0lab]; rfl
        have hlabj : st.1 j = some q := by
          rw [hr0lab, ← hjq, hrootj]
        rw [← hjq, hrootj]
        exact Relation.ReflTransGen.trans (hcomp j r0 hr0lab)
          (fullConn_single Dm δ (graphAdj_of_dm Dm hDm δ j i hjne (hDm j i ▸ hdmj)))
    have hrRob : R ≠ i := fun hh => hiP (hh ▸ hM_P R hRM)
    have hrootRootM : ∀ q ∈ M, st.1 q = some q := by
      intro q hq
      rw [hM] at hq
      rcases Finset.mem_insert.mp hq with hqi | hqg
      · rw [hqi, hri]
        obtain ⟨_, _, hsj⟩ := barStep_S_mem st.1 Dm δ i _
          (firstProcessed_mem σ Sf hSne i)
        exact hroot_root _ hsj
      · obtain ⟨j, hj, hjq⟩ := Finset.mem_image.mp hqg
        rw [← hjq]
        obtain ⟨_, _, hsj⟩ := barStep_S_mem st.1 Dm δ i j hj
        exact hroot_root j hsj
    have hlab2_i : lab2 i = some R := by rw [hlab2]; simp
    have hlab2_ne : ∀ v, v ≠ i → lab2 v =
        (match st.1 v with | some r => if r ∈ M then some R else some r | none => none) := by
      intro v hv; rw [hlab2]; simp [hv]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro v
      by_cases hv : v = i
      · rw [hv, hlab2_i]; simp [hiP]
      · cases h : st.1 v with
        | none =>
          rw [hlab2_ne v hv, h]
          have hnp : v ∉ P := by
            intro hvp
            have hs1 := (hmem v).mpr hvp
            rw [h] at hs1
            simp at hs1
          simp [hv, Set.mem_insert_iff, hnp]
        | some r0 =>
          have hvp : v ∈ P := (hmem v).mp (by simp [h])
          have hl2 : lab2 v = (if r0 ∈ M then some R else some r0) := by simp [hlab2_ne v hv, h]
          by_cases hr : r0 ∈ M
          · rw [hl2, if_pos hr]
            simp only [Option.isSome_some, true_iff]
            simp [Set.mem_insert_iff, hM_P r0 hr, hvp]
          · rw [hl2, if_neg hr]
            simp only [Option.isSome_some, true_iff]
            simp [Set.mem_insert_iff, hvp]
    · intro v r hv
      by_cases hv' : v = i
      · rw [hv'] at hv; rw [hlab2_i] at hv
        injection hv with hvR
        rw [← hvR]
        have hl2R : lab2 R = (if R ∈ M then some R else some R) := by
          rw [hlab2_ne R hrRob, hrootRootM R hRM]
        rw [hl2R]; simp [hRM]
      · cases h : st.1 v with
        | none => simp [hlab2_ne v hv', h] at hv
        | some r0 =>
          have hl2 : lab2 v = (if r0 ∈ M then some R else some r0) := by simp [hlab2_ne v hv', h]
          by_cases hr : r0 ∈ M
          · rw [hl2, if_pos hr] at hv
            injection hv with hvR
            rw [← hvR]
            have hl2R : lab2 R = (if R ∈ M then some R else some R) := by
              rw [hlab2_ne R hrRob, hrootRootM R hRM]
            rw [hl2R]
            simp [hRM]
          · rw [hl2, if_neg hr] at hv
            injection hv with hvR
            have hr0is : (st.1 r0).isSome = true := by rw [hptr v r0 h, Option.isSome_some]
            have hr0ne : r0 ≠ i := by
              intro hh; rw [hh] at hr0is; exact hiP ((hmem i).mp hr0is)
            rw [← hvR, hlab2_ne r0 hr0ne, hptr v r0 h]
            simp [hr]
    · intro v r hv
      by_cases hv' : v = i
      · rw [hv'] at hv; rw [hlab2_i] at hv
        injection hv with hvR
        rw [← hvR, hv']; exact horder R (hM_P R hRM)
      · cases h : st.1 v with
        | none => simp [hlab2_ne v hv', h] at hv
        | some r0 =>
          have hl2 : lab2 v = (if r0 ∈ M then some R else some r0) := by simp [hlab2_ne v hv', h]
          by_cases hr : r0 ∈ M
          · rw [hl2, if_pos hr] at hv
            injection hv with hvR
            rw [← hvR]
            exact le_trans (helder v r0 h) (hRmax r0 hr)
          · rw [hl2, if_neg hr] at hv
            injection hv with hvR
            rw [← hvR]; exact helder v r0 h
    · intro u v huv
      by_cases hu : u = i
      · rw [hu] at huv; rw [hu]
        by_cases hv : v = i
        · rw [hv, hlab2_i]; exact Or.inl rfl
        · by_cases hvP : v ∈ P
          · have hs : (st.1 v).isSome = true := (hmem v).mpr hvP
            obtain ⟨r0, hr0⟩ := (Option.isSome_iff_exists.mp hs)
            have hrootv : root v = r0 := by rw [hroot_of v hs, hr0]; rfl
            have hvSf : v ∈ Sf := by
              rw [hSf, Finset.mem_filter]
              have hdj : Dm i v ≤ δ := by
                rcases (graphAdj_iff Dm δ i v).mp huv with ⟨_, h⟩
                rcases h with h | h
                · exact h
                · rw [hDm]; exact h
              exact ⟨Finset.mem_univ v, hv, hdj, hs⟩
            have hce : st.1 v = some (root v) := by rw [hrootv]; exact hr0
            have hl2 : lab2 v = (if root v ∈ M then some R else some (root v)) := by
              simp [hlab2_ne v hv, hce]
            have hvR : lab2 v = some R := by
              rw [hl2, if_pos (hroot_mem_M v hvSf)]
            rw [hlab2_i, hvR]; exact Or.inl rfl
          · have hvn : st.1 v = none := by
              cases hh : st.1 v with
              | none => rfl
              | some r => exact absurd ((hmem v).mp (by simp [hh])) hvP
            rw [hlab2_i, hlab2_ne v hv, hvn]
            exact Or.inr (Or.inr (by simp))
      · by_cases hv : v = i
        · rw [hv] at huv; rw [hv]
          by_cases huP : u ∈ P
          · have hs : (st.1 u).isSome = true := (hmem u).mpr huP
            obtain ⟨r0, hr0⟩ := (Option.isSome_iff_exists.mp hs)
            have hrootu : root u = r0 := by rw [hroot_of u hs, hr0]; rfl
            have huSf : u ∈ Sf := by
              rw [hSf, Finset.mem_filter]
              have hdj : Dm i u ≤ δ := by
                rcases (graphAdj_iff Dm δ u i).mp huv with ⟨_, h⟩
                rcases h with h | h
                · rw [hDm]; exact h
                · exact h
              exact ⟨Finset.mem_univ u, hu, hdj, hs⟩
            have hce : st.1 u = some (root u) := by rw [hrootu]; exact hr0
            have hl2 : lab2 u = (if root u ∈ M then some R else some (root u)) := by
              simp [hlab2_ne u hu, hce]
            have huR : lab2 u = some R := by
              rw [hl2, if_pos (hroot_mem_M u huSf)]
            rw [huR, hlab2_i]; exact Or.inl rfl
          · have hun : st.1 u = none := by
              cases hh : st.1 u with
              | none => rfl
              | some r => exact absurd ((hmem u).mp (by simp [hh])) huP
            rw [hlab2_ne u hu, hun, hlab2_i]
            exact Or.inr (Or.inl (by simp))
        · have hisSome_lab2 : ∀ w : Fin n, w ≠ i →
              ((lab2 w).isSome = true ↔ (st.1 w).isSome = true) := by
            intro w hw; rw [hlab2_ne w hw]
            cases h : st.1 w with
            | none => simp [h]
            | some r => by_cases hr : r ∈ M <;> simp [hr, Option.isSome_some]
          rcases hedge u v huv with h | h | h
          · exact Or.inl (by rw [hlab2_ne u hu, hlab2_ne v hv, h])
          · exact Or.inr (Or.inl (fun h2 => h ((hisSome_lab2 u hu).mp h2)))
          · exact Or.inr (Or.inr (fun h2 => h ((hisSome_lab2 v hv).mp h2)))
    · intro v r hv
      by_cases hv' : v = i
      · rw [hv'] at hv; rw [hlab2_i] at hv
        injection hv with hvR
        rw [hv', ← hvR]; exact hconn_i_M R hRM
      · cases h : st.1 v with
        | none => simp [hlab2_ne v hv', h] at hv
        | some r0 =>
          have hl2 : lab2 v = (if r0 ∈ M then some R else some r0) := by simp [hlab2_ne v hv', h]
          by_cases hr : r0 ∈ M
          · rw [hl2, if_pos hr] at hv
            injection hv with hvR
            rw [← hvR]
            exact Relation.ReflTransGen.trans (hconn_i_M R hRM)
              (Relation.ReflTransGen.trans (fullConn_symm Dm δ (hconn_i_M r0 hr))
                (hcomp v r0 h))
          · rw [hl2, if_neg hr] at hv
            injection hv with hvR
            rw [← hvR]; exact hcomp v r0 h


/-! ### Fold over the sweep order -/

lemma finRange_pairwise_gt (n : ℕ) :
    (List.finRange n).Pairwise (fun a b : Fin n => (a : ℕ) < (b : ℕ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ_last, List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Pairwise.map Fin.castSucc (fun a b h => h) ih
    · simp
    · intro a ha b hb
      simp only [List.mem_singleton] at hb
      rw [hb]
      obtain ⟨a', _, rfl⟩ := List.mem_map.mp ha
      exact Fin.castSucc_lt_last a'

lemma sweep_fold {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (σ : Fin n ≃ Fin n) (l : List (Fin n))
    (hdec : l.Pairwise (fun a b : Fin n => (σ.symm a : Fin n) > σ.symm b))
    (st : UFState n × ((EReal × EReal) → ℕ∞)) (P0 : Set (Fin n))
    (h0 : SweepInv g Dm δ σ st.1 P0)
    (hPa : ∀ a ∈ P0, ∀ b ∈ l, (σ.symm a : Fin n) > σ.symm b) :
    SweepInv g Dm δ σ (l.foldl (fun st i => barStep g Dm δ σ st i) st).1
      (P0 ∪ (l.toFinset : Set (Fin n))) := by
  induction l generalizing st P0 with
  | nil => simpa using h0
  | cons i rest ih =>
    obtain ⟨hhead, hrest⟩ := List.pairwise_cons.mp hdec
    have hset : P0 ∪ (↑(i :: rest).toFinset : Set (Fin n))
        = insert i P0 ∪ (↑rest.toFinset : Set (Fin n)) := by
      simp [List.toFinset_cons, Set.union_insert, Set.insert_union]
    rw [List.foldl_cons, hset]
    have hiP : i ∉ P0 := by
      intro hi
      exact absurd (hPa i hi i (by simp)) (lt_irrefl _)
    refine ih hrest (barStep g Dm δ σ st i) (insert i P0)
      (barStep_inv g Dm δ hDm σ st P0 i h0 hiP
        (fun v hv => le_of_lt (hPa v hv i (by simp)))) ?_
    intro a ha b hb
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact hhead b hb
    · exact lt_trans (hhead b hb) (hPa a ha i (by simp))


lemma sweep_order_pairwise {n : ℕ} (σ : Fin n ≃ Fin n) :
    (((List.finRange n).reverse).map σ).Pairwise
      (fun a b : Fin n => (σ.symm a : Fin n) > σ.symm b) := by
  rw [List.pairwise_map]
  simp only [Equiv.symm_apply_apply]
  rw [List.finRange_reverse, List.pairwise_map]
  refine (finRange_pairwise_gt n).imp (fun {a b} h => ?_)
  show Fin.rev a > Fin.rev b
  exact Fin.rev_lt_rev.mpr h

lemma barRun_inv {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (σ : Fin n ≃ Fin n) :
    SweepInv g Dm δ σ (barRun g Dm δ σ).1 Set.univ := by
  set L : List (Fin n) := ((List.finRange n).reverse.map σ) with hL
  have hdec : L.Pairwise (fun a b : Fin n => (σ.symm a : Fin n) > σ.symm b) := by
    rw [hL]; exact sweep_order_pairwise σ
  have hf : (barRun g Dm δ σ).1
      = (L.foldl (fun st i => barStep g Dm δ σ st i) ((fun _ => none), (fun _ => 0))).1 := by
    rw [hL, barRun, List.foldl_map]
  rw [hf]
  have hinv := sweep_fold g Dm δ hDm σ L hdec ((fun _ => none), (fun _ => 0)) ∅
    (init_inv g Dm δ σ) (by simp)
  have hset : (∅ : Set (Fin n)) ∪ (L.toFinset : Set (Fin n)) = Set.univ := by
    rw [Set.empty_union]
    ext v
    simp only [Set.mem_univ, iff_true, Finset.mem_coe, List.mem_toFinset]
    rw [hL, List.mem_map]
    exact ⟨σ.symm v, List.mem_reverse.mpr (List.mem_finRange _), Equiv.apply_symm_apply _ _⟩
  rwa [hset] at hinv


/-! ### The final invariant gives labels constant on components -/

lemma lab_constant {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (lab : UFState n) (hinv : SweepInv g Dm δ σ lab Set.univ)
    {u v : Fin n} (h : fullConn Dm δ u v) : lab u = lab v := by
  have hsome : ∀ w, (lab w).isSome = true := fun w => (hinv.1 w).mpr (Set.mem_univ w)
  induction h with
  | refl => rfl
  | tail hprev hstep ih =>
    rcases hinv.2.2.2.1 _ _ hstep with h | h | h
    · rw [← h, ih]
    · exact absurd (hsome _) h
    · exact absurd (hsome _) h

lemma lab_elder {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) (lab : UFState n)
    (hinv : SweepInv g Dm δ σ lab Set.univ) {v r : Fin n} (hv : lab v = some r) :
    g v ≤ g r :=
  g_le_of_symm_le g σ hσ (hinv.2.2.1 v r hv)

/-- Pick the surviving root of a full-graph component. -/
noncomputable def compRoot {n : ℕ} (hn : 0 < n) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (lab : UFState n) (C : Set (Fin n)) : Fin n :=
  if h : ∃ u, fullComp Dm δ u = C then
    (lab (Classical.choose h)).getD (Classical.choose h)
  else ⟨0, hn⟩

lemma encard_roots_eq_V {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ)
    (lab : UFState n) (hinv : SweepInv g Dm δ σ lab Set.univ) (hn : 0 < n) (b : ℝ) :
    ({r : Fin n | lab r = some r ∧ g r = b} : Set (Fin n)).encard = V_imm g Dm δ b := by
  have hsome : ∀ w, (lab w).isSome = true := fun w => (hinv.1 w).mpr (Set.mem_univ w)
  have hconst : ∀ {u v : Fin n}, fullConn Dm δ u v → lab u = lab v := lab_constant g Dm δ σ lab hinv
  have hgle : ∀ {v r : Fin n}, lab v = some r → g v ≤ g r := lab_elder g Dm δ σ hσ lab hinv
  -- injection R → V
  have h1 : ({r : Fin n | lab r = some r ∧ g r = b} : Set (Fin n)).encard
      ≤ ({C ∈ fullComps Dm δ | maxgIs g b C} : Set (Set (Fin n))).encard := by
    refine Set.encard_le_encard_of_injOn (f := fun r => fullComp Dm δ r) ?_ ?_
    · intro r hr
      obtain ⟨hrr, hrb⟩ := hr
      refine ⟨⟨r, Set.mem_univ r, rfl⟩, ⟨⟨r, fullConn_refl Dm δ r, hrb⟩, ?_⟩⟩
      intro j hj
      have hjr : fullConn Dm δ r j := hj
      have hlabj : lab j = some r := by rw [← hconst hjr]; exact hrr
      have := hgle hlabj
      rwa [hrb] at this
    · intro r₁ hr₁ r₂ hr₂ heq
      obtain ⟨hrr₁, -⟩ := hr₁
      obtain ⟨hrr₂, -⟩ := hr₂
      have heq' : fullComp Dm δ r₁ = fullComp Dm δ r₂ := heq
      have hr₂mem : r₂ ∈ fullComp Dm δ r₁ := by rw [heq']; exact fullConn_refl Dm δ r₂
      have hlab : lab r₁ = lab r₂ := hconst hr₂mem
      rw [hrr₁, hrr₂] at hlab
      exact Option.some.inj hlab
  -- injection V → R
  have h2 : ({C ∈ fullComps Dm δ | maxgIs g b C} : Set (Set (Fin n))).encard
      ≤ ({r : Fin n | lab r = some r ∧ g r = b} : Set (Fin n)).encard := by
    refine Set.encard_le_encard_of_injOn (f := compRoot hn Dm δ lab) ?_ ?_
    · intro C hC
      obtain ⟨hCcomps, hCmax⟩ := hC
      obtain ⟨u, -, hu⟩ := hCcomps
      have hex : ∃ u, fullComp Dm δ u = C := ⟨u, hu⟩
      set u0 := Classical.choose hex with hu0
      have hu0c : fullComp Dm δ u0 = C := Classical.choose_spec hex
      have hroot : compRoot hn Dm δ lab C = (lab u0).getD u0 := by
        rw [compRoot, dif_pos hex]
      have hsomeu : ∃ r, lab u0 = some r := Option.isSome_iff_exists.mp (hsome u0)
      obtain ⟨r0, hr0⟩ := hsomeu
      have hget : (lab u0).getD u0 = r0 := by rw [hr0]; rfl
      have hptr0 : lab r0 = some r0 := hinv.2.1 u0 r0 hr0
      have hr0memC : r0 ∈ fullComp Dm δ u0 := fullConn_symm Dm δ (hinv.2.2.2.2 u0 r0 hr0)
      have hCeq : fullComp Dm δ r0 = C := (fullComp_eq_of_mem Dm δ hr0memC).trans hu0c
      have hgr0b : g r0 = b := by
        refine le_antisymm (hCmax.2 r0 (hu0c ▸ hr0memC)) ?_
        obtain ⟨v, hvC, hvb⟩ := hCmax.1
        have hCeq' : fullComp Dm δ r0 = C := hCeq
        have hvr : v ∈ fullComp Dm δ r0 := by rw [hCeq']; exact hvC
        have hlabv : lab v = some r0 := by rw [← hconst hvr]; exact hptr0
        have := hgle hlabv
        rwa [hvb] at this
      rw [hroot, hget]
      exact ⟨hptr0, hgr0b⟩
    · intro C₁ hC₁ C₂ hC₂ heq
      obtain ⟨hC₁c, -⟩ := hC₁
      obtain ⟨hC₂c, -⟩ := hC₂
      obtain ⟨u₁, -, hu₁⟩ := hC₁c
      obtain ⟨u₂, -, hu₂⟩ := hC₂c
      have hspec : ∀ (C : Set (Fin n)) (u : Fin n), fullComp Dm δ u = C →
          fullComp Dm δ (compRoot hn Dm δ lab C) = C := by
        intro C u hu
        have hex : ∃ u, fullComp Dm δ u = C := ⟨u, hu⟩
        have hch : fullComp Dm δ (Classical.choose hex) = C := Classical.choose_spec hex
        have hroot : compRoot hn Dm δ lab C = (lab (Classical.choose hex)).getD (Classical.choose hex) := by
          rw [compRoot, dif_pos hex]
        obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.mp (hsome (Classical.choose hex))
        have hget : (lab (Classical.choose hex)).getD (Classical.choose hex) = r0 := by rw [hr0]; rfl
        have hr0mem : r0 ∈ fullComp Dm δ (Classical.choose hex) :=
          fullConn_symm Dm δ (hinv.2.2.2.2 _ r0 hr0)
        rw [hroot, hget]
        exact (fullComp_eq_of_mem Dm δ hr0mem).trans hch
      rw [← hspec C₁ u₁ hu₁, heq, hspec C₂ u₂ hu₂]
  exact le_antisymm h1 h2


lemma sum_indicator_card {n : ℕ} (s : Finset (Fin n)) (P : Fin n → Prop) [DecidablePred P] :
    s.sum (fun r => if P r then (1 : ℕ∞) else 0) = ((s.filter P).card : ℕ∞) := by
  rw [Finset.sum_ite]
  rw [Finset.sum_const, Finset.sum_const]
  simp [nsmul_eq_mul]

lemma barcode_bot_eq_V {n : ℕ} (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) (b : ℝ) :
    ripsBarcode g Dm δ σ ((b : EReal), ⊥) = AlgImmortal.V_imm g Dm δ b := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    have hu0 : (Set.univ : Set (Fin 0)) = ∅ := by
      ext x; exact x.elim0
    have hV0 : AlgImmortal.V_imm g Dm δ b = 0 := by
      unfold AlgImmortal.V_imm AlgImmortal.fullComps
      rw [hu0, Set.image_empty, Set.sep_empty]
      exact Set.encard_empty
    have hB0 : ripsBarcode g Dm δ σ ((b : EReal), ⊥) = 0 := by
      simp only [ripsBarcode, barRun, List.finRange_zero, List.reverse_nil, List.foldl_nil]
      rw [Finset.univ_eq_empty]
      simp
    rw [hV0, hB0]
  · have hacc := accZero_run g Dm δ σ b
    have hinv := barRun_inv g Dm δ hDm σ
    have hroots := encard_roots_eq_V g Dm δ hDm σ hσ (barRun g Dm δ σ).1 hinv hn b
    have hcoeeq : ∀ r : Fin n, (((b : EReal), (⊥ : EReal)) = ((g r : EReal), (⊥ : EReal))) ↔ g r = b := by
      intro r
      constructor
      · intro h; exact (EReal.coe_injective (Prod.ext_iff.mp h).1).symm
      · intro h; rw [h]
    have hsum : (Finset.univ.filter (fun r => (barRun g Dm δ σ).1 r = some r)).sum
        (fun r => if ((b : EReal), (⊥ : EReal)) = ((g r : EReal), (⊥ : EReal)) then (1 : ℕ∞) else 0)
        = ((Finset.univ.filter (fun r => (barRun g Dm δ σ).1 r = some r ∧ g r = b)).card : ℕ∞) := by
      rw [Finset.sum_congr rfl (fun r _ => by rw [if_congr (hcoeeq r) rfl rfl])]
      have hff : (Finset.univ.filter (fun r => (barRun g Dm δ σ).1 r = some r)).filter
          (fun r => g r = b)
          = Finset.univ.filter (fun r => (barRun g Dm δ σ).1 r = some r ∧ g r = b) := by
        ext r; simp [and_assoc]
      rw [sum_indicator_card (Finset.univ.filter (fun r => (barRun g Dm δ σ).1 r = some r))
        (fun r => g r = b), hff]
    have hset : ({r : Fin n | (barRun g Dm δ σ).1 r = some r ∧ g r = b} : Set (Fin n)).toFinset
        = Finset.univ.filter (fun r => (barRun g Dm δ σ).1 r = some r ∧ g r = b) := by
      ext r; simp [Set.mem_toFinset]
    have henc : ({r : Fin n | (barRun g Dm δ σ).1 r = some r ∧ g r = b} : Set (Fin n)).encard
        = ((Finset.univ.filter (fun r => (barRun g Dm δ σ).1 r = some r ∧ g r = b)).card : ℕ∞) := by
      rw [Set.encard_eq_coe_toFinset_card, hset]
    simp only [ripsBarcode, hacc, zero_add]
    rw [hsum, ← henc, hroots]

end AlgBc

theorem solution
    (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (δ : ℝ) (σ : Fin n ≃ Fin n)
    (hσ : IsSortOrder g σ) (b : ℝ) :
    ripsDiagram Dm g δ ((b : EReal), ⊥) = ripsBarcode g Dm δ σ ((b : EReal), ⊥) := by
  have hL : ripsDiagram Dm g δ ((b : EReal), ⊥) = AlgImmortal.V_imm g Dm δ b :=
    AlgImmortal.mult_eq_V g Dm δ b
  have hR : ripsBarcode g Dm δ σ ((b : EReal), ⊥) = AlgImmortal.V_imm g Dm δ b :=
    AlgBc.barcode_bot_eq_V g Dm δ hDm σ hσ b
  rw [hL, hR]





