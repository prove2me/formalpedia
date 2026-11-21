-- Prove2me | solution 1 for OnlineColoringKYY.Supplement.theorem_6_26
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T17:31:10.63474+00:00
-- url     : https://prove2.me/submissions/2ec04f09-5920-4ad5-8691-d4b9a6df69bd

import Mathlib
import Definitions.Def_OnlineColoringKYY_Supplement_cliqueFree
import Definitions.Def_OnlineColoringKYY_prefixGraph
import Definitions.Def_OnlineColoringKYY_Supplement_Common
import Definitions.Def_OnlineColoringKYY_Supplement_locAlg

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626
open Classical OnlineColoringKYY.Supplement
/-!
Blueprint layer 1 for Theorem 6.26 (q414): Lemma 6.3 (online object coloring), Lemma 6.4
(CliqueFree(r), for partial runs) and Corollary 6.5 (one bin of at most `L` vertices, run through
`c65Step`, uses at most `L/M` colors when `n_{M+1} ≤ L`).
-/
/-- Run Algorithm 3 on a list of arrivals, each a selection rule and a set. -/
noncomputable def objRun (μ : ℝ) :
    List (Finset (Finset ℕ)) → List ((Finset ℕ → ℕ) × Finset (Finset ℕ)) →
      List (Finset (Finset ℕ)) × List ℕ
  | X, [] => (X, [])
  | X, a :: as =>
    let r := objStep μ a.1 X a.2
    let r2 := objRun μ r.1 as
    (r2.1, r.2 :: r2.2)

/-- Run `cfStep` (Algorithm 4) on a list of arriving vertices; `Adjf v` is the adjacency seen at the
arrival of `v`. -/
noncomputable def cfRun (A : ℕ) (R : Resolver) (Adjf : ℕ → ℕ → ℕ → Prop) (r : ℕ) (addr : List ℕ) :
    List ℕ → CFState → CFState × List Color
  | [], s => (s, [])
  | v :: vs, s =>
    let x := cfStep A R (Adjf v) v r addr s
    let y := cfRun A R Adjf r addr vs x.1
    (y.1, x.2 :: y.2)

/-- Run `c65Step` (Corollary 6.5's algorithm) on a list of arriving vertices. -/
noncomputable def c65Run (A : ℕ) (R : Resolver) (Adjf : ℕ → ℕ → ℕ → Prop) (addr : List ℕ) :
    List ℕ → ℕ × CFState → (ℕ × CFState) × List Color
  | [], s => (s, [])
  | v :: vs, s =>
    let x := c65Step A R (Adjf v) v addr s
    let y := c65Run A R Adjf addr vs x.1
    (y.1, x.2 :: y.2)

/-- The time-varying adjacency agrees with the fixed symmetric `Adj` on the vertices arrived so far
(including the arriving one). -/
def Consistent (Adjf : ℕ → ℕ → ℕ → Prop) (Adj : ℕ → ℕ → Prop) (vs : List ℕ) : Prop :=
  ∀ i (hi : i < vs.length), ∀ a ∈ vs.take (i + 1), ∀ b ∈ vs.take (i + 1),
    (Adjf (vs.get ⟨i, hi⟩) a b ↔ Adj a b)

end OnlineColoringKYY.Supplement.Dev.T626
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartOC
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
/-! ## Lemma 6.3: online object coloring -/
lemma mem_foldr_union (X : List (Finset (Finset ℕ))) (x : Finset ℕ) :
    x ∈ X.foldr (· ∪ ·) ∅ ↔ ∃ Y ∈ X, x ∈ Y := by
  induction X with
  | nil => simp
  | cons Y X ih => simp [ih]

lemma getD_set_eq (X : List (Finset (Finset ℕ))) (i j : ℕ) (y : Finset (Finset ℕ))
    (hi : i < X.length) :
    (X.set i y).getD j ∅ = if j = i then y else X.getD j ∅ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : j = i
  · subst h; simp [hi]
  · rw [if_neg (Ne.symm h), if_neg h]

lemma getD_append_single (X : List (Finset (Finset ℕ))) (B : Finset (Finset ℕ)) (j : ℕ) :
    (X ++ [B]).getD j ∅ =
      if j < X.length then X.getD j ∅ else if j = X.length then B else ∅ := by
  split_ifs with h1 h2
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h1, ← List.getD_eq_getElem?_getD]
  · subst h2; simp [List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      List.getElem?_eq_none (by simp; omega)]
    rfl

lemma foldr_eq_biUnion (X : List (Finset (Finset ℕ))) :
    X.foldr (· ∪ ·) ∅ = (Finset.range X.length).biUnion (fun i => X.getD i ∅) := by
  ext x
  rw [mem_foldr_union]
  simp only [Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨Y, hY, hx⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hY
    exact ⟨i, hi, by simpa [List.getD_eq_getElem?_getD, hi] using hx⟩
  · rintro ⟨i, hi, hx⟩
    exact ⟨X[i], List.getElem_mem hi, by simpa [List.getD_eq_getElem?_getD, hi] using hx⟩

/-- Invariant of Algorithm 3 along a run. -/
def ObjInv (μ : ℝ) (U : Finset (Finset ℕ)) (X : List (Finset (Finset ℕ))) (n : ℕ → ℕ) : Prop :=
  (∀ i j, i ≠ j → Disjoint (X.getD i ∅) (X.getD j ∅)) ∧
  (∀ i, X.getD i ∅ ⊆ U) ∧
  (∀ i < X.length, (U.card : ℝ) ≤ ((X.getD i ∅).card : ℝ) * (2 * μ) ^ (n (i + 1))) ∧
  (U = ∅ → X.length ≤ 1)

lemma sum_card_le (X : List (Finset (Finset ℕ))) (U : Finset (Finset ℕ)) (s : Finset ℕ)
    (hd : ∀ i j, i ≠ j → Disjoint (X.getD i ∅) (X.getD j ∅)) (hs : ∀ i, X.getD i ∅ ⊆ U) :
    ∑ i ∈ s, (X.getD i ∅).card ≤ U.card := by
  rw [← Finset.card_biUnion (fun i _ j _ hij => hd i j hij)]
  exact Finset.card_le_card (Finset.biUnion_subset.2 (fun i _ => hs i))

lemma inv_set (μ : ℝ) (hμ : 1 ≤ μ) (U : Finset (Finset ℕ)) (X : List (Finset (Finset ℕ)))
    (n : ℕ → ℕ) (Aset : Finset (Finset ℕ)) (hI : ObjInv μ U X n)
    (c : ℕ) (hc1 : 1 ≤ c) (hc2 : c ≤ X.length)
    (ht : (((X.getD (c - 1) ∅) ∩ Aset).card : ℝ) ≥ ((X.getD (c - 1) ∅).card : ℝ) / (2 * μ)) :
    1 ≤ c ∧ c ≤ (X.set (c - 1) ((X.getD (c - 1) ∅) ∩ Aset)).length ∧
      X.length ≤ (X.set (c - 1) ((X.getD (c - 1) ∅) ∩ Aset)).length ∧
      ObjInv μ U (X.set (c - 1) ((X.getD (c - 1) ∅) ∩ Aset)) (Function.update n c (n c + 1)) := by
  obtain ⟨hd, hs, ha, he⟩ := hI
  have hlt : c - 1 < X.length := by omega
  have hg : ∀ j, (X.set (c - 1) ((X.getD (c - 1) ∅) ∩ Aset)).getD j ∅ =
      if j = c - 1 then (X.getD (c - 1) ∅) ∩ Aset else X.getD j ∅ :=
    fun j => getD_set_eq X _ j _ hlt
  have hsub : ∀ j, (X.set (c - 1) ((X.getD (c - 1) ∅) ∩ Aset)).getD j ∅ ⊆ X.getD j ∅ := by
    intro j; rw [hg]; split_ifs with h
    · subst h; exact Finset.inter_subset_left
    · exact Finset.Subset.refl _
  have h2μ : (0 : ℝ) < 2 * μ := by linarith
  refine ⟨hc1, by simpa using hc2, by simp, ?_, ?_, ?_, ?_⟩
  · intro i j hij; exact (hd i j hij).mono (hsub i) (hsub j)
  · intro i; exact (hsub i).trans (hs i)
  · intro i hi
    rw [List.length_set] at hi
    by_cases hic : i + 1 = c
    · have hi' : i = c - 1 := by omega
      rw [hg, if_pos hi', hic, Function.update_self]
      have h1 := ha i hi
      rw [hic, hi'] at h1
      have h3 : ((X.getD (c - 1) ∅).card : ℝ) ≤ (((X.getD (c - 1) ∅) ∩ Aset).card : ℝ) * (2 * μ) :=
        (div_le_iff₀ h2μ).1 ht
      have hp : (0 : ℝ) ≤ (2 * μ) ^ (n c) := by positivity
      calc (U.card : ℝ) ≤ ((X.getD (c - 1) ∅).card : ℝ) * (2 * μ) ^ (n c) := h1
        _ ≤ ((((X.getD (c - 1) ∅) ∩ Aset).card : ℝ) * (2 * μ)) * (2 * μ) ^ (n c) :=
          mul_le_mul_of_nonneg_right h3 hp
        _ = _ := by rw [pow_succ]; ring
    · rw [Function.update_of_ne hic, hg, if_neg (by omega)]; exact ha i hi
  · intro hU; simpa using he hU

lemma inv_app (μ : ℝ) (hμ : 1 ≤ μ) (U : Finset (Finset ℕ)) (X : List (Finset (Finset ℕ)))
    (n : ℕ → ℕ) (Aset : Finset (Finset ℕ)) (hAU : Aset ⊆ U)
    (hsz : (U.card : ℝ) ≤ μ * (Aset.card : ℝ)) (hI : ObjInv μ U X n)
    (hno : ∀ c ∈ Finset.Icc 1 X.length, ¬ ((((X.getD (c - 1) ∅) ∩ Aset).card : ℝ) ≥
      ((X.getD (c - 1) ∅).card : ℝ) / (2 * μ))) :
    1 ≤ X.length + 1 ∧ X.length + 1 ≤ (X ++ [Aset \ X.foldr (· ∪ ·) ∅]).length ∧
      X.length ≤ (X ++ [Aset \ X.foldr (· ∪ ·) ∅]).length ∧
      ObjInv μ U (X ++ [Aset \ X.foldr (· ∪ ·) ∅])
        (Function.update n (X.length + 1) (n (X.length + 1) + 1)) := by
  obtain ⟨hd, hs, ha, he⟩ := hI
  have h2μ : (0 : ℝ) < 2 * μ := by linarith
  set F := X.foldr (· ∪ ·) ∅ with hF
  set B := Aset \ F with hBdef
  have hg := getD_append_single X B
  have hXF : ∀ j < X.length, X.getD j ∅ ⊆ F := by
    intro j hj
    rw [hF, foldr_eq_biUnion]
    exact Finset.subset_biUnion_of_mem (fun i => X.getD i ∅) (Finset.mem_range.2 hj)
  have hBX : ∀ j < X.length, Disjoint B (X.getD j ∅) := by
    intro j hj
    exact (Finset.sdiff_disjoint).mono_right (hXF j hj)
  have hno' : ∀ i < X.length, (((X.getD i ∅) ∩ Aset).card : ℝ) < ((X.getD i ∅).card : ℝ) / (2 * μ) := by
    intro i hi
    have := hno (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    simpa using this
  -- the main estimate
  have hmain : (U.card : ℝ) ≤ (B.card : ℝ) * (2 * μ) := by
    have hB : (B.card : ℝ) + ((Aset ∩ F).card : ℝ) = Aset.card := by
      rw [hBdef]; exact_mod_cast Finset.card_sdiff_add_card_inter Aset F
    have hAF1 : (Aset ∩ F).card ≤ ∑ i ∈ Finset.range X.length, ((X.getD i ∅) ∩ Aset).card := by
      refine le_trans (Finset.card_le_card ?_) Finset.card_biUnion_le
      intro x hx
      rw [Finset.mem_inter] at hx
      have hx2 := hx.2
      rw [hF, foldr_eq_biUnion, Finset.mem_biUnion] at hx2
      obtain ⟨i, hi, hxi⟩ := hx2
      exact Finset.mem_biUnion.2 ⟨i, hi, Finset.mem_inter.2 ⟨hxi, hx.1⟩⟩
    have hAF2 : (∑ i ∈ Finset.range X.length, (((X.getD i ∅) ∩ Aset).card : ℝ)) ≤
        ∑ i ∈ Finset.range X.length, ((X.getD i ∅).card : ℝ) / (2 * μ) :=
      Finset.sum_le_sum (fun i hi => (hno' i (Finset.mem_range.1 hi)).le)
    have hAF3 : (∑ i ∈ Finset.range X.length, ((X.getD i ∅).card : ℝ)) ≤ U.card := by
      exact_mod_cast sum_card_le X U _ hd hs
    have hAF : ((Aset ∩ F).card : ℝ) ≤ (U.card : ℝ) / (2 * μ) := by
      calc ((Aset ∩ F).card : ℝ)
          ≤ ∑ i ∈ Finset.range X.length, (((X.getD i ∅) ∩ Aset).card : ℝ) := by exact_mod_cast hAF1
        _ ≤ ∑ i ∈ Finset.range X.length, ((X.getD i ∅).card : ℝ) / (2 * μ) := hAF2
        _ = (∑ i ∈ Finset.range X.length, ((X.getD i ∅).card : ℝ)) / (2 * μ) := by
          rw [Finset.sum_div]
        _ ≤ (U.card : ℝ) / (2 * μ) := div_le_div_of_nonneg_right hAF3 h2μ.le
    have hAF' : ((Aset ∩ F).card : ℝ) * (2 * μ) ≤ U.card := (le_div_iff₀ h2μ).1 hAF
    have e : (B.card : ℝ) * (2 * μ) = (Aset.card : ℝ) * (2 * μ) - ((Aset ∩ F).card : ℝ) * (2 * μ) := by
      rw [← hB]; ring
    rw [e]; nlinarith
  refine ⟨by omega, by simp, by simp, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    rw [hg, hg]
    split_ifs <;>
      first
      | exact hd i j hij
      | exact (hBX i ‹_›).symm
      | exact hBX j ‹_›
      | exact Finset.disjoint_empty_left _
      | exact Finset.disjoint_empty_right _
      | exact (hBX j ‹_›).symm
      | exact hBX i ‹_›
      | omega
  · intro i
    rw [hg]
    split_ifs
    · exact hs i
    · exact Finset.sdiff_subset.trans hAU
    · exact Finset.empty_subset _
  · intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hil : i < X.length
    · rw [Function.update_of_ne (by omega), hg, if_pos hil]; exact ha i hil
    · have hi' : i = X.length := by omega
      rw [hi', Function.update_self, hg, if_neg (lt_irrefl _), if_pos rfl]
      have h1 : (1 : ℝ) ≤ (2 * μ) ^ (n (X.length + 1)) := one_le_pow₀ (by linarith)
      have hB0 : (0 : ℝ) ≤ B.card := by positivity
      calc (U.card : ℝ) ≤ (B.card : ℝ) * (2 * μ) := hmain
        _ ≤ (B.card : ℝ) * (2 * μ) * (2 * μ) ^ (n (X.length + 1)) := by
          have : (0 : ℝ) ≤ (B.card : ℝ) * (2 * μ) := by positivity
          nlinarith
        _ = _ := by rw [pow_succ]; ring
  · intro hU
    simp only [List.length_append, List.length_singleton]
    by_contra hcon
    have hpos : 0 < X.length := by omega
    have h0 := hno' 0 hpos
    have hX0 : X.getD 0 ∅ = ∅ := by
      have := hs 0; rw [hU] at this; exact Finset.subset_empty.1 this
    rw [hX0] at h0
    simp at h0

lemma objStep_inv (μ : ℝ) (hμ : 1 ≤ μ) (U : Finset (Finset ℕ)) (X : List (Finset (Finset ℕ)))
    (n : ℕ → ℕ) (pick : Finset ℕ → ℕ) (Aset : Finset (Finset ℕ))
    (hpick : ∀ S : Finset ℕ, S.Nonempty → pick S ∈ S) (hAU : Aset ⊆ U)
    (hsz : (U.card : ℝ) ≤ μ * (Aset.card : ℝ)) (hI : ObjInv μ U X n) :
    1 ≤ (objStep μ pick X Aset).2 ∧ (objStep μ pick X Aset).2 ≤ (objStep μ pick X Aset).1.length ∧
      X.length ≤ (objStep μ pick X Aset).1.length ∧
      ObjInv μ U (objStep μ pick X Aset).1
        (Function.update n (objStep μ pick X Aset).2 (n (objStep μ pick X Aset).2 + 1)) := by
  simp only [objStep]
  split_ifs with hc
  · have hcm := hpick _ hc
    rw [Finset.mem_filter, Finset.mem_Icc] at hcm
    exact inv_set μ hμ U X n Aset hI _ hcm.1.1 hcm.1.2 hcm.2
  · have hno := Finset.filter_eq_empty_iff.1 (Finset.not_nonempty_iff_eq_empty.1 hc)
    exact inv_app μ hμ U X n Aset hAU hsz hI hno

lemma objRun_length (μ : ℝ) : ∀ (as : List ((Finset ℕ → ℕ) × Finset (Finset ℕ)))
    (X : List (Finset (Finset ℕ))), (objRun μ X as).2.length = as.length
  | [], X => by simp [objRun]
  | a :: as, X => by simp [objRun, objRun_length μ as]

lemma objRun_inv (μ : ℝ) (hμ : 1 ≤ μ) (U : Finset (Finset ℕ)) :
    ∀ (as : List ((Finset ℕ → ℕ) × Finset (Finset ℕ))) (X : List (Finset (Finset ℕ)))
      (n : ℕ → ℕ),
    (∀ a ∈ as, ∀ S : Finset ℕ, S.Nonempty → a.1 S ∈ S) → (∀ a ∈ as, a.2 ⊆ U) →
    (∀ a ∈ as, (U.card : ℝ) ≤ μ * (a.2.card : ℝ)) → ObjInv μ U X n →
    ObjInv μ U (objRun μ X as).1 (fun c => n c + (objRun μ X as).2.count c) ∧
      (∀ c ∈ (objRun μ X as).2, 1 ≤ c ∧ c ≤ (objRun μ X as).1.length) ∧
      X.length ≤ (objRun μ X as).1.length
  | [], X, n, _, _, _, hI => by
    simp only [objRun, List.count_nil, add_zero, List.not_mem_nil, false_implies, implies_true,
      le_refl, and_true]
    exact hI
  | a :: as, X, n, hp, hU, hs, hI => by
    obtain ⟨h1, h2, h3, h4⟩ := objStep_inv μ hμ U X n a.1 a.2 (hp a List.mem_cons_self)
      (hU a List.mem_cons_self) (hs a List.mem_cons_self) hI
    obtain ⟨i1, i2, i3⟩ := objRun_inv μ hμ U as _ _ (fun b hb => hp b (List.mem_cons_of_mem _ hb))
      (fun b hb => hU b (List.mem_cons_of_mem _ hb)) (fun b hb => hs b (List.mem_cons_of_mem _ hb)) h4
    simp only [objRun]
    refine ⟨?_, ?_, by omega⟩
    · convert i1 using 1
      funext c
      by_cases hc : c = (objStep μ a.1 X a.2).2
      · subst hc; simp only [Function.update_self, List.count_cons_self]; omega
      · simp [Function.update_of_ne hc, Ne.symm hc]
    · intro c hc
      rw [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact ⟨h1, by omega⟩
      · exact i2 c hc

/-- Paper's Lemma 6.3: with `μ ≥ 1`, every selection rule valid and every set of size at least
`|U|/μ` (`U` the union of all sets), Algorithm 3 uses at most `p/h + (2μ)^{h−1}` colors. -/
theorem obj_colors_le (μ : ℝ) (hμ : 1 ≤ μ) (as : List ((Finset ℕ → ℕ) × Finset (Finset ℕ)))
    (hpick : ∀ a ∈ as, ∀ S : Finset ℕ, S.Nonempty → a.1 S ∈ S)
    (hsize : ∀ a ∈ as, ((as.map Prod.snd).foldr (· ∪ ·) ∅).card ≤ μ * (a.2.card : ℝ))
    (h : ℕ) (hh : 1 ≤ h) :
    ((objRun μ [] as).2.toFinset.card : ℝ) ≤ (as.length : ℝ) / h + (2 * μ) ^ (h - 1) := by
  set U := (as.map Prod.snd).foldr (· ∪ ·) ∅ with hUdef
  have hAU : ∀ a ∈ as, a.2 ⊆ U := fun a ha x hx =>
    (mem_foldr_union _ x).2 ⟨a.2, List.mem_map_of_mem ha, hx⟩
  have h0 : ObjInv μ U [] (fun _ => 0) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp
  obtain ⟨⟨hd, hs, ha, he⟩, hcol, -⟩ := objRun_inv μ hμ U as [] (fun _ => 0) hpick hAU hsize h0
  set Xf := (objRun μ [] as).1 with hXf
  set Lc := (objRun μ [] as).2 with hLc
  have hlen : Lc.length = as.length := objRun_length μ as []
  simp only [zero_add] at ha
  have h2μ : (1 : ℝ) ≤ 2 * μ := by linarith
  have hpow1 : (1 : ℝ) ≤ (2 * μ) ^ (h - 1) := one_le_pow₀ h2μ
  have hhpos : (0 : ℝ) < h := by exact_mod_cast hh
  have hp0 : (0 : ℝ) ≤ (as.length : ℝ) / h := by positivity
  set S := Lc.toFinset with hS
  have hSI : S ⊆ Finset.Icc 1 Xf.length := by
    intro c hc
    rw [hS, List.mem_toFinset] at hc
    exact Finset.mem_Icc.2 (hcol c hc)
  by_cases hU : U = ∅
  · have h1 : S.card ≤ 1 := by
      calc S.card ≤ (Finset.Icc 1 Xf.length).card := Finset.card_le_card hSI
        _ = Xf.length := by simp
        _ ≤ 1 := he hU
    have : (S.card : ℝ) ≤ 1 := by exact_mod_cast h1
    linarith
  have hUpos : (0 : ℝ) < U.card := by
    have : U.Nonempty := Finset.nonempty_iff_ne_empty.2 hU
    exact_mod_cast this.card_pos
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (fun c => h ≤ Lc.count c)
  -- colors used at least `h` times
  have hbig : ((S.filter (fun c => h ≤ Lc.count c)).card : ℝ) ≤ (as.length : ℝ) / h := by
    have h1 : (S.filter (fun c => h ≤ Lc.count c)).card • h ≤
        ∑ c ∈ S.filter (fun c => h ≤ Lc.count c), Lc.count c :=
      Finset.card_nsmul_le_sum _ _ _ (fun c hc => (Finset.mem_filter.1 hc).2)
    have h2 : ∑ c ∈ S.filter (fun c => h ≤ Lc.count c), Lc.count c ≤ ∑ c ∈ S, Lc.count c :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have h3 : ∑ c ∈ S, Lc.count c = Lc.length := List.sum_toFinset_count_eq_length Lc
    have h4 : (S.filter (fun c => h ≤ Lc.count c)).card * h ≤ as.length := by
      rw [smul_eq_mul] at h1; omega
    rw [le_div_iff₀ hhpos]
    exact_mod_cast h4
  -- colors used fewer than `h` times
  have hsmall : ((S.filter (fun c => ¬ h ≤ Lc.count c)).card : ℝ) ≤ (2 * μ) ^ (h - 1) := by
    set Ss := S.filter (fun c => ¬ h ≤ Lc.count c) with hSs
    have hmem : ∀ c ∈ Ss, 1 ≤ c ∧ c ≤ Xf.length ∧ ¬ h ≤ Lc.count c := by
      intro c hc
      rw [hSs, Finset.mem_filter] at hc
      have := Finset.mem_Icc.1 (hSI hc.1)
      exact ⟨this.1, this.2, hc.2⟩
    have hdisj : (Ss : Set ℕ).PairwiseDisjoint (fun c => Xf.getD (c - 1) ∅) := by
      intro x hx y hy hxy
      have := hmem x hx; have := hmem y hy
      exact hd _ _ (by omega)
    have hsum : ∑ c ∈ Ss, (Xf.getD (c - 1) ∅).card ≤ U.card := by
      rw [← Finset.card_biUnion hdisj]
      exact Finset.card_le_card (Finset.biUnion_subset.2 (fun i _ => hs _))
    have hsumR : (∑ c ∈ Ss, ((Xf.getD (c - 1) ∅).card : ℝ)) ≤ U.card := by exact_mod_cast hsum
    have hterm : ∀ c ∈ Ss, (U.card : ℝ) ≤ ((Xf.getD (c - 1) ∅).card : ℝ) * (2 * μ) ^ (h - 1) := by
      intro c hc
      obtain ⟨hc1, hc2, hc3⟩ := hmem c hc
      have := ha (c - 1) (by omega)
      rw [show c - 1 + 1 = c by omega] at this
      refine this.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h2μ (by omega)) (by positivity))
    have hmul : (Ss.card : ℝ) * U.card ≤ (2 * μ) ^ (h - 1) * U.card := by
      calc (Ss.card : ℝ) * U.card = ∑ c ∈ Ss, (U.card : ℝ) := by simp
        _ ≤ ∑ c ∈ Ss, ((Xf.getD (c - 1) ∅).card : ℝ) * (2 * μ) ^ (h - 1) := Finset.sum_le_sum hterm
        _ = (∑ c ∈ Ss, ((Xf.getD (c - 1) ∅).card : ℝ)) * (2 * μ) ^ (h - 1) := by
          rw [Finset.sum_mul]
        _ ≤ (U.card : ℝ) * (2 * μ) ^ (h - 1) :=
          mul_le_mul_of_nonneg_right hsumR (by positivity)
        _ = (2 * μ) ^ (h - 1) * U.card := by ring
    exact le_of_mul_le_mul_right hmul hUpos
  have : (S.card : ℝ) = ((S.filter (fun c => h ≤ Lc.count c)).card : ℝ) +
      ((S.filter (fun c => ¬ h ≤ Lc.count c)).card : ℝ) := by exact_mod_cast hsplit.symm
  rw [this]
  linarith

end OnlineColoringKYY.Supplement.Dev.T626.PartOC
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626
open Classical OnlineColoringKYY.Supplement
alias obj_colors_le := OnlineColoringKYY.Supplement.Dev.T626.PartOC.obj_colors_le

end OnlineColoringKYY.Supplement.Dev.T626
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartCF
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
/-!
Paper's Lemma 6.4 (CliqueFree(r) uses at most `(r−1)/(2A²)·n_r` colors), for partial runs.
Strong induction on `r ≥ 2`; at `r ≥ 3` a run invariant on the bins and the object coloring
instance, then counting.
-/
/-! ## Generic run lemmas -/
theorem cfRun_append (A : ℕ) (R : Resolver) (Adjf : ℕ → ℕ → ℕ → Prop) (r : ℕ) (addr : List ℕ)
    (vs ws : List ℕ) (s : CFState) :
    cfRun A R Adjf r addr (vs ++ ws) s =
      ((cfRun A R Adjf r addr ws (cfRun A R Adjf r addr vs s).1).1,
        (cfRun A R Adjf r addr vs s).2 ++
          (cfRun A R Adjf r addr ws (cfRun A R Adjf r addr vs s).1).2) := by
  induction vs generalizing s with
  | nil => simp [cfRun]
  | cons v vs ih => simp [cfRun, ih]

theorem cfRun_single (A : ℕ) (R : Resolver) (Adjf : ℕ → ℕ → ℕ → Prop) (r : ℕ) (addr : List ℕ)
    (v : ℕ) (s : CFState) :
    cfRun A R Adjf r addr [v] s =
      ((cfStep A R (Adjf v) v r addr s).1, [(cfStep A R (Adjf v) v r addr s).2]) := by
  simp [cfRun]

theorem objRun_append (μ : ℝ) (X : List (Finset (Finset ℕ)))
    (as bs : List ((Finset ℕ → ℕ) × Finset (Finset ℕ))) :
    objRun μ X (as ++ bs) =
      ((objRun μ (objRun μ X as).1 bs).1, (objRun μ X as).2 ++ (objRun μ (objRun μ X as).1 bs).2) := by
  induction as generalizing X with
  | nil => simp [objRun]
  | cons a as ih => simp [objRun, ih]

theorem objRun_single (μ : ℝ) (X : List (Finset (Finset ℕ)))
    (a : (Finset ℕ → ℕ) × Finset (Finset ℕ)) :
    objRun μ X [a] = ((objStep μ a.1 X a.2).1, [(objStep μ a.1 X a.2).2]) := by
  simp [objRun]

/-! ## Consistency in recursive form -/
/-- `Adjf v` agrees with `Adj` on `v` and the earlier vertices `H`. -/
def Agree (Adjf : ℕ → ℕ → ℕ → Prop) (Adj : ℕ → ℕ → Prop) (v : ℕ) (H : List ℕ) : Prop :=
  ∀ a ∈ v :: H, ∀ b ∈ v :: H, (Adjf v a b ↔ Adj a b)

/-- Consistency of a run `vs` that follows the history `H`. -/
def Cons2 (Adjf : ℕ → ℕ → ℕ → Prop) (Adj : ℕ → ℕ → Prop) : List ℕ → List ℕ → Prop
  | _, [] => True
  | H, v :: vs => Agree Adjf Adj v H ∧ Cons2 Adjf Adj (H ++ [v]) vs

theorem agree_mono {Adjf : ℕ → ℕ → ℕ → Prop} {Adj : ℕ → ℕ → Prop} {v : ℕ} {H H' : List ℕ}
    (h : Agree Adjf Adj v H) (hs : ∀ x ∈ H', x ∈ H) : Agree Adjf Adj v H' := by
  have hm : ∀ a ∈ v :: H', a ∈ v :: H := by
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · simp
    · exact List.mem_cons_of_mem _ (hs a ha)
  intro a ha b hb
  exact h a (hm a ha) b (hm b hb)

theorem cons2_append_single {Adjf : ℕ → ℕ → ℕ → Prop} {Adj : ℕ → ℕ → Prop} (L : List ℕ) (v : ℕ) :
    ∀ H : List ℕ, Cons2 Adjf Adj H (L ++ [v]) ↔ Cons2 Adjf Adj H L ∧ Agree Adjf Adj v (H ++ L) := by
  induction L with
  | nil => intro H; simp [Cons2]
  | cons w L ih => intro H; simp [Cons2, ih, and_assoc]

theorem cons2_of_consistent {Adjf : ℕ → ℕ → ℕ → Prop} {Adj : ℕ → ℕ → Prop} (vs : List ℕ) :
    ∀ H : List ℕ, Consistent Adjf Adj (H ++ vs) → Cons2 Adjf Adj H vs := by
  induction vs with
  | nil => intro H _; exact trivial
  | cons v vs ih =>
    intro H h
    refine ⟨?_, ih (H ++ [v]) (by simpa using h)⟩
    intro a ha b hb
    have hi : H.length < (H ++ v :: vs).length := by simp
    have key := h H.length hi
    have hget : (H ++ v :: vs).get ⟨H.length, hi⟩ = v := by simp
    have htake : (H ++ v :: vs).take (H.length + 1) = H ++ [v] := by
      rw [List.take_append]; simp
    rw [hget, htake] at key
    exact key a (by simp at ha ⊢; tauto) b (by simp at hb ⊢; tauto)

/-! ## Cliques -/
theorem mem_cliquesIn {Adj : ℕ → ℕ → Prop} {k : ℕ} {S t : Finset ℕ} :
    t ∈ cliquesIn Adj k S ↔ t ⊆ S ∧ t.card = k ∧ IsCliqueSet Adj t := by
  simp [cliquesIn]

theorem cliquesIn_congr {Adj1 Adj2 : ℕ → ℕ → Prop} {k : ℕ} {S : Finset ℕ}
    (h : ∀ a ∈ S, ∀ b ∈ S, (Adj1 a b ↔ Adj2 a b)) : cliquesIn Adj1 k S = cliquesIn Adj2 k S := by
  ext t
  rw [mem_cliquesIn, mem_cliquesIn]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun a ha b hb hab => (h a (h1 ha) b (h1 hb)).1 (h3 a ha b hb hab)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun a ha b hb hab => (h a (h1 ha) b (h1 hb)).2 (h3 a ha b hb hab)⟩

theorem cliquesIn_singleton {Adj : ℕ → ℕ → Prop} (q v : ℕ) : cliquesIn Adj (q + 2) {v} = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro s hs
  rw [mem_cliquesIn] at hs
  have := Finset.card_le_card hs.1
  rw [hs.2.1, Finset.card_singleton] at this
  omega

/-! ## Finset unions along lists -/
theorem mem_foldr_union (l : List (Finset (Finset ℕ))) (x : Finset ℕ) :
    x ∈ l.foldr (· ∪ ·) ∅ ↔ ∃ s ∈ l, x ∈ s := by
  induction l with
  | nil => simp
  | cons s l ih => simp [ih]

theorem mem_foldr_union' {β : Type} (g : β → Finset (Finset ℕ)) (l : List β) (x : Finset ℕ) :
    x ∈ l.foldr (fun L acc => g L ∪ acc) ∅ ↔ ∃ L ∈ l, x ∈ g L := by
  induction l with
  | nil => simp
  | cons s l ih => simp [ih]

theorem card_foldr_union_le {β : Type} (g : β → Finset (Finset ℕ)) (l : List β) :
    (l.foldr (fun L acc => g L ∪ acc) ∅).card ≤ (l.map (fun L => (g L).card)).sum := by
  induction l with
  | nil => simp
  | cons s l ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left ih _)

/-! ## The pieces of one step of Algorithm 4 -/
/-- Bin `B` may receive `v`. -/
def OkB (A q : ℕ) (Adj : ℕ → ℕ → Prop) (v : ℕ) (B : Finset ℕ) : Prop :=
  B.card < nSeq A (q + 2) ∧ cliquesIn Adj (q + 2) (insert v B) = ∅

/-- The set presented to object coloring. -/
noncomputable def asetOf (Adj : ℕ → ℕ → Prop) (q v : ℕ) (bins : List (Finset ℕ × CFState)) :
    Finset (Finset ℕ) :=
  List.foldr (fun b acc => acc ∪ cliquesIn Adj (q + 1) ({u ∈ b.1 | Adj v u})) ∅ bins

/-- The number of incomplete bins. -/
def incOf (A q : ℕ) (bins : List (Finset ℕ × CFState)) : ℕ :=
  (List.filter (fun b => decide (1 ≤ b.1.card ∧ b.1.card < nSeq A (q + 2))) bins).length

/-- `J`. -/
def Jof (A q : ℕ) : ℕ := nSeq A (q + 3) / (3 * (q + 3) * nSeq A (q + 2))

/-- `μ`. -/
noncomputable def muOf (A q : ℕ) : ℝ := 3 * ((q + 3 : ℕ) : ℝ) * ((nSeq A (q + 2) : ℕ) : ℝ) ^ (q + 2)

theorem mem_asetOf {Adj : ℕ → ℕ → Prop} {q v : ℕ} {bins : List (Finset ℕ × CFState)}
    {t : Finset ℕ} :
    t ∈ asetOf Adj q v bins ↔ ∃ b ∈ bins, t ∈ cliquesIn Adj (q + 1) ({u ∈ b.1 | Adj v u}) := by
  induction bins with
  | nil => simp [asetOf]
  | cons b bins ih =>
    simp only [asetOf, List.foldr_cons] at ih ⊢
    rw [Finset.mem_union, ih]
    simp only [List.mem_cons, exists_eq_or_imp]
    exact or_comm

theorem find_facts {p : ℕ → Prop} [DecidablePred p] (h : ∃ j, p j) :
    p (Nat.find h) ∧ ∀ k < Nat.find h, ¬ p k :=
  ⟨Nat.find_spec h, fun _ hk => Nat.find_min h hk⟩

theorem cfStep_cases (A : ℕ) (R : Resolver) (Adj : ℕ → ℕ → Prop) (v q : ℕ) (addr : List ℕ)
    (bins : List (Finset ℕ × CFState)) (obj : List (Finset (Finset ℕ))) :
    ((∀ k (hk : k < bins.length), ¬ OkB A q Adj v bins[k].1) ∧ incOf A q bins = Jof A q ∧
      cfStep A R Adj v (q + 3) addr (CFState.mk bins obj) =
        (CFState.mk bins
          (objStep (muOf A q) (R.objColor (addr ++ [1, 0, 0]) v) obj (asetOf Adj q v bins)).1,
          (addr ++ [1, 0, 0],
            (objStep (muOf A q) (R.objColor (addr ++ [1, 0, 0]) v) obj (asetOf Adj q v bins)).2))) ∨
    (∃ j, ∃ hj : j < bins.length, OkB A q Adj v bins[j].1 ∧
      cfStep A R Adj v (q + 3) addr (CFState.mk bins obj) =
        (CFState.mk (bins.set j (insert v bins[j].1,
            (cfStep A R Adj v (q + 2) (addr ++ [0, j, 0]) bins[j].2).1)) obj,
          (cfStep A R Adj v (q + 2) (addr ++ [0, j, 0]) bins[j].2).2)) ∨
    (incOf A q bins ≠ Jof A q ∧
      cfStep A R Adj v (q + 3) addr (CFState.mk bins obj) =
        (CFState.mk (bins ++ [({v},
            (cfStep A R Adj v (q + 2) (addr ++ [0, bins.length, 0]) (CFState.mk [] [])).1)]) obj,
          (cfStep A R Adj v (q + 2) (addr ++ [0, bins.length, 0]) (CFState.mk [] [])).2)) := by
  rw [cfStep]
  obtain ⟨hs, hm⟩ := find_facts (p := fun j => (j < bins.length ∧
      ((bins.getD j (∅, default)).1.card < nSeq A (q + 2) ∧
        cliquesIn Adj (q + 2) (insert v (bins.getD j (∅, default)).1) = ∅)) ∨ j = bins.length)
    ⟨bins.length, Or.inr rfl⟩
  generalize Nat.find (p := fun j => (j < bins.length ∧
      ((bins.getD j (∅, default)).1.card < nSeq A (q + 2) ∧
        cliquesIn Adj (q + 2) (insert v (bins.getD j (∅, default)).1) = ∅)) ∨ j = bins.length)
    ⟨bins.length, Or.inr rfl⟩ = j at hs hm ⊢
  by_cases hc : j = bins.length ∧ incOf A q bins = Jof A q
  · left
    obtain ⟨hj, hinc⟩ := hc
    subst hj
    refine ⟨?_, hinc, ?_⟩
    · intro k hk hok
      exact hm k hk (Or.inl ⟨hk, by rw [List.getD_eq_getElem _ _ hk]; exact hok⟩)
    · unfold incOf Jof at hinc
      rw [if_pos ⟨rfl, hinc⟩]
      rfl
  · right
    have hc' : ¬ (j = bins.length ∧
        (List.filter (fun b => decide (1 ≤ b.1.card ∧ b.1.card < nSeq A (q + 2))) bins).length =
          nSeq A (q + 3) / (3 * (q + 3) * nSeq A (q + 2))) := hc
    rw [if_neg hc']
    rcases hs with ⟨hj, hok⟩ | hj
    · left
      refine ⟨j, hj, ?_, ?_⟩
      · rw [List.getD_eq_getElem _ _ hj] at hok; exact hok
      · simp only [List.getD_eq_getElem _ _ hj, if_pos hj]
    · right
      subst hj
      refine ⟨fun h => hc ⟨rfl, h⟩, ?_⟩
      simp only [List.getD_eq_default _ _ le_rfl, lt_irrefl, if_false]
      rfl

/-! ## The run invariant -/
/-- An arrival of object coloring: a selection rule and a presented set. -/
abbrev Arr : Type := (Finset ℕ → ℕ) × Finset (Finset ℕ)

/-- The state of bin `j` holding the vertex list `L`. -/
noncomputable def binSt (A : ℕ) (R : Resolver) (Adjf : ℕ → ℕ → ℕ → Prop) (q : ℕ)
    (addr : List ℕ) (j : ℕ) (L : List ℕ) : Finset ℕ × CFState :=
  (L.toFinset, (cfRun A R Adjf (q + 2) (addr ++ [0, j, 0]) L (CFState.mk [] [])).1)

/-- The bins are those of the vertex lists `ls`. -/
def BinsRel (A : ℕ) (R : Resolver) (Adjf : ℕ → ℕ → ℕ → Prop) (q : ℕ) (addr : List ℕ)
    (bins : List (Finset ℕ × CFState)) (ls : List (List ℕ)) : Prop :=
  bins.length = ls.length ∧
    ∀ j (h1 : j < bins.length) (h2 : j < ls.length), bins[j] = binSt A R Adjf q addr j ls[j]

/-- A color of a bin's sub-instance or of the object coloring instance. -/
def InColors (A : ℕ) (R : Resolver) (Adjf : ℕ → ℕ → ℕ → Prop) (q : ℕ) (addr : List ℕ)
    (ls : List (List ℕ)) (as : List Arr) (c : Color) : Prop :=
  (∃ j, ∃ hj : j < ls.length,
      c ∈ (cfRun A R Adjf (q + 2) (addr ++ [0, j, 0]) ls[j] (CFState.mk [] [])).2) ∨
    (∃ x ∈ (objRun (muOf A q) [] as).2, c = (addr ++ [1, 0, 0], x))

/-- The run invariant of CliqueFree(q + 3) after processing the vertices `P`. -/
structure Inv (A : ℕ) (R : Resolver) (Adjf : ℕ → ℕ → ℕ → Prop) (Adj : ℕ → ℕ → Prop) (q : ℕ)
    (addr : List ℕ) (P : List ℕ) (ls : List (List ℕ)) (as : List Arr) (s : CFState)
    (cs : List Color) : Prop where
  st : ∃ bins, s = CFState.mk bins (objRun (muOf A q) [] as).1 ∧ BinsRel A R Adjf q addr bins ls
  nodup : ls.flatten.Nodup
  sub : ∀ x ∈ ls.flatten, x ∈ P
  each : ∀ L ∈ ls, L ≠ [] ∧ L.length ≤ nSeq A (q + 2) ∧ cliquesIn Adj (q + 2) L.toFinset = ∅ ∧
    Cons2 Adjf Adj [] L
  inc : ls.countP (fun L => decide (L.length < nSeq A (q + 2))) ≤ Jof A q
  asg : ∀ a ∈ as, (∀ S : Finset ℕ, S.Nonempty → a.1 S ∈ S) ∧ Jof A q ≤ a.2.card ∧
    ∀ t ∈ a.2, t.card = q + 1 ∧ ∃ L ∈ ls, t ⊆ L.toFinset
  aslen : as.length ≤ P.length
  cols : ∀ c ∈ cs, InColors A R Adjf q addr ls as c

/-- Each bin list extends the old one. -/
def Grow (ls ls' : List (List ℕ)) : Prop :=
  ∀ j (hj : j < ls.length), ∃ hj' : j < ls'.length, ∃ w, ls'[j] = ls[j] ++ w

end OnlineColoringKYY.Supplement.Dev.T626.PartCF
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartCF
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
variable {A : ℕ} {R : Resolver} {Adjf : ℕ → ℕ → ℕ → Prop} {Adj : ℕ → ℕ → Prop} {q : ℕ}
  {addr : List ℕ}
theorem grow_refl (ls : List (List ℕ)) : Grow ls ls := fun _ hj => ⟨hj, [], by simp⟩

theorem grow_mem {ls ls' : List (List ℕ)} (hg : Grow ls ls') {t : Finset ℕ}
    (h : ∃ L ∈ ls, t ⊆ L.toFinset) : ∃ L ∈ ls', t ⊆ L.toFinset := by
  obtain ⟨L, hL, ht⟩ := h
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hL
  obtain ⟨hj', w, hw⟩ := hg j hj
  refine ⟨ls'[j], List.getElem_mem hj', ht.trans ?_⟩
  rw [hw, List.toFinset_append]
  exact Finset.subset_union_left

theorem inColors_mono {ls ls' : List (List ℕ)} {as : List Arr} (hg : Grow ls ls') (w : List Arr)
    {c : Color} (h : InColors A R Adjf q addr ls as c) :
    InColors A R Adjf q addr ls' (as ++ w) c := by
  rcases h with ⟨j, hj, hc⟩ | ⟨x, hx, rfl⟩
  · obtain ⟨hj', w', hw⟩ := hg j hj
    left
    refine ⟨j, hj', ?_⟩
    rw [hw, cfRun_append]
    exact List.mem_append_left _ hc
  · right
    refine ⟨x, ?_, rfl⟩
    rw [objRun_append]
    exact List.mem_append_left _ hx

theorem binsRel_fst {bins : List (Finset ℕ × CFState)} {ls : List (List ℕ)}
    (h : BinsRel A R Adjf q addr bins ls) : bins.map Prod.fst = ls.map List.toFinset := by
  obtain ⟨hl, hb⟩ := h
  apply List.ext_getElem (by simp [hl])
  intro j h1 h2
  simp only [List.getElem_map]
  rw [hb j (by simpa using h1) (by simpa using h2)]
  rfl

theorem incOf_eq {bins : List (Finset ℕ × CFState)} {ls : List (List ℕ)}
    (h : BinsRel A R Adjf q addr bins ls) (hnd : ls.flatten.Nodup) (hne : ∀ L ∈ ls, L ≠ []) :
    incOf A q bins = ls.countP (fun L => decide (L.length < nSeq A (q + 2))) := by
  unfold incOf
  rw [← List.countP_eq_length_filter]
  have : bins.countP (fun b => decide (1 ≤ b.1.card ∧ b.1.card < nSeq A (q + 2))) =
      (bins.map Prod.fst).countP (fun B => decide (1 ≤ B.card ∧ B.card < nSeq A (q + 2))) := by
    rw [List.countP_map]; rfl
  rw [this, binsRel_fst h, List.countP_map]
  apply List.countP_congr
  intro L hL
  have hLn : L.Nodup := (List.nodup_flatten.1 hnd).1 L hL
  have hc : L.toFinset.card = L.length := List.toFinset_card_of_nodup hLn
  have hpos : 0 < L.length := List.length_pos_iff.2 (hne L hL)
  simp only [Function.comp, hc, decide_eq_true_eq]
  omega

theorem reject_card {P : List ℕ} {v : ℕ} {bins : List (Finset ℕ × CFState)}
    {ls : List (List ℕ)} (hb : BinsRel A R Adjf q addr bins ls) (hnd : ls.flatten.Nodup)
    (hsub : ∀ x ∈ ls.flatten, x ∈ P) (hfree : ∀ L ∈ ls, cliquesIn Adj (q + 2) L.toFinset = ∅)
    (hag : Agree Adjf Adj v P) (hrej : ∀ k (hk : k < bins.length), ¬ OkB A q (Adjf v) v bins[k].1) :
    ls.countP (fun L => decide (L.length < nSeq A (q + 2))) ≤ (asetOf (Adjf v) q v bins).card := by
  obtain ⟨hl, hbk⟩ := hb
  rw [List.countP_eq_length_filter]
  have key : ∀ L ∈ ls.filter (fun L => decide (L.length < nSeq A (q + 2))),
      ∃ t ∈ asetOf (Adjf v) q v bins, t.Nonempty ∧ t ⊆ L.toFinset := by
    intro L hL
    rw [List.mem_filter] at hL
    obtain ⟨hL, hlt⟩ := hL
    simp only [decide_eq_true_eq] at hlt
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hL
    have hk' : k < bins.length := hl ▸ hk
    have hbkk := hbk k hk' hk
    have hLn : ls[k].Nodup := (List.nodup_flatten.1 hnd).1 _ hL
    have hcard : ls[k].toFinset.card = ls[k].length := List.toFinset_card_of_nodup hLn
    have hne : cliquesIn (Adjf v) (q + 2) (insert v ls[k].toFinset) ≠ ∅ := by
      intro h0
      apply hrej k hk'
      rw [hbkk]
      unfold OkB binSt
      exact ⟨(by rw [hcard]; exact hlt : ls[k].toFinset.card < nSeq A (q + 2)), h0⟩
    obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.2 hne
    rw [mem_cliquesIn] at hs
    obtain ⟨hsS, hsc, hscl⟩ := hs
    have hm : ∀ a ∈ insert v ls[k].toFinset, a ∈ v :: P := by
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · simp
      · exact List.mem_cons_of_mem _ (hsub a (List.mem_flatten.2 ⟨_, hL, List.mem_toFinset.1 ha⟩))
    have hvs : v ∈ s := by
      by_contra hvs
      have hsub' : s ⊆ ls[k].toFinset := (Finset.subset_insert_iff_of_notMem hvs).1 hsS
      have : s ∈ cliquesIn Adj (q + 2) ls[k].toFinset := by
        rw [mem_cliquesIn]
        exact ⟨hsub', hsc, fun a ha b hb' hab =>
          (hag a (hm a (hsS ha)) b (hm b (hsS hb'))).1 (hscl a ha b hb' hab)⟩
      rw [hfree _ hL] at this
      simp at this
    have herase : s.erase v ⊆ ls[k].toFinset := by
      intro x hx
      obtain ⟨hxv, hxs⟩ := Finset.mem_erase.1 hx
      rcases Finset.mem_insert.1 (hsS hxs) with h | h
      · exact absurd h hxv
      · exact h
    refine ⟨s.erase v, ?_, ?_, herase⟩
    · rw [mem_asetOf]
      refine ⟨bins[k], List.getElem_mem hk', ?_⟩
      rw [mem_cliquesIn]
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        rw [Finset.mem_filter]
        obtain ⟨hxv, hxs⟩ := Finset.mem_erase.1 hx
        refine ⟨?_, hscl v hvs x hxs (Ne.symm hxv)⟩
        rw [hbkk]
        exact herase hx
      · rw [Finset.card_erase_of_mem hvs, hsc]
        omega
      · intro a ha b hb' hab
        exact hscl a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb') hab
    · rw [← Finset.card_pos, Finset.card_erase_of_mem hvs, hsc]
      omega
  choose! f hf using key
  have hpw : List.Pairwise List.Disjoint (ls.filter (fun L => decide (L.length < nSeq A (q + 2)))) :=
    (List.nodup_flatten.1 hnd).2.sublist List.filter_sublist
  have hnd' : ((ls.filter (fun L => decide (L.length < nSeq A (q + 2)))).map f).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    refine hpw.imp_of_mem ?_
    intro L1 L2 h1 h2 hd heq
    obtain ⟨_, hne1, hs1⟩ := hf L1 h1
    obtain ⟨_, _, hs2⟩ := hf L2 h2
    obtain ⟨x, hx⟩ := hne1
    have hx1 := List.mem_toFinset.1 (hs1 hx)
    have hx2 := List.mem_toFinset.1 (hs2 (heq ▸ hx))
    exact hd hx1 hx2
  calc (ls.filter (fun L => decide (L.length < nSeq A (q + 2)))).length
      = ((ls.filter (fun L => decide (L.length < nSeq A (q + 2)))).map f).length := by simp
    _ = ((ls.filter (fun L => decide (L.length < nSeq A (q + 2)))).map f).toFinset.card :=
        (List.toFinset_card_of_nodup hnd').symm
    _ ≤ _ := by
      apply Finset.card_le_card
      intro t ht
      rw [List.mem_toFinset, List.mem_map] at ht
      obtain ⟨L, hL, rfl⟩ := ht
      exact (hf L hL).1

theorem binsRel_mem {bins : List (Finset ℕ × CFState)} {ls : List (List ℕ)}
    (hb : BinsRel A R Adjf q addr bins ls) {b : Finset ℕ × CFState} (h : b ∈ bins) :
    ∃ L ∈ ls, b.1 = L.toFinset := by
  obtain ⟨hl, hbk⟩ := hb
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem h
  have hk' : k < ls.length := hl ▸ hk
  exact ⟨ls[k], List.getElem_mem hk', by rw [hbk k hk hk']; rfl⟩

theorem inv_step_obj (hR : R.Valid) {P : List ℕ} {ls : List (List ℕ)} {as : List Arr}
    {bins : List (Finset ℕ × CFState)} {cs : List Color} {v : ℕ}
    (hI : Inv A R Adjf Adj q addr P ls as (CFState.mk bins (objRun (muOf A q) [] as).1) cs)
    (hb : BinsRel A R Adjf q addr bins ls) (hag : Agree Adjf Adj v P)
    (hrej : ∀ k (hk : k < bins.length), ¬ OkB A q (Adjf v) v bins[k].1)
    (hinc : incOf A q bins = Jof A q) :
    Inv A R Adjf Adj q addr (P ++ [v]) ls
      (as ++ [(R.objColor (addr ++ [1, 0, 0]) v, asetOf (Adjf v) q v bins)])
      (CFState.mk bins (objStep (muOf A q) (R.objColor (addr ++ [1, 0, 0]) v)
        (objRun (muOf A q) [] as).1 (asetOf (Adjf v) q v bins)).1)
      (cs ++ [(addr ++ [1, 0, 0], (objStep (muOf A q) (R.objColor (addr ++ [1, 0, 0]) v)
        (objRun (muOf A q) [] as).1 (asetOf (Adjf v) q v bins)).2)]) := by
  refine { st := ⟨bins, ?_, hb⟩, nodup := hI.nodup,
           sub := fun x hx => List.mem_append_left _ (hI.sub x hx), each := hI.each, inc := hI.inc,
           asg := ?_, aslen := by simpa using hI.aslen, cols := ?_ }
  · rw [objRun_append, objRun_single]
  · intro a ha
    rw [List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact hI.asg a ha
    refine ⟨fun S hS => hR.1 _ _ S hS, ?_, ?_⟩
    · rw [← hinc, incOf_eq hb hI.nodup (fun L hL => (hI.each L hL).1)]
      exact reject_card hb hI.nodup hI.sub (fun L hL => (hI.each L hL).2.2.1) hag hrej
    · intro t ht
      rw [mem_asetOf] at ht
      obtain ⟨b, hbm, ht⟩ := ht
      rw [mem_cliquesIn] at ht
      obtain ⟨L, hL, hbL⟩ := binsRel_mem hb hbm
      refine ⟨ht.2.1, L, hL, ?_⟩
      rw [← hbL]
      exact ht.1.trans (Finset.filter_subset _ _)
  · intro c hc
    rw [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact inColors_mono (grow_refl ls) _ (hI.cols c hc)
    · right
      refine ⟨_, ?_, rfl⟩
      rw [objRun_append, objRun_single]
      simp

theorem flatten_set_perm (v : ℕ) : ∀ (ls : List (List ℕ)) (j : ℕ) (hj : j < ls.length),
    (ls.set j (ls[j] ++ [v])).flatten.Perm (ls.flatten ++ [v])
  | [], _, hj => by simp at hj
  | L :: ls, 0, _ => by
    simp only [List.set_cons_zero, List.flatten_cons, List.getElem_cons_zero, List.append_assoc]
    exact List.Perm.append_left L List.perm_append_comm
  | L :: ls, j + 1, hj => by
    simp only [List.set_cons_succ, List.flatten_cons, List.getElem_cons_succ, List.append_assoc]
    exact List.Perm.append_left L (flatten_set_perm v ls j (by simpa using hj))

theorem grow_set (ls : List (List ℕ)) (j : ℕ) (hj : j < ls.length) (v : ℕ) :
    Grow ls (ls.set j (ls[j] ++ [v])) := by
  intro i hi
  refine ⟨by simpa using hi, ?_⟩
  rw [List.getElem_set]
  split_ifs with h
  · subst h; exact ⟨[v], rfl⟩
  · exact ⟨[], by simp⟩

theorem grow_append (ls : List (List ℕ)) (L : List ℕ) : Grow ls (ls ++ [L]) := by
  intro i hi
  refine ⟨by simp; omega, [], ?_⟩
  rw [List.getElem_append_left hi]
  simp

theorem inv_step_ins {P : List ℕ} {ls : List (List ℕ)} {as : List Arr}
    {bins : List (Finset ℕ × CFState)} {cs : List Color} {v j : ℕ}
    (hI : Inv A R Adjf Adj q addr P ls as (CFState.mk bins (objRun (muOf A q) [] as).1) cs)
    (hb : BinsRel A R Adjf q addr bins ls) (hv : v ∉ P) (hag : Agree Adjf Adj v P)
    (hj : j < bins.length) (hok : OkB A q (Adjf v) v bins[j].1) :
    ∃ ls', Inv A R Adjf Adj q addr (P ++ [v]) ls' as
      (CFState.mk (bins.set j (insert v bins[j].1,
          (cfStep A R (Adjf v) v (q + 2) (addr ++ [0, j, 0]) bins[j].2).1))
        (objRun (muOf A q) [] as).1)
      (cs ++ [(cfStep A R (Adjf v) v (q + 2) (addr ++ [0, j, 0]) bins[j].2).2]) := by
  obtain ⟨hl, hbk⟩ := hb
  have hjl : j < ls.length := hl ▸ hj
  have hbj := hbk j hj hjl
  have hLn : ls[j].Nodup := (List.nodup_flatten.1 hI.nodup).1 _ (List.getElem_mem hjl)
  have hcard : ls[j].toFinset.card = ls[j].length := List.toFinset_card_of_nodup hLn
  rw [hbj] at hok ⊢
  unfold OkB binSt at hok
  unfold binSt
  simp only at hok ⊢
  have hvf : v ∉ ls.flatten := fun h => hv (hI.sub v h)
  have hperm := flatten_set_perm v ls j hjl
  have hg := grow_set ls j hjl v
  refine ⟨ls.set j (ls[j] ++ [v]),
    { st := ⟨_, rfl, ?_, ?_⟩, nodup := ?_, sub := ?_, each := ?_,
      inc := ?_, asg := ?_, aslen := by have := hI.aslen; simp; omega, cols := ?_ }⟩
  · simp [hl]
  · intro i h1 h2
    rw [List.getElem_set, List.getElem_set]
    split_ifs with hij
    · subst hij
      unfold binSt
      rw [cfRun_append, cfRun_single, List.toFinset_append]
      ext x
      · simp
      · rfl
    · exact hbk i (by simpa using h1) (by simpa using h2)
  · rw [hperm.nodup_iff, List.nodup_append]
    exact ⟨hI.nodup, List.nodup_singleton v, fun a ha b hb hab => by
      simp at hb; subst hb; subst hab; exact hvf ha⟩
  · intro x hx
    rcases List.mem_append.1 (hperm.mem_iff.1 hx) with h | h
    · exact List.mem_append_left _ (hI.sub x h)
    · exact List.mem_append_right _ h
  · intro L hL
    rcases List.mem_or_eq_of_mem_set hL with hL | rfl
    · exact hI.each L hL
    have hold := hI.each _ (List.getElem_mem hjl)
    refine ⟨by simp, by simp; omega, ?_, ?_⟩
    · rw [List.toFinset_append]
      have : ls[j].toFinset ∪ [v].toFinset = insert v ls[j].toFinset := by
        ext x; simp
      rw [this, ← hok.2]
      apply cliquesIn_congr
      intro a ha b hb'
      have hm : ∀ a ∈ insert v ls[j].toFinset, a ∈ v :: P := by
        intro a ha
        rcases Finset.mem_insert.1 ha with rfl | ha
        · simp
        · exact List.mem_cons_of_mem _
            (hI.sub a (List.mem_flatten.2 ⟨_, List.getElem_mem hjl, List.mem_toFinset.1 ha⟩))
      exact (hag a (hm a ha) b (hm b hb')).symm
    · rw [cons2_append_single]
      refine ⟨hold.2.2.2, agree_mono hag ?_⟩
      intro x hx
      exact hI.sub x (List.mem_flatten.2 ⟨_, List.getElem_mem hjl, by simpa using hx⟩)
  · have h1 := List.countP_set (p := fun L => decide (L.length < nSeq A (q + 2))) (a := ls[j] ++ [v])
      hjl
    have h2 := hI.inc
    split_ifs at h1 with ha hb1 hb2
    · have := (List.countP_pos_iff (p := fun L => decide (L.length < nSeq A (q + 2)))).2
        ⟨ls[j], List.getElem_mem hjl, ha⟩
      omega
    · omega
    · simp at ha hb2; omega
    · omega
  · intro a ha
    obtain ⟨h1, h2, h3⟩ := hI.asg a ha
    exact ⟨h1, h2, fun t ht => ⟨(h3 t ht).1, grow_mem hg (h3 t ht).2⟩⟩
  · intro c hc
    rw [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · simpa using inColors_mono hg [] (hI.cols c hc)
    · left
      refine ⟨j, by simpa using hjl, ?_⟩
      rw [List.getElem_set_self, cfRun_append, cfRun_single]
      simp

theorem inv_step_new {P : List ℕ} {ls : List (List ℕ)} {as : List Arr}
    {bins : List (Finset ℕ × CFState)} {cs : List Color} {v : ℕ}
    (hI : Inv A R Adjf Adj q addr P ls as (CFState.mk bins (objRun (muOf A q) [] as).1) cs)
    (hb : BinsRel A R Adjf q addr bins ls) (hv : v ∉ P) (hag : Agree Adjf Adj v P)
    (hcap : 2 ≤ nSeq A (q + 2)) (hinc : incOf A q bins ≠ Jof A q) :
    ∃ ls', Inv A R Adjf Adj q addr (P ++ [v]) ls' as
      (CFState.mk (bins ++ [({v},
          (cfStep A R (Adjf v) v (q + 2) (addr ++ [0, bins.length, 0]) (CFState.mk [] [])).1)])
        (objRun (muOf A q) [] as).1)
      (cs ++ [(cfStep A R (Adjf v) v (q + 2) (addr ++ [0, bins.length, 0]) (CFState.mk [] [])).2]) := by
  have hinc' := incOf_eq hb hI.nodup (fun L hL => (hI.each L hL).1)
  obtain ⟨hl, hbk⟩ := hb
  have hvf : v ∉ ls.flatten := fun h => hv (hI.sub v h)
  have hg := grow_append ls [v]
  refine ⟨ls ++ [[v]],
    { st := ⟨_, rfl, ?_, ?_⟩, nodup := ?_, sub := ?_, each := ?_,
      inc := ?_, asg := ?_, aslen := by have := hI.aslen; simp; omega, cols := ?_ }⟩
  · simp [hl]
  · intro i h1 h2
    by_cases hi : i < bins.length
    · rw [List.getElem_append_left hi, List.getElem_append_left (hl ▸ hi)]
      exact hbk i hi (hl ▸ hi)
    · have hi1 : i = bins.length := by simp at h1; omega
      subst hi1
      rw [List.getElem_append_right (le_refl _), List.getElem_append_right (by omega)]
      simp only [Nat.sub_self, List.getElem_cons_zero, hl]
      unfold binSt
      rw [cfRun_single]
      simp
  · rw [List.flatten_append, List.nodup_append]
    refine ⟨hI.nodup, by simp, fun a ha b hb hab => ?_⟩
    simp at hb; subst hb; subst hab; exact hvf ha
  · intro x hx
    rw [List.flatten_append, List.mem_append] at hx
    rcases hx with h | h
    · exact List.mem_append_left _ (hI.sub x h)
    · exact List.mem_append_right _ (by simpa using h)
  · intro L hL
    rw [List.mem_append, List.mem_singleton] at hL
    rcases hL with hL | rfl
    · exact hI.each L hL
    refine ⟨by simp, by simp; omega, ?_, ?_⟩
    · simpa using cliquesIn_singleton (Adj := Adj) q v
    · exact ⟨agree_mono hag (by simp), trivial⟩
  · rw [List.countP_append]
    have h1 := List.countP_le_length (p := fun L => decide (L.length < nSeq A (q + 2))) (l := [[v]])
    have h2 := hI.inc
    simp only [List.length_singleton] at h1
    omega
  · intro a ha
    obtain ⟨h1, h2, h3⟩ := hI.asg a ha
    exact ⟨h1, h2, fun t ht => ⟨(h3 t ht).1, grow_mem hg (h3 t ht).2⟩⟩
  · intro c hc
    rw [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · simpa using inColors_mono hg [] (hI.cols c hc)
    · left
      refine ⟨ls.length, by simp, ?_⟩
      rw [List.getElem_append_right (le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero, cfRun_single]
      simp [hl]

theorem inv_step (hR : R.Valid) (hcap : 2 ≤ nSeq A (q + 2)) {P : List ℕ} {ls : List (List ℕ)}
    {as : List Arr} {s : CFState} {cs : List Color} {v : ℕ}
    (hI : Inv A R Adjf Adj q addr P ls as s cs) (hv : v ∉ P) (hag : Agree Adjf Adj v P) :
    ∃ ls' as', Inv A R Adjf Adj q addr (P ++ [v]) ls' as' (cfStep A R (Adjf v) v (q + 3) addr s).1
      (cs ++ [(cfStep A R (Adjf v) v (q + 3) addr s).2]) := by
  obtain ⟨bins, rfl, hb⟩ := hI.st
  rcases cfStep_cases A R (Adjf v) v q addr bins (objRun (muOf A q) [] as).1 with
    ⟨hrej, hinc, heq⟩ | ⟨j, hj, hok, heq⟩ | ⟨hinc, heq⟩ <;> rw [heq]
  · exact ⟨ls, _, inv_step_obj hR hI hb hag hrej hinc⟩
  · obtain ⟨ls', h⟩ := inv_step_ins hI hb hv hag hj hok
    exact ⟨ls', as, h⟩
  · obtain ⟨ls', h⟩ := inv_step_new hI hb hv hag hcap hinc
    exact ⟨ls', as, h⟩

theorem inv_run (hR : R.Valid) (hcap : 2 ≤ nSeq A (q + 2)) (vs : List ℕ) :
    ∀ (P : List ℕ) (ls : List (List ℕ)) (as : List Arr) (s : CFState) (cs : List Color),
      Inv A R Adjf Adj q addr P ls as s cs → (P ++ vs).Nodup → Cons2 Adjf Adj P vs →
      ∃ ls' as', Inv A R Adjf Adj q addr (P ++ vs) ls' as' (cfRun A R Adjf (q + 3) addr vs s).1
        (cs ++ (cfRun A R Adjf (q + 3) addr vs s).2) := by
  induction vs with
  | nil => intro P ls as s cs hI _ _; exact ⟨ls, as, by simpa [cfRun] using hI⟩
  | cons v vs ih =>
    intro P ls as s cs hI hnd hc
    have hv : v ∉ P := by
      intro h
      exact (List.nodup_append.1 hnd).2.2 v h v List.mem_cons_self rfl
    obtain ⟨ls1, as1, h1⟩ := inv_step hR hcap hI hv hc.1
    obtain ⟨ls2, as2, h2⟩ := ih (P ++ [v]) ls1 as1 _ _ h1 (by simpa using hnd) hc.2
    refine ⟨ls2, as2, ?_⟩
    simpa [cfRun] using h2

end OnlineColoringKYY.Supplement.Dev.T626.PartCF
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartCF
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
/-! ## Arithmetic of `n_r` -/
theorem nSeq_succ3 (A q : ℕ) :
    nSeq A (q + 3) = 6 * A ^ 2 * (6 * (q + 3) * nSeq A (q + 2) ^ (q + 2)) ^ (6 * A ^ 2) := by
  rw [nSeq]

theorem nSeq_ge_two (A : ℕ) (hA : 1 ≤ A) : ∀ q, 2 ≤ nSeq A (q + 2)
  | 0 => by
    show 2 ≤ 2 * A ^ 2
    have := Nat.one_le_pow 2 A hA
    omega
  | q + 1 => by
    have ih := nSeq_ge_two A hA q
    show 2 ≤ nSeq A (q + 3)
    rw [nSeq_succ3]
    have h0 : 0 < 6 * (q + 3) * nSeq A (q + 2) ^ (q + 2) :=
      Nat.mul_pos (by omega) (pow_pos (by omega) _)
    have h1 : 1 ≤ (6 * (q + 3) * nSeq A (q + 2) ^ (q + 2)) ^ (6 * A ^ 2) := Nat.one_le_pow _ _ h0
    have h2 : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ hA
    nlinarith

theorem Jof_mul (A : ℕ) (hA : 1 ≤ A) (q : ℕ) :
    3 * (q + 3) * nSeq A (q + 2) * Jof A q = nSeq A (q + 3) := by
  unfold Jof
  apply Nat.mul_div_cancel'
  rw [nSeq_succ3]
  apply Dvd.dvd.mul_left
  have hX : 3 * (q + 3) * nSeq A (q + 2) ∣ 6 * (q + 3) * nSeq A (q + 2) ^ (q + 2) :=
    ⟨2 * nSeq A (q + 2) ^ (q + 1), by ring⟩
  have h2 : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ hA
  exact hX.trans (dvd_pow_self _ (by omega))

theorem bins_count (c : ℕ) : ∀ ls : List (List ℕ),
    c * ls.length ≤ (ls.map List.length).sum + c * ls.countP (fun L => decide (L.length < c))
  | [] => by simp
  | L :: ls => by
    have ih := bins_count c ls
    simp only [List.length_cons, List.map_cons, List.sum_cons, List.countP_cons]
    split_ifs with h
    · nlinarith
    · simp at h
      nlinarith

/-! ## The case `r = 2` -/
theorem cfRun_two (A : ℕ) (R : Resolver) (Adjf : ℕ → ℕ → ℕ → Prop) (addr : List ℕ) :
    ∀ (vs : List ℕ) (s : CFState), ∀ c ∈ (cfRun A R Adjf 2 addr vs s).2, c = (addr, 0)
  | [], s => by simp [cfRun]
  | v :: vs, s => by
    intro c hc
    simp only [cfRun, List.mem_cons] at hc
    rcases hc with rfl | hc
    · cases s; rfl
    · exact cfRun_two A R Adjf addr vs _ c hc

/-! ## The case `r = q + 3`: counting -/
theorem cf_step (A : ℕ) (hA : 1 ≤ A) (R : Resolver) (hR : R.Valid) (Adjf : ℕ → ℕ → ℕ → Prop)
    (Adj : ℕ → ℕ → Prop) (q : ℕ)
    (ih : ∀ addr vs : List ℕ, vs.Nodup → vs.length ≤ nSeq A (q + 2) → Cons2 Adjf Adj [] vs →
      ((cfRun A R Adjf (q + 2) addr vs (CFState.mk [] [])).2.toFinset.card : ℝ) ≤
        (((q + 2 : ℕ) : ℝ) - 1) / (2 * (A : ℝ) ^ 2) * (nSeq A (q + 2) : ℝ))
    (addr vs : List ℕ) (hnd : vs.Nodup) (hlen : vs.length ≤ nSeq A (q + 3))
    (hc : Cons2 Adjf Adj [] vs) :
    ((cfRun A R Adjf (q + 3) addr vs (CFState.mk [] [])).2.toFinset.card : ℝ) ≤
      (((q + 3 : ℕ) : ℝ) - 1) / (2 * (A : ℝ) ^ 2) * (nSeq A (q + 3) : ℝ) := by
  have hcap := nSeq_ge_two A hA q
  have hI0 : Inv A R Adjf Adj q addr [] [] [] (CFState.mk [] []) [] := by
    refine { st := ⟨[], rfl, by simp [BinsRel]⟩, nodup := by simp, sub := by simp,
             each := by simp, inc := by simp, asg := by simp, aslen := by simp, cols := by simp }
  obtain ⟨ls, as, hI⟩ := inv_run hR hcap vs [] [] [] _ [] hI0 (by simpa using hnd) hc
  rw [List.nil_append, List.nil_append] at hI
  -- per-bin bound
  have hbin : ∀ j ∈ Finset.range ls.length,
      (((cfRun A R Adjf (q + 2) (addr ++ [0, j, 0]) (ls.getD j []) (CFState.mk [] [])).2.toFinset.card
        : ℕ) : ℝ) ≤ (((q + 2 : ℕ) : ℝ) - 1) / (2 * (A : ℝ) ^ 2) * (nSeq A (q + 2) : ℝ) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [List.getD_eq_getElem _ _ hj]
    have hm := List.getElem_mem hj
    obtain ⟨_, hl, _, hc2⟩ := hI.each _ hm
    exact ih _ _ ((List.nodup_flatten.1 hI.nodup).1 _ hm) hl hc2
  -- the color set
  have hsub : (cfRun A R Adjf (q + 3) addr vs (CFState.mk [] [])).2.toFinset ⊆
      (Finset.range ls.length).biUnion (fun j =>
        (cfRun A R Adjf (q + 2) (addr ++ [0, j, 0]) (ls.getD j []) (CFState.mk [] [])).2.toFinset) ∪
      (objRun (muOf A q) [] as).2.toFinset.image (fun x => (addr ++ [1, 0, 0], x)) := by
    intro c hc
    rw [List.mem_toFinset] at hc
    rcases hI.cols c hc with ⟨j, hj, hcj⟩ | ⟨x, hx, rfl⟩
    · apply Finset.mem_union_left
      rw [Finset.mem_biUnion]
      refine ⟨j, Finset.mem_range.2 hj, ?_⟩
      rw [List.getD_eq_getElem _ _ hj, List.mem_toFinset]
      exact hcj
    · apply Finset.mem_union_right
      rw [Finset.mem_image]
      exact ⟨x, List.mem_toFinset.2 hx, rfl⟩
  have hcard : (cfRun A R Adjf (q + 3) addr vs (CFState.mk [] [])).2.toFinset.card ≤
      ∑ j ∈ Finset.range ls.length,
        (cfRun A R Adjf (q + 2) (addr ++ [0, j, 0]) (ls.getD j []) (CFState.mk [] [])).2.toFinset.card +
      (objRun (muOf A q) [] as).2.toFinset.card :=
    (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add Finset.card_biUnion_le Finset.card_image_le))
  have hSb : ((∑ j ∈ Finset.range ls.length,
        (cfRun A R Adjf (q + 2) (addr ++ [0, j, 0]) (ls.getD j []) (CFState.mk [] [])).2.toFinset.card
          : ℕ) : ℝ) ≤
      (ls.length : ℝ) * ((((q + 2 : ℕ) : ℝ) - 1) / (2 * (A : ℝ) ^ 2) * (nSeq A (q + 2) : ℝ)) := by
    rw [Nat.cast_sum]
    calc _ ≤ ∑ j ∈ Finset.range ls.length,
          ((((q + 2 : ℕ) : ℝ) - 1) / (2 * (A : ℝ) ^ 2) * (nSeq A (q + 2) : ℝ)) :=
          Finset.sum_le_sum hbin
      _ = _ := by simp
  -- object coloring
  have hcap1 : (1 : ℝ) ≤ (nSeq A (q + 2) : ℝ) := by exact_mod_cast (by omega : 1 ≤ nSeq A (q + 2))
  have hpow1 : (1 : ℝ) ≤ (nSeq A (q + 2) : ℝ) ^ (q + 2) := one_le_pow₀ hcap1
  have hμ1 : 1 ≤ muOf A q := by
    simp only [muOf]
    push_cast
    nlinarith
  have hJmul : (3 * ((q : ℝ) + 3) * (nSeq A (q + 2) : ℝ) * (Jof A q : ℝ)) = (nSeq A (q + 3) : ℝ) := by
    exact_mod_cast Jof_mul A hA q
  have hU : ((as.map Prod.snd).foldr (· ∪ ·) ∅).card ≤ vs.length * nSeq A (q + 2) ^ q := by
    have hsub2 : (as.map Prod.snd).foldr (· ∪ ·) ∅ ⊆
        ls.foldr (fun L acc => L.toFinset.powersetCard (q + 1) ∪ acc) ∅ := by
      intro t ht
      rw [mem_foldr_union] at ht
      obtain ⟨s, hs, ht⟩ := ht
      rw [List.mem_map] at hs
      obtain ⟨a, ha, rfl⟩ := hs
      obtain ⟨hc1, L, hL, htL⟩ := (hI.asg a ha).2.2 t ht
      rw [mem_foldr_union']
      exact ⟨L, hL, Finset.mem_powersetCard.2 ⟨htL, hc1⟩⟩
    calc _ ≤ _ := Finset.card_le_card hsub2
      _ ≤ (ls.map (fun L => (L.toFinset.powersetCard (q + 1)).card)).sum := card_foldr_union_le _ _
      _ ≤ (ls.map (fun L => L.length * nSeq A (q + 2) ^ q)).sum := by
          apply List.sum_le_sum
          intro L hL
          rw [Finset.card_powersetCard]
          have h1 := List.toFinset_card_le L
          have h2 := (hI.each L hL).2.1
          calc L.toFinset.card.choose (q + 1) ≤ L.toFinset.card ^ (q + 1) := Nat.choose_le_pow _ _
            _ = L.toFinset.card * L.toFinset.card ^ q := by ring
            _ ≤ L.length * nSeq A (q + 2) ^ q :=
                Nat.mul_le_mul h1 (Nat.pow_le_pow_left (h1.trans h2) q)
      _ = (ls.map List.length).sum * nSeq A (q + 2) ^ q := List.sum_map_mul_right _ _ _
      _ = ls.flatten.length * nSeq A (q + 2) ^ q := by rw [List.length_flatten]
      _ ≤ vs.length * nSeq A (q + 2) ^ q :=
          Nat.mul_le_mul_right _ ((hI.nodup.subperm (fun x hx => hI.sub x hx)).length_le)
  have hsize : ∀ a ∈ as,
      (((as.map Prod.snd).foldr (· ∪ ·) ∅).card : ℝ) ≤ muOf A q * (a.2.card : ℝ) := by
    intro a ha
    have hJa : (Jof A q : ℝ) ≤ (a.2.card : ℝ) := by exact_mod_cast (hI.asg a ha).2.1
    have hU' : (((as.map Prod.snd).foldr (· ∪ ·) ∅).card : ℝ) ≤
        (vs.length : ℝ) * (nSeq A (q + 2) : ℝ) ^ q := by exact_mod_cast hU
    have hlen' : (vs.length : ℝ) ≤ (nSeq A (q + 3) : ℝ) := by exact_mod_cast hlen
    have hpq : (0 : ℝ) ≤ (nSeq A (q + 2) : ℝ) ^ q := by positivity
    have hc2 : (nSeq A (q + 2) : ℝ) * (nSeq A (q + 2) : ℝ) ^ q ≤ (nSeq A (q + 2) : ℝ) ^ (q + 2) := by
      rw [← pow_succ']
      exact pow_le_pow_right₀ hcap1 (by omega)
    have hJ0 : (0 : ℝ) ≤ (Jof A q : ℝ) := by positivity
    have hμ0 : 0 ≤ muOf A q := by linarith
    calc (((as.map Prod.snd).foldr (· ∪ ·) ∅).card : ℝ)
        ≤ (vs.length : ℝ) * (nSeq A (q + 2) : ℝ) ^ q := hU'
      _ ≤ (nSeq A (q + 3) : ℝ) * (nSeq A (q + 2) : ℝ) ^ q := mul_le_mul_of_nonneg_right hlen' hpq
      _ ≤ muOf A q * (Jof A q : ℝ) := by
          rw [← hJmul]
          simp only [muOf]
          push_cast
          have h3 : (0 : ℝ) ≤ 3 * ((q : ℝ) + 3) * (Jof A q : ℝ) := by positivity
          have := mul_le_mul_of_nonneg_left hc2 h3
          nlinarith
      _ ≤ muOf A q * (a.2.card : ℝ) := mul_le_mul_of_nonneg_left hJa hμ0
  have hpick : ∀ a ∈ as, ∀ S : Finset ℕ, S.Nonempty → a.1 S ∈ S := fun a ha => (hI.asg a ha).1
  have hh : 1 ≤ 6 * A ^ 2 := by
    have := Nat.one_le_pow 2 A hA
    omega
  have hobj := obj_colors_le (muOf A q) hμ1 as hpick hsize (6 * A ^ 2) hh
  -- final arithmetic
  have hA2 : (1 : ℝ) ≤ (A : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
    nlinarith
  have hX : 2 * muOf A q = 6 * ((q : ℝ) + 3) * (nSeq A (q + 2) : ℝ) ^ (q + 2) := by
    simp only [muOf]; push_cast; ring
  have hNX : (nSeq A (q + 3) : ℝ) = 6 * (A : ℝ) ^ 2 * (2 * muOf A q) ^ (6 * A ^ 2) := by
    rw [hX, nSeq_succ3]; push_cast; ring
  have hXle : (2 * muOf A q) ^ (6 * A ^ 2 - 1) ≤ (2 * muOf A q) ^ (6 * A ^ 2) :=
    pow_le_pow_right₀ (by linarith) (Nat.sub_le _ _)
  have hcL : (nSeq A (q + 2) : ℝ) * (ls.length : ℝ) ≤
      (vs.length : ℝ) + (nSeq A (q + 2) : ℝ) * (Jof A q : ℝ) := by
    have h1 := bins_count (nSeq A (q + 2)) ls
    have h2 : (ls.map List.length).sum ≤ vs.length := by
      rw [← List.length_flatten]
      exact (hI.nodup.subperm (fun x hx => hI.sub x hx)).length_le
    have h3 := hI.inc
    have h4 : nSeq A (q + 2) * ls.length ≤ vs.length + nSeq A (q + 2) * Jof A q := by
      have := Nat.mul_le_mul_left (nSeq A (q + 2)) h3
      omega
    exact_mod_cast h4
  have hlen' : (vs.length : ℝ) ≤ (nSeq A (q + 3) : ℝ) := by exact_mod_cast hlen
  have hasl : (as.length : ℝ) ≤ (vs.length : ℝ) := by exact_mod_cast hI.aslen
  have hD : (0 : ℝ) < 2 * (A : ℝ) ^ 2 := by linarith
  set Y := (2 * muOf A q) ^ (6 * A ^ 2) with hY
  set c := (nSeq A (q + 2) : ℝ) with hcdef
  set N := (nSeq A (q + 3) : ℝ) with hNdef
  set a2 := (A : ℝ) ^ 2 with ha2
  set L := (ls.length : ℝ) with hLdef
  set J := (Jof A q : ℝ) with hJdef
  have hobj' : ((objRun (muOf A q) [] as).2.toFinset.card : ℝ) ≤ (as.length : ℝ) / (6 * a2) + Y := by
    have : ((6 * A ^ 2 : ℕ) : ℝ) = 6 * a2 := by push_cast; rfl
    rw [this] at hobj
    linarith
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hJ0 : (0 : ℝ) ≤ J := by positivity
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have key : (L * (((q : ℝ) + 1) / (2 * a2) * c) + ((as.length : ℝ) / (6 * a2) + Y)) * (2 * a2) ≤
      ((q : ℝ) + 2) * N := by
    have e : (L * (((q : ℝ) + 1) / (2 * a2) * c) + ((as.length : ℝ) / (6 * a2) + Y)) * (2 * a2) =
        ((q : ℝ) + 1) * (c * L) + (as.length : ℝ) / 3 + 2 * a2 * Y := by
      field_simp
      ring
    rw [e]
    have h1 := mul_le_mul_of_nonneg_left hcL (by linarith : (0 : ℝ) ≤ (q : ℝ) + 1)
    have h2 := mul_le_mul_of_nonneg_left hlen' (by linarith : (0 : ℝ) ≤ (q : ℝ) + 1)
    have h3 : ((q : ℝ) + 1) * (c * J) ≤ ((q : ℝ) + 3) * (c * J) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith
  have htot : ((cfRun A R Adjf (q + 3) addr vs (CFState.mk [] [])).2.toFinset.card : ℝ) ≤
      L * (((q : ℝ) + 1) / (2 * a2) * c) + ((as.length : ℝ) / (6 * a2) + Y) := by
    have h1 : ((cfRun A R Adjf (q + 3) addr vs (CFState.mk [] [])).2.toFinset.card : ℝ) ≤
        ((∑ j ∈ Finset.range ls.length,
          (cfRun A R Adjf (q + 2) (addr ++ [0, j, 0]) (ls.getD j []) (CFState.mk [] [])).2.toFinset.card
            : ℕ) : ℝ) + ((objRun (muOf A q) [] as).2.toFinset.card : ℝ) := by
      exact_mod_cast hcard
    have h2 : (((q + 2 : ℕ) : ℝ) - 1) = (q : ℝ) + 1 := by push_cast; ring
    rw [h2] at hSb
    linarith
  have hfin : ((((q + 3 : ℕ) : ℝ) - 1) / (2 * a2) * N) = ((q : ℝ) + 2) * N / (2 * a2) := by
    push_cast; ring
  rw [hfin, le_div_iff₀ hD]
  calc _ ≤ (L * (((q : ℝ) + 1) / (2 * a2) * c) + ((as.length : ℝ) / (6 * a2) + Y)) * (2 * a2) :=
        mul_le_mul_of_nonneg_right htot hD.le
    _ ≤ _ := key

theorem cf_gen (A : ℕ) (hA : 1 ≤ A) (R : Resolver) (hR : R.Valid) (Adjf : ℕ → ℕ → ℕ → Prop)
    (Adj : ℕ → ℕ → Prop) : ∀ q : ℕ, ∀ addr vs : List ℕ, vs.Nodup → vs.length ≤ nSeq A (q + 2) →
      Cons2 Adjf Adj [] vs →
      ((cfRun A R Adjf (q + 2) addr vs (CFState.mk [] [])).2.toFinset.card : ℝ) ≤
        (((q + 2 : ℕ) : ℝ) - 1) / (2 * (A : ℝ) ^ 2) * (nSeq A (q + 2) : ℝ)
  | 0 => by
    intro addr vs _ _ _
    have h1 : (cfRun A R Adjf 2 addr vs (CFState.mk [] [])).2.toFinset.card ≤ 1 := by
      apply Finset.card_le_one.2
      intro a ha b hb
      rw [List.mem_toFinset] at ha hb
      rw [cfRun_two A R Adjf addr vs _ a ha, cfRun_two A R Adjf addr vs _ b hb]
    have hA2 : (0 : ℝ) < (A : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
      positivity
    have h2 : (((0 + 2 : ℕ) : ℝ) - 1) / (2 * (A : ℝ) ^ 2) * (nSeq A (0 + 2) : ℝ) = 1 := by
      show (((0 + 2 : ℕ) : ℝ) - 1) / (2 * (A : ℝ) ^ 2) * ((2 * A ^ 2 : ℕ) : ℝ) = 1
      push_cast
      field_simp
      ring
    rw [h2]
    exact_mod_cast h1
  | q + 1 => fun addr vs hnd hlen hc =>
    cf_step A hA R hR Adjf Adj q (cf_gen A hA R hR Adjf Adj q) addr vs hnd hlen hc

/-- Paper's Lemma 6.4, for any run of at most `n_r` vertices of an `r`-clique-free set. -/
theorem cf_colors_le (A : ℕ) (hA : 1 ≤ A) (R : Resolver) (hR : R.Valid) (r : ℕ) (hr : 2 ≤ r)
    (Adjf : ℕ → ℕ → ℕ → Prop) (Adj : ℕ → ℕ → Prop) (hsymm : ∀ a b, Adj a b → Adj b a)
    (addr : List ℕ) (vs : List ℕ) (hnd : vs.Nodup) (hlen : vs.length ≤ nSeq A r)
    (hfree : cliquesIn Adj r vs.toFinset = ∅) (hcons : Consistent Adjf Adj vs) :
    ((cfRun A R Adjf r addr vs (CFState.mk [] [])).2.toFinset.card : ℝ) ≤
      ((r : ℝ) - 1) / (2 * (A : ℝ) ^ 2) * (nSeq A r : ℝ) := by
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 2 := ⟨r - 2, by omega⟩
  exact cf_gen A hA R hR Adjf Adj q addr vs hnd hlen
    (cons2_of_consistent vs [] (by simpa using hcons))

end OnlineColoringKYY.Supplement.Dev.T626.PartCF
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626
open Classical OnlineColoringKYY.Supplement
alias cf_colors_le := OnlineColoringKYY.Supplement.Dev.T626.PartCF.cf_colors_le

end OnlineColoringKYY.Supplement.Dev.T626
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartOC
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
/-! ## Corollary 6.5 -/
lemma nSeq_pos (A : ℕ) (hA : 1 ≤ A) : ∀ r, 2 ≤ r → 1 ≤ nSeq A r
  | 0, h => by omega
  | 1, h => by omega
  | 2, _ => by
    simp only [nSeq]
    have : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ hA
    omega
  | (q + 3), _ => by
    have ih := nSeq_pos A hA (q + 2) (by omega)
    simp only [nSeq]
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) (pow_pos hA 2))
      (pow_pos (Nat.mul_pos (by omega) (pow_pos ih _)) _)

lemma cliquesIn_mono (Adj : ℕ → ℕ → Prop) (r : ℕ) (S T : Finset ℕ) (hST : S ⊆ T)
    (h : cliquesIn Adj r T = ∅) : cliquesIn Adj r S = ∅ := by
  apply Finset.subset_empty.1
  rw [← h]
  exact Finset.filter_subset_filter _ (Finset.powerset_mono.2 hST)

lemma consistent_take (Adjf : ℕ → ℕ → ℕ → Prop) (Adj : ℕ → ℕ → Prop) (vs : List ℕ) (n : ℕ)
    (h : Consistent Adjf Adj vs) : Consistent Adjf Adj (vs.take n) := by
  intro i hi a ha b hb
  have hi2 : i < n ∧ i < vs.length := by simpa using hi
  have hi' : i < vs.length := hi2.2
  rw [List.take_take, Nat.min_eq_left (by omega)] at ha hb
  have hg : (vs.take n).get ⟨i, hi⟩ = vs.get ⟨i, hi'⟩ := by simp
  rw [hg]; exact h i hi' a ha b hb

lemma consistent_drop (Adjf : ℕ → ℕ → ℕ → Prop) (Adj : ℕ → ℕ → Prop) (vs : List ℕ) (n : ℕ)
    (h : Consistent Adjf Adj vs) : Consistent Adjf Adj (vs.drop n) := by
  intro i hi a ha b hb
  have hi' : n + i < vs.length := by simp at hi; omega
  rw [List.take_drop] at ha hb
  have hg : (vs.drop n).get ⟨i, hi⟩ = vs.get ⟨n + i, hi'⟩ := by simp
  rw [hg]
  exact h (n + i) hi' a (List.mem_of_mem_drop ha) b (List.mem_of_mem_drop hb)

lemma c65Run_append (A : ℕ) (R : Resolver) (Adjf : ℕ → ℕ → ℕ → Prop) (addr : List ℕ) :
    ∀ (xs ys : List ℕ) (st : ℕ × CFState),
    (c65Run A R Adjf addr (xs ++ ys) st).2 =
      (c65Run A R Adjf addr xs st).2 ++
        (c65Run A R Adjf addr ys (c65Run A R Adjf addr xs st).1).2
  | [], ys, st => by simp [c65Run]
  | x :: xs, ys, st => by
    simp only [List.cons_append, c65Run, c65Run_append A R Adjf addr xs ys, List.cons_append]

lemma c65Run_cnt (A : ℕ) (R : Resolver) (Adjf : ℕ → ℕ → ℕ → Prop) (addr : List ℕ) :
    ∀ (xs : List ℕ) (st : ℕ × CFState),
    (c65Run A R Adjf addr xs st).1.1 = st.1 + xs.length
  | [], st => by simp [c65Run]
  | x :: xs, (cnt, s) => by
    simp only [c65Run, c65Run_cnt A R Adjf addr xs, List.length_cons]
    simp only [c65Step]
    omega

lemma c65Run_block (A : ℕ) (R : Resolver) (Adjf : ℕ → ℕ → ℕ → Prop) (addr : List ℕ)
    (hN : 0 < nSeq A (A + 1)) (k : ℕ) :
    ∀ (ws : List ℕ) (i : ℕ) (s : CFState), i < nSeq A (A + 1) →
    i + ws.length ≤ nSeq A (A + 1) →
    (c65Run A R Adjf addr ws (k * nSeq A (A + 1) + i, s)).2 =
      (cfRun A R Adjf (A + 1) (addr ++ [7, k, 0]) ws
        (if i = 0 then CFState.mk [] [] else s)).2
  | [], i, s, _, _ => by simp [c65Run, cfRun]
  | w :: ws, i, s, hi, hl => by
    have hdiv : (k * nSeq A (A + 1) + i) / nSeq A (A + 1) = k := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt hi, zero_add]
    have hmod : (k * nSeq A (A + 1) + i) % nSeq A (A + 1) = i := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
    simp only [c65Run, cfRun, c65Step, hdiv, hmod]
    congr 1
    rcases ws with _ | ⟨w', ws'⟩
    · simp [c65Run, cfRun]
    · simp only [List.length_cons] at hl
      rw [show k * nSeq A (A + 1) + i + 1 = k * nSeq A (A + 1) + (i + 1) by omega,
        c65Run_block A R Adjf addr hN k (w' :: ws') (i + 1) _ (by omega)
          (by simp only [List.length_cons]; omega)]
      simp

lemma c65_aux (A : ℕ) (hA : 1 ≤ A) (R : Resolver) (hR : R.Valid) (Adjf : ℕ → ℕ → ℕ → Prop)
    (Adj : ℕ → ℕ → Prop) (hsymm : ∀ a b, Adj a b → Adj b a) (addr : List ℕ) :
    ∀ (m : ℕ) (vs : List ℕ) (k : ℕ) (s : CFState),
    vs.Nodup → vs.length ≤ m * nSeq A (A + 1) → cliquesIn Adj (A + 1) vs.toFinset = ∅ →
    Consistent Adjf Adj vs →
    ((c65Run A R Adjf addr vs (k * nSeq A (A + 1), s)).2.toFinset.card : ℝ) ≤
      m * ((((A + 1 : ℕ) : ℝ) - 1) / (2 * (A : ℝ) ^ 2) * (nSeq A (A + 1) : ℝ))
  | 0, vs, k, s, _, hl, _, _ => by
    have : vs = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst this
    simp [c65Run]
  | m + 1, vs, k, s, hnd, hl, hfree, hcons => by
    have hN : 0 < nSeq A (A + 1) := nSeq_pos A hA (A + 1) (by omega)
    set N := nSeq A (A + 1) with hNdef
    have e := c65Run_append A R Adjf addr (vs.take N) (vs.drop N) (k * N, s)
    rw [List.take_append_drop] at e
    rw [e, List.toFinset_append]
    -- first block
    have hblk := c65Run_block A R Adjf addr hN k (vs.take N) 0 s hN
      (by rw [zero_add, List.length_take]; exact Nat.min_le_left _ _)
    simp only [add_zero, if_true] at hblk
    have hfirst : (((c65Run A R Adjf addr (vs.take N) (k * N, s)).2.toFinset.card : ℕ) : ℝ) ≤
        (((A + 1 : ℕ) : ℝ) - 1) / (2 * (A : ℝ) ^ 2) * (N : ℝ) := by
      rw [hblk]
      exact cf_colors_le A hA R hR (A + 1) (by omega) Adjf Adj hsymm (addr ++ [7, k, 0])
        (vs.take N) (hnd.sublist (List.take_sublist _ _))
        (by rw [List.length_take]; exact Nat.min_le_left _ _)
        (cliquesIn_mono Adj _ _ _ (fun x hx => by
          rw [List.mem_toFinset] at hx ⊢; exact List.mem_of_mem_take hx) hfree)
        (consistent_take Adjf Adj vs N hcons)
    have hcard := Finset.card_union_le (c65Run A R Adjf addr (vs.take N) (k * N, s)).2.toFinset
      (c65Run A R Adjf addr (vs.drop N) (c65Run A R Adjf addr (vs.take N) (k * N, s)).1).2.toFinset
    have hcardR : (((c65Run A R Adjf addr (vs.take N) (k * N, s)).2.toFinset ∪
        (c65Run A R Adjf addr (vs.drop N)
          (c65Run A R Adjf addr (vs.take N) (k * N, s)).1).2.toFinset).card : ℝ) ≤
        ((c65Run A R Adjf addr (vs.take N) (k * N, s)).2.toFinset.card : ℝ) +
        ((c65Run A R Adjf addr (vs.drop N)
          (c65Run A R Adjf addr (vs.take N) (k * N, s)).1).2.toFinset.card : ℝ) := by
      exact_mod_cast hcard
    refine hcardR.trans ?_
    by_cases hd : vs.drop N = []
    · rw [hd]
      simp only [c65Run, List.toFinset_nil, Finset.card_empty, Nat.cast_zero, add_zero]
      push_cast at hfirst ⊢
      have : (0 : ℝ) ≤ m * ((A + 1 - 1) / (2 * (A : ℝ) ^ 2) * (N : ℝ)) := by
        have : (0:ℝ) ≤ (A + 1 - 1) / (2 * (A : ℝ) ^ 2) * (N : ℝ) := by
          rw [add_sub_cancel_right]; positivity
        positivity
      nlinarith
    · have hlt : N < vs.length := by
        by_contra hc
        exact hd (List.drop_eq_nil_of_le (by omega))
      have hst : (c65Run A R Adjf addr (vs.take N) (k * N, s)).1 =
          ((k + 1) * N, (c65Run A R Adjf addr (vs.take N) (k * N, s)).1.2) := by
        refine Prod.ext ?_ rfl
        rw [c65Run_cnt, List.length_take, Nat.min_eq_left hlt.le]
        ring
      rw [hst]
      have hl' : (vs.drop N).length ≤ m * N := by
        rw [List.length_drop]
        have : vs.length ≤ m * N + N := by rw [add_mul, one_mul] at hl; exact hl
        generalize m * N = t at *
        omega
      have ih := c65_aux A hA R hR Adjf Adj hsymm addr m (vs.drop N) (k + 1)
        (c65Run A R Adjf addr (vs.take N) (k * N, s)).1.2
        (hnd.sublist (List.drop_sublist _ _)) hl'
        (cliquesIn_mono Adj _ _ _ (fun x hx => by
          rw [List.mem_toFinset] at hx ⊢; exact List.mem_of_mem_drop hx) hfree)
        (consistent_drop Adjf Adj vs N hcons)
      push_cast at hfirst ih ⊢
      linarith

/-- Corollary 6.5 (core): with `A ≥ 1` and `n_{A+1} ≤ L`, a bin of at most `L` vertices that is
`(A+1)`-clique-free uses at most `L/A` colors. -/
theorem c65_colors_le (A L : ℕ) (hA : 1 ≤ A) (hL : nSeq A (A + 1) ≤ L) (R : Resolver)
    (hR : R.Valid) (Adjf : ℕ → ℕ → ℕ → Prop) (Adj : ℕ → ℕ → Prop)
    (hsymm : ∀ a b, Adj a b → Adj b a) (addr : List ℕ) (vs : List ℕ) (hnd : vs.Nodup)
    (hlen : vs.length ≤ L) (hfree : cliquesIn Adj (A + 1) vs.toFinset = ∅)
    (hcons : Consistent Adjf Adj vs) :
    ((c65Run A R Adjf addr vs (0, CFState.mk [] [])).2.toFinset.card : ℝ) ≤ (L : ℝ) / A := by
  have hN : 0 < nSeq A (A + 1) := nSeq_pos A hA (A + 1) (by omega)
  set N := nSeq A (A + 1) with hNdef
  set m := L / N + 1 with hm
  have hlt : L < L / N * N + N := Nat.lt_div_mul_add hN
  have hmN : m * N ≤ 2 * L := by
    have := Nat.div_mul_le_self L N
    rw [hm, add_mul, one_mul]; omega
  have hlen' : vs.length ≤ m * N := by rw [hm, add_mul, one_mul]; omega
  have key := c65_aux A hA R hR Adjf Adj hsymm addr m vs 0 (CFState.mk [] []) hnd hlen' hfree hcons
  rw [zero_mul] at key
  refine key.trans ?_
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  have hmNR : (m : ℝ) * N ≤ 2 * L := by exact_mod_cast hmN
  push_cast
  rw [add_sub_cancel_right]
  have e : (m : ℝ) * ((A : ℝ) / (2 * (A : ℝ) ^ 2) * (N : ℝ)) = ((m : ℝ) * N) / (2 * A) := by
    field_simp
  rw [e, div_le_div_iff₀ (by positivity) hA']
  nlinarith

end OnlineColoringKYY.Supplement.Dev.T626.PartOC
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626
open Classical OnlineColoringKYY.Supplement
alias c65_colors_le := OnlineColoringKYY.Supplement.Dev.T626.PartOC.c65_colors_le

/-!
Blueprint layer 2 for Theorem 6.26 (q414): the analysis of LOC / LOC′ / CB (Sections 6.5–6.11).

An instance of mode `m` at address `addr` receives inputs `(v, 𝒞(v))` with strictly increasing
vertices; at `v` it sees the adjacency `AdjAt Adj v` (the fixed symmetric `Adj` restricted to
vertices `≤ v`). `instRun` is its run from `Inst.fresh`. A run is *live* if no output occurs
before the last input (a parent never feeds a terminated instance).

`Summary` of a live run with good inputs: there are numbers `nb` (bins created inside, at every
depth), `ext` (extra colors of LOC′ terminations) and a list `sizes` (the number of inputs of each
LOC instance inside, including the instance itself if it is a LOC) with
* colors ≤ (L/M)·nb + ext                                   (Corollary 6.5 per bin),
* nb ≤ #inputs/L + ownBins m + Σ_{x ∈ sizes} 8·x^{1−1/M^{10}}  (Lemma 6.25),
* ext ≤ |sizes| + ownExt m, |sizes| ≤ cntOf m (Lemmas 6.14, 6.23, 6.24), Σ sizes ≤ #inputs·depOf m,
* the output, if any, satisfies `OutOK` (Lemmas 6.15–6.18: certificate sizes `fB`, `gB`).
-/
def AdjAt (Adj : ℕ → ℕ → Prop) (v a b : ℕ) : Prop := a ≤ v ∧ b ≤ v ∧ Adj a b

noncomputable def instRun (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (m : Mode)
    (addr : List ℕ) : List (ℕ × Finset (Finset ℕ)) → Inst → Inst × List Color × List (Option Out)
  | [], s => (s, [], [])
  | x :: xs, s =>
    let r := locStep P R (AdjAt Adj x.1) x.1 m addr x.2 s
    let y := instRun P R Adj m addr xs r.1
    (y.1, r.2.1 :: y.2.1, r.2.2 :: y.2.2)

/-- No output before the last step. -/
def Live (outs : List (Option Out)) : Prop := ∀ o ∈ outs.dropLast, o = none

/-- `J` of Algorithm 5 for `LOC′(k)` on `n` vertices. -/
noncomputable def Jof (P : LocParams) (k n : ℕ) : ℕ :=
  max 1 ⌊(n : ℝ) / max (P.L : ℝ) ((n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ 5))⌋₊

/-- `ν` of Algorithm 5 for `LOC′(k)` on `n` vertices. -/
noncomputable def nuOf (P : LocParams) (k n : ℕ) : ℝ :=
  2 * (n : ℝ) * (P.L : ℝ) ^ (P.M - 1) / (Jof P k n : ℝ)

/-- `g_{k,ℓ}` (Lemmas 6.17, 6.18), given `f` on smaller indices. -/
def gB (M k : ℕ) (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => (M + 1) * f (k - M)
  | ℓ + 1 => if ℓ + 1 ≤ M then (M + 1) * f (k - M) else f (k - (ℓ + 1)) * (gB M k f ℓ + 1)

/-- `f_k` (Lemmas 6.15, 6.16). -/
def fB (M : ℕ) (k : ℕ) : ℕ :=
  if k ≤ M then M + 1 else gB M k (fun j => if _h : j < k then fB M j else 0) k
termination_by k
decreasing_by all_goals assumption

/-- Instance-count bound for CB(k, ℓ, ·) given the bound `fL` for LOC on smaller indices. -/
noncomputable def cC (M : ℕ) (W F : ℝ) (k : ℕ) (fL : ℕ → ℝ) : ℕ → ℝ
  | 0 => fL (k - M)
  | ℓ + 1 => if ℓ + 1 ≤ M then fL (k - M)
      else 3 * W * fL (k - (ℓ + 1)) + 3 * W * F * cC M W F k fL ℓ

/-- Instance-count bound for LOC(k) (`lg` bounds `log₂` of the number of inputs). -/
noncomputable def cL (M : ℕ) (W F lg : ℝ) (k : ℕ) : ℝ :=
  if k ≤ M then 1 else 1 + (lg + 1) * cC M W F k (fun j => if _h : j < k then cL M W F lg j else 0) k
termination_by k
decreasing_by all_goals assumption

noncomputable def cntOf (M : ℕ) (W F lg : ℝ) : Mode → ℝ
  | .loc k => cL M W F lg k
  | .locP k _ => if k ≤ M then 0 else cC M W F k (fun j => if _h : j < k then cL M W F lg j else 0) k
  | .cb k ℓ _ => cC M W F k (fun j => if _h : j < k then cL M W F lg j else 0) ℓ

def depOf (M : ℕ) : Mode → ℕ
  | .loc k => k / M + 1
  | .locP k _ => k / M
  | .cb k _ _ => k / M

noncomputable def ownBins (P : LocParams) : Mode → ℝ
  | .locP k n => if k ≤ P.M then 1 else (Jof P k n : ℝ)
  | _ => 0

def ownExt : Mode → ℕ
  | .locP _ _ => 1
  | _ => 0

/-- The vertices of the cliques given with the inputs. -/
def inVerts (ins : List (ℕ × Finset (Finset ℕ))) : Finset ℕ :=
  (ins.map (fun x => x.2.sup id)).foldr (· ∪ ·) ∅

def OutOK (P : LocParams) (ins : List (ℕ × Finset (Finset ℕ))) : Mode → Out → Prop
  | .loc k, o => o.2.Nonempty ∧ o.2 ⊆ (ins.map Prod.fst).toFinset ∧ o.2.card ≤ fB P.M k
  | .locP k _, o => o.2.Nonempty ∧ o.2 ⊆ (ins.map Prod.fst).toFinset ∧ o.2.card ≤ fB P.M k
  | .cb k ℓ _, o => (Out.verts o).Nonempty ∧
      Out.verts o ⊆ (ins.map Prod.fst).toFinset ∪ inVerts ins ∧
      (Out.verts o).card ≤ gB P.M k (fB P.M) ℓ

def InOK (P : LocParams) (N : ℕ) (W : ℝ) (ins : List (ℕ × Finset (Finset ℕ))) : Mode → Prop
  | .loc k => (ins.map Prod.fst).Pairwise (· < ·) ∧ ins.length ≤ N ∧ k ≤ P.M ^ 2
  | .locP k n => (ins.map Prod.fst).Pairwise (· < ·) ∧ ins.length ≤ N ∧ k ≤ P.M ^ 2 ∧
      ins.length ≤ n ∧ 1 ≤ n ∧ n ≤ 2 * N
  | .cb k ℓ ν => (ins.map Prod.fst).Pairwise (· < ·) ∧ ins.length ≤ N ∧
      P.M ≤ ℓ ∧ ℓ ≤ k ∧ P.M < k ∧ k ≤ P.M ^ 2 ∧ 1 ≤ ν ∧ ν * 2 ^ (ℓ - P.M) ≤ W ∧
      ∀ x ∈ ins, x.2.Nonempty ∧ (∀ S ∈ x.2, S.card = P.M) ∧
        ((((ins.map Prod.snd).foldr (· ∪ ·) ∅).card : ℕ) : ℝ) ≤ ν * (x.2.card : ℝ)

/-- Global hypotheses on the parameters. -/
def GoodP (P : LocParams) (N : ℕ) (W F : ℝ) : Prop :=
  2 ≤ P.M ∧ 1 ≤ P.L ∧ nSeq P.M (P.M + 1) ≤ P.L ∧ 1 ≤ W ∧ 1 ≤ F ∧
    (∀ k, k ≤ P.M ^ 2 → (fB P.M k : ℝ) ≤ F) ∧
    (∀ k n, P.M < k → k ≤ P.M ^ 2 → 1 ≤ n → n ≤ 2 * N → nuOf P k n * 2 ^ (k - P.M) ≤ W)

noncomputable def Summary (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (N : ℕ) (W F : ℝ)
    (m : Mode) (addr : List ℕ) (ins : List (ℕ × Finset (Finset ℕ))) : Prop :=
  ∃ (nb ext : ℕ) (sizes : List ℕ),
    ((instRun P R Adj m addr ins Inst.fresh).2.1.toFinset.card : ℝ) ≤
        (P.L : ℝ) / P.M * nb + ext ∧
    (nb : ℝ) ≤ (ins.length : ℝ) / P.L + ownBins P m +
        (sizes.map (fun x : ℕ => 8 * ((x : ℕ) : ℝ) ^ (1 - 1 / (P.M : ℝ) ^ 10))).sum ∧
    ext ≤ sizes.length + ownExt m ∧
    ((∀ o, (instRun P R Adj m addr ins Inst.fresh).2.2.getLast? ≠ some (some o)) →
      ext ≤ sizes.length) ∧
    (sizes.length : ℝ) ≤ cntOf P.M W F (Real.logb 2 N) m ∧
    sizes.sum ≤ ins.length * depOf P.M m ∧
    (∀ x ∈ sizes, 1 ≤ x ∧ x ≤ N) ∧
    (∀ o, (instRun P R Adj m addr ins Inst.fresh).2.2.getLast? = some (some o) →
      OutOK P ins m o)

/-- The standing hypotheses of every case lemma. -/
def Std (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (N : ℕ) (W F : ℝ) : Prop :=
  GoodP P N W F ∧ R.Valid ∧ (∀ a b, Adj a b → Adj b a)

/-- The induction hypothesis for a mode. -/
def Holds (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (N : ℕ) (W F : ℝ) (m : Mode) :
    Prop :=
  ∀ addr ins, InOK P N W ins m → Live (instRun P R Adj m addr ins Inst.fresh).2.2 →
    Summary P R Adj N W F m addr ins

end OnlineColoringKYY.Supplement.Dev.T626
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartSB
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
theorem step_small_eq (P : LocParams) (R : Resolver) (A : ℕ → ℕ → Prop) (v k n : ℕ) (addr : List ℕ)
    (Cv : Finset (Finset ℕ)) (s : Inst) (cnt : ℕ) (bins : List (Finset ℕ × (ℕ × CFState)))
    (hn : Inst.normalize P (.locP k n) s = .small cnt bins) :
    locStep P R A v (.locP k n) addr Cv s =
      if (cliquesIn A (P.M + 1) (insert v (bins.getD (cnt / P.L) (∅, (0, default))).1)).Nonempty then
        (.small (cnt + 1) bins, (addr ++ [2, 0, 0], 0),
          some (∅, R.clique addr v (cliquesIn A (P.M + 1) (insert v (bins.getD (cnt / P.L) (∅, (0, default))).1))))
      else
        (.small (cnt + 1) (if cnt / P.L < bins.length then bins.set (cnt / P.L)
            (insert v (bins.getD (cnt / P.L) (∅, (0, default))).1,
              (c65Step P.M R A v (addr ++ [0, cnt / P.L, 0]) (bins.getD (cnt / P.L) (∅, (0, default))).2).1)
          else bins ++ [(insert v (bins.getD (cnt / P.L) (∅, (0, default))).1,
              (c65Step P.M R A v (addr ++ [0, cnt / P.L, 0]) (bins.getD (cnt / P.L) (∅, (0, default))).2).1)]),
          (c65Step P.M R A v (addr ++ [0, cnt / P.L, 0]) (bins.getD (cnt / P.L) (∅, (0, default))).2).2,
          none) := by
  rw [locStep.eq_def, hn]

theorem step_big_eq (P : LocParams) (R : Resolver) (A : ℕ → ℕ → Prop) (v k n : ℕ) (addr : List ℕ)
    (Cv : Finset (Finset ℕ)) (s : Inst) (bins : List (Finset ℕ × (ℕ × CFState))) (cb : Inst)
    (hn : Inst.normalize P (.locP k n) s = .big bins cb) :
    locStep P R A v (.locP k n) addr Cv s =
      (let ok : ℕ → Prop := fun j =>
        (bins.getD j (∅, (0, default))).1.card < P.L ∧
          cliquesIn A (P.M + 1) (insert v (bins.getD j (∅, (0, default))).1) = ∅
      have hex : ∃ j, (j < bins.length ∧ ok j) ∨ j = bins.length := ⟨bins.length, Or.inr rfl⟩
      let j : ℕ := Nat.find hex
      let incomplete : ℕ := (bins.filter (fun b => 1 ≤ b.1.card ∧ b.1.card < P.L)).length
      if j = bins.length ∧ incomplete = Jof P k n then
        let C : Finset (Finset ℕ) := bins.foldr
          (fun b acc => acc ∪ (cliquesIn A P.M b.1).filter (fun S => ∀ u ∈ S, A v u)) ∅
        let res := locStep P R A v (.cb k k (nuOf P k n)) (addr ++ [8, 0, 0]) C cb
        (.big bins res.1, res.2.1, res.2.2.map (fun o => (∅, Out.verts o)))
      else
        let bin := bins.getD j (∅, (0, default))
        let res := c65Step P.M R A v (addr ++ [0, j, 0]) bin.2
        let bins' := if j < bins.length then bins.set j (insert v bin.1, res.1)
          else bins ++ [({v}, res.1)]
        (.big bins' cb, res.2, none)) := by
  rw [locStep.eq_def, hn]
  rfl

theorem gB_congr (M k : ℕ) (hM : 0 < M) (hk : 0 < k) (f g : ℕ → ℕ) (h : ∀ j < k, f j = g j) :
    ∀ l, gB M k f l = gB M k g l
  | 0 => by simp only [gB]; rw [h _ (by omega)]
  | l + 1 => by
    simp only [gB]
    rw [h (k - M) (by omega), h (k - (l + 1)) (by omega), gB_congr M k hM hk f g h l]

theorem fB_big (M k : ℕ) (hM : 0 < M) (hk : M < k) : gB M k (fB M) k = fB M k := by
  conv_rhs => rw [fB]
  rw [if_neg (by omega)]
  apply gB_congr M k hM (by omega)
  intro j hj
  rw [dif_pos hj]

theorem fB_small (M k : ℕ) (hk : k ≤ M) : fB M k = M + 1 := by
  rw [fB, if_pos hk]

/-! ## Generic run lemmas -/
theorem instRun_append (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (m : Mode)
    (addr : List ℕ) (xs ys : List (ℕ × Finset (Finset ℕ))) (s : Inst) :
    instRun P R Adj m addr (xs ++ ys) s =
      ((instRun P R Adj m addr ys (instRun P R Adj m addr xs s).1).1,
        (instRun P R Adj m addr xs s).2.1 ++ (instRun P R Adj m addr ys (instRun P R Adj m addr xs s).1).2.1,
        (instRun P R Adj m addr xs s).2.2 ++ (instRun P R Adj m addr ys (instRun P R Adj m addr xs s).1).2.2) := by
  induction xs generalizing s with
  | nil => simp [instRun]
  | cons x xs ih => simp [instRun, ih]

theorem instRun_single (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (m : Mode)
    (addr : List ℕ) (x : ℕ × Finset (Finset ℕ)) (s : Inst) :
    instRun P R Adj m addr [x] s =
      ((locStep P R (AdjAt Adj x.1) x.1 m addr x.2 s).1,
        [(locStep P R (AdjAt Adj x.1) x.1 m addr x.2 s).2.1],
        [(locStep P R (AdjAt Adj x.1) x.1 m addr x.2 s).2.2]) := by
  simp [instRun]

theorem instRun_snoc (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (m : Mode)
    (addr : List ℕ) (xs : List (ℕ × Finset (Finset ℕ))) (x : ℕ × Finset (Finset ℕ)) (s : Inst) :
    instRun P R Adj m addr (xs ++ [x]) s =
      ((locStep P R (AdjAt Adj x.1) x.1 m addr x.2 (instRun P R Adj m addr xs s).1).1,
        (instRun P R Adj m addr xs s).2.1 ++
          [(locStep P R (AdjAt Adj x.1) x.1 m addr x.2 (instRun P R Adj m addr xs s).1).2.1],
        (instRun P R Adj m addr xs s).2.2 ++
          [(locStep P R (AdjAt Adj x.1) x.1 m addr x.2 (instRun P R Adj m addr xs s).1).2.2]) := by
  rw [instRun_append, instRun_single]

theorem c65Run_append (A : ℕ) (R : Resolver) (Adjf : ℕ → ℕ → ℕ → Prop) (addr : List ℕ)
    (vs ws : List ℕ) (s : ℕ × CFState) :
    c65Run A R Adjf addr (vs ++ ws) s =
      ((c65Run A R Adjf addr ws (c65Run A R Adjf addr vs s).1).1,
        (c65Run A R Adjf addr vs s).2 ++ (c65Run A R Adjf addr ws (c65Run A R Adjf addr vs s).1).2) := by
  induction vs generalizing s with
  | nil => simp [c65Run]
  | cons v vs ih => simp [c65Run, ih]

theorem c65Run_snoc (A : ℕ) (R : Resolver) (Adjf : ℕ → ℕ → ℕ → Prop) (addr : List ℕ)
    (vs : List ℕ) (v : ℕ) (s : ℕ × CFState) :
    c65Run A R Adjf addr (vs ++ [v]) s =
      ((c65Step A R (Adjf v) v addr (c65Run A R Adjf addr vs s).1).1,
        (c65Run A R Adjf addr vs s).2 ++ [(c65Step A R (Adjf v) v addr (c65Run A R Adjf addr vs s).1).2]) := by
  rw [c65Run_append]; simp [c65Run]

/-! ## Cliques and the restricted adjacency -/
theorem mem_cliquesIn {Adj : ℕ → ℕ → Prop} {k : ℕ} {S t : Finset ℕ} :
    t ∈ cliquesIn Adj k S ↔ t ⊆ S ∧ t.card = k ∧ IsCliqueSet Adj t := by
  simp [cliquesIn]

theorem cliquesIn_adjAt (Adj : ℕ → ℕ → Prop) (v r : ℕ) (S : Finset ℕ) (h : ∀ a ∈ S, a ≤ v) :
    cliquesIn (AdjAt Adj v) r S = cliquesIn Adj r S := by
  ext t
  rw [mem_cliquesIn, mem_cliquesIn]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun a ha b hb hab => (h3 a ha b hb hab).2.2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun a ha b hb hab => ⟨h a (h1 ha), h b (h1 hb), h3 a ha b hb hab⟩⟩

theorem consistent_of_sorted (Adj : ℕ → ℕ → Prop) (vs : List ℕ) (h : vs.Pairwise (· < ·)) :
    Consistent (AdjAt Adj) Adj vs := by
  intro i hi a ha b hb
  have hle : ∀ x ∈ vs.take (i + 1), x ≤ vs.get ⟨i, hi⟩ := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have hj' : j ≤ i := by simp at hj; omega
    rw [List.getElem_take]
    rcases Nat.lt_or_eq_of_le hj' with hlt | rfl
    · exact le_of_lt (List.pairwise_iff_getElem.1 h j i (by omega) hi hlt)
    · simp
  exact ⟨fun h' => h'.2.2, fun h' => ⟨hle a ha, hle b hb, h'⟩⟩

theorem toFinset_concat (l : List ℕ) (v : ℕ) : (l ++ [v]).toFinset = insert v l.toFinset := by
  ext x; simp

/-! ## Algorithm 5: the cases of one step -/
/-- Bin `B` may receive `v`. -/
def OkB (P : LocParams) (A : ℕ → ℕ → Prop) (v : ℕ) (B : Finset ℕ) : Prop :=
  B.card < P.L ∧ cliquesIn A (P.M + 1) (insert v B) = ∅

/-- The set `𝒞(v)` presented to the CB instance. -/
noncomputable def Cset (P : LocParams) (A : ℕ → ℕ → Prop) (v : ℕ)
    (bins : List (Finset ℕ × (ℕ × CFState))) : Finset (Finset ℕ) :=
  bins.foldr (fun b acc => acc ∪ (cliquesIn A P.M b.1).filter (fun S => ∀ u ∈ S, A v u)) ∅

/-- The number of incomplete bins. -/
def incOf (P : LocParams) (bins : List (Finset ℕ × (ℕ × CFState))) : ℕ :=
  (bins.filter (fun b => decide (1 ≤ b.1.card ∧ b.1.card < P.L))).length

theorem mem_Cset {P : LocParams} {A : ℕ → ℕ → Prop} {v : ℕ}
    {bins : List (Finset ℕ × (ℕ × CFState))} {t : Finset ℕ} :
    t ∈ Cset P A v bins ↔ ∃ b ∈ bins, t ∈ cliquesIn A P.M b.1 ∧ ∀ u ∈ t, A v u := by
  induction bins with
  | nil => simp [Cset]
  | cons b bins ih =>
    simp only [Cset, List.foldr_cons] at ih ⊢
    rw [Finset.mem_union, ih, Finset.mem_filter]
    simp only [List.mem_cons, exists_eq_or_imp]
    exact or_comm

theorem find_facts {p : ℕ → Prop} [DecidablePred p] (h : ∃ j, p j) :
    p (Nat.find h) ∧ ∀ k < Nat.find h, ¬ p k :=
  ⟨Nat.find_spec h, fun _ hk => Nat.find_min h hk⟩

theorem step_big_cases (P : LocParams) (R : Resolver) (A : ℕ → ℕ → Prop) (v k n : ℕ)
    (addr : List ℕ) (Cv : Finset (Finset ℕ)) (s : Inst) (bins : List (Finset ℕ × (ℕ × CFState)))
    (cb : Inst) (hn : Inst.normalize P (.locP k n) s = .big bins cb) :
    ((∀ i (hi : i < bins.length), ¬ OkB P A v bins[i].1) ∧ incOf P bins = Jof P k n ∧
      locStep P R A v (.locP k n) addr Cv s =
        (.big bins (locStep P R A v (.cb k k (nuOf P k n)) (addr ++ [8, 0, 0]) (Cset P A v bins) cb).1,
          (locStep P R A v (.cb k k (nuOf P k n)) (addr ++ [8, 0, 0]) (Cset P A v bins) cb).2.1,
          (locStep P R A v (.cb k k (nuOf P k n)) (addr ++ [8, 0, 0]) (Cset P A v bins) cb).2.2.map
            (fun o => (∅, Out.verts o)))) ∨
    (∃ j, ∃ hj : j < bins.length, OkB P A v bins[j].1 ∧
      locStep P R A v (.locP k n) addr Cv s =
        (.big (bins.set j (insert v bins[j].1,
            (c65Step P.M R A v (addr ++ [0, j, 0]) bins[j].2).1)) cb,
          (c65Step P.M R A v (addr ++ [0, j, 0]) bins[j].2).2, none)) ∨
    (incOf P bins ≠ Jof P k n ∧
      locStep P R A v (.locP k n) addr Cv s =
        (.big (bins ++ [({v}, (c65Step P.M R A v (addr ++ [0, bins.length, 0]) (0, CFState.mk [] [])).1)]) cb,
          (c65Step P.M R A v (addr ++ [0, bins.length, 0]) (0, CFState.mk [] [])).2, none)) := by
  rw [step_big_eq P R A v k n addr Cv s bins cb hn]
  dsimp only
  obtain ⟨hs, hm⟩ := find_facts (p := fun j => (j < bins.length ∧
      ((bins.getD j (∅, (0, default))).1.card < P.L ∧
        cliquesIn A (P.M + 1) (insert v (bins.getD j (∅, (0, default))).1) = ∅)) ∨ j = bins.length)
    ⟨bins.length, Or.inr rfl⟩
  generalize Nat.find (p := fun j => (j < bins.length ∧
      ((bins.getD j (∅, (0, default))).1.card < P.L ∧
        cliquesIn A (P.M + 1) (insert v (bins.getD j (∅, (0, default))).1) = ∅)) ∨ j = bins.length)
    ⟨bins.length, Or.inr rfl⟩ = j at hs hm ⊢
  by_cases hc : j = bins.length ∧ incOf P bins = Jof P k n
  · left
    obtain ⟨hj, hinc⟩ := hc
    subst hj
    refine ⟨?_, hinc, ?_⟩
    · intro i hi hok
      exact hm i hi (Or.inl ⟨hi, by rw [List.getD_eq_getElem _ _ hi]; exact hok⟩)
    · unfold incOf at hinc
      rw [if_pos ⟨rfl, hinc⟩]
      rfl
  · right
    have hc' : ¬ (j = bins.length ∧
        (List.filter (fun b => decide (1 ≤ b.1.card ∧ b.1.card < P.L)) bins).length =
          Jof P k n) := hc
    rw [if_neg hc']
    rcases hs with ⟨hj, hok⟩ | hj
    · left
      refine ⟨j, hj, ?_, ?_⟩
      · rw [List.getD_eq_getElem _ _ hj] at hok; exact hok
      · simp only [List.getD_eq_getElem _ _ hj, if_pos hj]
    · right
      subst hj
      refine ⟨fun h => hc ⟨rfl, h⟩, ?_⟩
      simp only [List.getD_eq_default _ _ le_rfl, lt_irrefl, if_false]
      rfl

/-! ## Bins -/
/-- The state of bin `i` holding the vertex list `l`. -/
noncomputable def binSt (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (addr : List ℕ)
    (i : ℕ) (l : List ℕ) : Finset ℕ × (ℕ × CFState) :=
  (l.toFinset, (c65Run P.M R (AdjAt Adj) (addr ++ [0, i, 0]) l (0, CFState.mk [] [])).1)

/-- The colors of bin `i` holding the vertex list `l`. -/
noncomputable def binCols (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (addr : List ℕ)
    (i : ℕ) (l : List ℕ) : List Color :=
  (c65Run P.M R (AdjAt Adj) (addr ++ [0, i, 0]) l (0, CFState.mk [] [])).2

def BinsRel (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (addr : List ℕ)
    (bins : List (Finset ℕ × (ℕ × CFState))) (ls : List (List ℕ)) : Prop :=
  bins.length = ls.length ∧
    ∀ i (h1 : i < bins.length) (h2 : i < ls.length), bins[i] = binSt P R Adj addr i ls[i]

theorem binSt_snoc (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (addr : List ℕ)
    (i : ℕ) (l : List ℕ) (v : ℕ) :
    binSt P R Adj addr i (l ++ [v]) =
      (insert v (binSt P R Adj addr i l).1,
        (c65Step P.M R (AdjAt Adj v) v (addr ++ [0, i, 0]) (binSt P R Adj addr i l).2).1) := by
  unfold binSt
  rw [c65Run_snoc, toFinset_concat]

theorem binCols_snoc (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (addr : List ℕ)
    (i : ℕ) (l : List ℕ) (v : ℕ) :
    binCols P R Adj addr i (l ++ [v]) = binCols P R Adj addr i l ++
        [(c65Step P.M R (AdjAt Adj v) v (addr ++ [0, i, 0]) (binSt P R Adj addr i l).2).2] := by
  unfold binCols binSt
  rw [c65Run_snoc]

theorem binSt_nil (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (addr : List ℕ) (i : ℕ) :
    binSt P R Adj addr i [] = (∅, (0, default)) := rfl

/-- Per-bin color bound (Corollary 6.5). -/
theorem binCols_card (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (addr : List ℕ)
    (hM : 1 ≤ P.M) (hL : nSeq P.M (P.M + 1) ≤ P.L) (hR : R.Valid)
    (hsymm : ∀ a b, Adj a b → Adj b a) (i : ℕ) (l : List ℕ) (hs : l.Pairwise (· < ·))
    (hlen : l.length ≤ P.L) (hfree : cliquesIn Adj (P.M + 1) l.toFinset = ∅) :
    ((binCols P R Adj addr i l).toFinset.card : ℝ) ≤ (P.L : ℝ) / P.M :=
  c65_colors_le P.M P.L hM hL R hR (AdjAt Adj) Adj hsymm _ l (hs.imp (fun h => ne_of_lt h)) hlen
    hfree (consistent_of_sorted Adj l hs)

/-- The colors of a family of bins. -/
theorem cols_card (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (addr : List ℕ)
    (hM : 1 ≤ P.M) (hL : nSeq P.M (P.M + 1) ≤ P.L) (hR : R.Valid)
    (hsymm : ∀ a b, Adj a b → Adj b a) (ls : List (List ℕ))
    (hls : ∀ l ∈ ls, l.Pairwise (· < ·) ∧ l.length ≤ P.L ∧ cliquesIn Adj (P.M + 1) l.toFinset = ∅)
    (cs : List Color)
    (hcs : ∀ c ∈ cs, ∃ i, ∃ h : i < ls.length, c ∈ binCols P R Adj addr i ls[i]) :
    (cs.toFinset.card : ℝ) ≤ (P.L : ℝ) / P.M * ls.length := by
  have hsub : cs.toFinset ⊆ (Finset.range ls.length).biUnion
      (fun i => (binCols P R Adj addr i (ls.getD i [])).toFinset) := by
    intro c hc
    rw [List.mem_toFinset] at hc
    obtain ⟨i, hi, hci⟩ := hcs c hc
    rw [Finset.mem_biUnion]
    refine ⟨i, Finset.mem_range.2 hi, ?_⟩
    rw [List.getD_eq_getElem _ _ hi, List.mem_toFinset]
    exact hci
  have h1 : cs.toFinset.card ≤ ∑ i ∈ Finset.range ls.length,
      (binCols P R Adj addr i (ls.getD i [])).toFinset.card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h2 : ((∑ i ∈ Finset.range ls.length,
      (binCols P R Adj addr i (ls.getD i [])).toFinset.card : ℕ) : ℝ) ≤
      ∑ i ∈ Finset.range ls.length, (P.L : ℝ) / P.M := by
    rw [Nat.cast_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_range] at hi
    rw [List.getD_eq_getElem _ _ hi]
    obtain ⟨a, b, c⟩ := hls _ (List.getElem_mem hi)
    exact binCols_card P R Adj addr hM hL hR hsymm i _ a b c
  have h3 : (cs.toFinset.card : ℝ) ≤ ((∑ i ∈ Finset.range ls.length,
      (binCols P R Adj addr i (ls.getD i [])).toFinset.card : ℕ) : ℝ) := by exact_mod_cast h1
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
  linarith

/-! ## LOC′(k), `k ≤ M` -/
structure SInv (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (addr : List ℕ) (k n : ℕ)
    (H : List ℕ) (ls : List (List ℕ)) (s : Inst) (cs : List Color) : Prop where
  st : ∃ bins, Inst.normalize P (.locP k n) s = .small H.length bins ∧ BinsRel P R Adj addr bins ls
  len : ∀ i (h : i < ls.length), ls[i].length = min P.L (H.length - i * P.L)
  cnt1 : H.length ≤ P.L * ls.length
  cnt2 : P.L * ls.length < H.length + P.L
  each : ∀ l ∈ ls, l.Pairwise (· < ·) ∧ (∀ x ∈ l, x ∈ H) ∧ cliquesIn Adj (P.M + 1) l.toFinset = ∅
  cols : ∀ c ∈ cs, ∃ i, ∃ h : i < ls.length, c ∈ binCols P R Adj addr i ls[i]

theorem sinv_len_le {P : LocParams} {R : Resolver} {Adj : ℕ → ℕ → Prop} {addr : List ℕ} {k n : ℕ}
    {H : List ℕ} {ls : List (List ℕ)} {s : Inst} {cs : List Color}
    (hI : SInv P R Adj addr k n H ls s cs) : ∀ l ∈ ls, l.length ≤ P.L := by
  intro l hl
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
  rw [hI.len i hi]
  exact min_le_left _ _

theorem sinv_step (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (addr : List ℕ) (k n : ℕ)
    (hL : 1 ≤ P.L) {H : List ℕ} {ls : List (List ℕ)} {s : Inst} {cs : List Color}
    (hI : SInv P R Adj addr k n H ls s cs) (v : ℕ) (Cv : Finset (Finset ℕ))
    (hv : ∀ h ∈ H, h < v)
    (hnone : (locStep P R (AdjAt Adj v) v (.locP k n) addr Cv s).2.2 = none) :
    ∃ ls', SInv P R Adj addr k n (H ++ [v]) ls' (locStep P R (AdjAt Adj v) v (.locP k n) addr Cv s).1
      (cs ++ [(locStep P R (AdjAt Adj v) v (.locP k n) addr Cv s).2.1]) := by
  obtain ⟨bins, hn, hbl, hbk⟩ := hI.st
  rw [step_small_eq P R (AdjAt Adj v) v k n addr Cv s H.length bins hn] at hnone ⊢
  have hcl : ¬ (cliquesIn (AdjAt Adj v) (P.M + 1)
      (insert v (bins.getD (H.length / P.L) (∅, (0, default))).1)).Nonempty := by
    intro h; rw [if_pos h] at hnone; simp at hnone
  rw [if_neg hcl]
  clear hnone
  -- arithmetic
  set c := H.length with hc
  set b := c / P.L with hbdef
  clear_value b c
  have hb1 : b * P.L ≤ c := hbdef ▸ Nat.div_mul_le_self c P.L
  have hb2 : c < P.L * (b + 1) := hbdef ▸ Nat.lt_mul_div_succ c (by omega)
  have hc1 := hI.cnt1
  have hc2 := hI.cnt2
  rw [← hc] at hc1 hc2
  have hlen_le : ls.length ≤ b + 1 := by
    have : P.L * ls.length < P.L * (b + 2) := by rw [mul_add]; rw [mul_add] at hb2; omega
    have := Nat.lt_of_mul_lt_mul_left this
    omega
  have hle_b : b ≤ ls.length := by
    have : P.L * b ≤ P.L * ls.length := by rw [mul_comm]; omega
    exact Nat.le_of_mul_le_mul_left this (by omega)
  have hfreeT : ∀ l : List ℕ, (∀ x ∈ l, x ∈ H) →
      ¬ (cliquesIn (AdjAt Adj v) (P.M + 1) (insert v l.toFinset)).Nonempty →
      cliquesIn Adj (P.M + 1) (l ++ [v]).toFinset = ∅ := by
    intro l hl h
    rw [toFinset_concat, ← cliquesIn_adjAt Adj v]
    · exact Finset.not_nonempty_iff_eq_empty.1 h
    · intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact le_rfl
      · exact le_of_lt (hv a (hl a (List.mem_toFinset.1 ha)))
  have hsortT : ∀ l : List ℕ, (∀ x ∈ l, x ∈ H) → l.Pairwise (· < ·) → (l ++ [v]).Pairwise (· < ·) := by
    intro l hl hs
    rw [List.pairwise_append]
    exact ⟨hs, by simp, fun a ha b hb => by simp at hb; subst hb; exact hv a (hl a ha)⟩
  have hsubT : ∀ l : List ℕ, (∀ x ∈ l, x ∈ H) → ∀ x ∈ l ++ [v], x ∈ H ++ [v] := by
    intro l hl x hx
    rcases List.mem_append.1 hx with h | h
    · exact List.mem_append_left _ (hl x h)
    · exact List.mem_append_right _ h
  rcases Nat.lt_or_ge b ls.length with hbl' | hbl'
  · -- insert into the last bin
    have hlb : ls.length = b + 1 := by omega
    have hbb : b < bins.length := by omega
    rw [List.getD_eq_getElem _ _ hbb, hbk b hbb hbl'] at hcl ⊢
    rw [if_pos hbb]
    have hold := hI.each _ (List.getElem_mem hbl')
    refine ⟨ls.set b (ls[b] ++ [v]), ⟨_, by rw [List.length_append, List.length_singleton, ← hc]; rfl, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hbl]
    · intro i h1 h2
      rw [List.getElem_set, List.getElem_set]
      split_ifs with hib
      · subst hib; rw [binSt_snoc]
      · exact hbk i (by simpa using h1) (by simpa using h2)
    · intro i hi
      rw [List.length_set] at hi
      rw [List.getElem_set]
      simp only [List.length_append, List.length_singleton]
      split_ifs with hib
      · subst hib
        rw [List.length_append, List.length_singleton, hI.len _ hbl']
        rw [mul_add] at hb2
        have := mul_comm P.L b
        omega
      · have hib' : i < b := by omega
        have h3 : (i + 1) * P.L ≤ b * P.L := Nat.mul_le_mul_right _ hib'
        rw [hI.len i (by omega)]
        rw [add_mul] at h3
        omega
    · simp only [List.length_append, List.length_singleton, List.length_set]
      rw [mul_add] at hb2; rw [hlb, mul_add]; omega
    · simp only [List.length_append, List.length_singleton, List.length_set]
      omega
    · intro l hl
      rcases List.mem_or_eq_of_mem_set hl with hl | rfl
      · obtain ⟨a, b, c⟩ := hI.each l hl
        exact ⟨a, fun x hx => List.mem_append_left _ (b x hx), c⟩
      · exact ⟨hsortT _ hold.2.1 hold.1, hsubT _ hold.2.1, hfreeT _ hold.2.1 hcl⟩
    · intro c hc'
      rcases List.mem_append.1 hc' with hc' | hc'
      · obtain ⟨i, hi, hci⟩ := hI.cols c hc'
        refine ⟨i, by simpa using hi, ?_⟩
        rw [List.getElem_set]
        split_ifs with hib
        · subst hib; rw [binCols_snoc]; exact List.mem_append_left _ hci
        · exact hci
      · rw [List.mem_singleton] at hc'
        subst hc'
        refine ⟨b, by simpa using hbl', ?_⟩
        rw [List.getElem_set_self, binCols_snoc]
        simp
  · -- a new bin
    have hlb : ls.length = b := by omega
    have hbb : bins.length = b := by omega
    have hcb : c = P.L * b := by
      have : P.L * b ≤ c := by rw [mul_comm]; exact hb1
      rw [hlb] at hc1; omega
    rw [List.getD_eq_default _ _ (by omega)] at hcl ⊢
    rw [if_neg (by omega)]
    have hcl' : ¬ (cliquesIn (AdjAt Adj v) (P.M + 1) (insert v ([] : List ℕ).toFinset)).Nonempty := by
      simpa using hcl
    refine ⟨ls ++ [[v]], ⟨_, by rw [List.length_append, List.length_singleton, ← hc]; rfl, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hbl]
    · intro i h1 h2
      by_cases hi : i < bins.length
      · rw [List.getElem_append_left hi, List.getElem_append_left (hbl ▸ hi)]
        exact hbk i hi (hbl ▸ hi)
      · have hi1 : i = bins.length := by simp at h1; omega
        subst hi1
        rw [List.getElem_concat_length rfl, List.getElem_concat_length hbl]
        rw [hbb, show ([v] : List ℕ) = [] ++ [v] from rfl, binSt_snoc, binSt_nil]
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi ⊢
      by_cases hi' : i < ls.length
      · rw [List.getElem_append_left hi', hI.len i hi']
        have h3 : (i + 1) * P.L ≤ b * P.L := Nat.mul_le_mul_right _ (by omega)
        rw [add_mul] at h3
        rw [mul_comm] at hcb
        omega
      · have hi1 : i = ls.length := by omega
        subst hi1
        rw [List.getElem_append_right (le_refl _)]
        simp only [Nat.sub_self, List.getElem_cons_zero, List.length_singleton]
        rw [hlb]
        have := mul_comm P.L b
        omega
    · simp only [List.length_append, List.length_singleton]
      rw [mul_add, hlb]; omega
    · simp only [List.length_append, List.length_singleton]
      rw [mul_add, hlb]; omega
    · intro l hl
      rcases List.mem_append.1 hl with hl | hl
      · obtain ⟨a, b, c⟩ := hI.each l hl
        exact ⟨a, fun x hx => List.mem_append_left _ (b x hx), c⟩
      · rw [List.mem_singleton] at hl
        subst hl
        exact ⟨hsortT [] (by simp) (by simp), hsubT [] (by simp),
          hfreeT [] (by simp) hcl'⟩
    · intro c hc'
      rcases List.mem_append.1 hc' with hc' | hc'
      · obtain ⟨i, hi, hci⟩ := hI.cols c hc'
        exact ⟨i, by simp; omega, by rw [List.getElem_append_left hi]; exact hci⟩
      · rw [List.mem_singleton] at hc'
        subst hc'
        refine ⟨ls.length, by simp, ?_⟩
        rw [List.getElem_append_right (le_refl _)]
        simp only [Nat.sub_self, List.getElem_cons_zero]
        rw [show ([v] : List ℕ) = [] ++ [v] from rfl, binCols_snoc, binSt_nil, hlb]
        simp

theorem binsRel_getD_sub {P : LocParams} {R : Resolver} {Adj : ℕ → ℕ → Prop} {addr : List ℕ}
    {bins : List (Finset ℕ × (ℕ × CFState))} {ls : List (List ℕ)} {H : List ℕ}
    (hb : BinsRel P R Adj addr bins ls) (hsub : ∀ l ∈ ls, ∀ x ∈ l, x ∈ H) (b : ℕ) :
    ∀ x ∈ (bins.getD b (∅, (0, default))).1, x ∈ H := by
  intro x hx
  by_cases hbb : b < bins.length
  · rw [List.getD_eq_getElem _ _ hbb, hb.2 b hbb (hb.1 ▸ hbb)] at hx
    exact hsub _ (List.getElem_mem _) x (List.mem_toFinset.1 hx)
  · rw [List.getD_eq_default _ _ (by omega)] at hx
    simp at hx

theorem sinv_step_some (P : LocParams) (R : Resolver) (hR : R.Valid) (Adj : ℕ → ℕ → Prop)
    (addr : List ℕ) (k n : ℕ) {H : List ℕ} {ls : List (List ℕ)} {s : Inst} {cs : List Color}
    (hI : SInv P R Adj addr k n H ls s cs) (v : ℕ) (Cv : Finset (Finset ℕ)) (o : Out)
    (ho : (locStep P R (AdjAt Adj v) v (.locP k n) addr Cv s).2.2 = some o) :
    (locStep P R (AdjAt Adj v) v (.locP k n) addr Cv s).2.1 = (addr ++ [2, 0, 0], 0) ∧
      o.2.card = P.M + 1 ∧ ∀ x ∈ o.2, x = v ∨ x ∈ H := by
  obtain ⟨bins, hn, hb⟩ := hI.st
  rw [step_small_eq P R (AdjAt Adj v) v k n addr Cv s H.length bins hn] at ho ⊢
  by_cases hcl : (cliquesIn (AdjAt Adj v) (P.M + 1)
      (insert v (bins.getD (H.length / P.L) (∅, (0, default))).1)).Nonempty
  · rw [if_pos hcl] at ho ⊢
    simp only [Option.some.injEq] at ho
    subst ho
    have hm := hR.2.1 addr v _ hcl
    rw [mem_cliquesIn] at hm
    refine ⟨rfl, hm.2.1, fun x hx => ?_⟩
    rcases Finset.mem_insert.1 (hm.1 hx) with h | h
    · exact Or.inl h
    · exact Or.inr (binsRel_getD_sub hb (fun l hl => (hI.each l hl).2.1) _ x h)
  · rw [if_neg hcl] at ho
    simp at ho

theorem srun (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (addr : List ℕ) (k n : ℕ)
    (hL : 1 ≤ P.L) (xs : List (ℕ × Finset (Finset ℕ))) :
    ∀ (H : List ℕ) (ls : List (List ℕ)) (s : Inst) (cs : List Color),
      SInv P R Adj addr k n H ls s cs → (H ++ xs.map Prod.fst).Pairwise (· < ·) →
      (∀ o ∈ (instRun P R Adj (.locP k n) addr xs s).2.2, o = none) →
      ∃ ls', SInv P R Adj addr k n (H ++ xs.map Prod.fst) ls'
        (instRun P R Adj (.locP k n) addr xs s).1 (cs ++ (instRun P R Adj (.locP k n) addr xs s).2.1) := by
  induction xs with
  | nil => intro H ls s cs hI _ _; exact ⟨ls, by simpa [instRun] using hI⟩
  | cons x xs ih =>
    intro H ls s cs hI hs ho
    simp only [instRun, List.mem_cons, forall_eq_or_imp] at ho
    have hv : ∀ h ∈ H, h < x.1 := by
      intro h hh
      rw [List.map_cons, List.pairwise_append] at hs
      exact hs.2.2 h hh x.1 List.mem_cons_self
    obtain ⟨ls1, h1⟩ := sinv_step P R Adj addr k n hL hI x.1 x.2 hv ho.1
    obtain ⟨ls2, h2⟩ := ih (H ++ [x.1]) ls1 _ _ h1 (by simpa using hs) ho.2
    refine ⟨ls2, ?_⟩
    simpa [instRun] using h2

theorem nb_real (L l c N : ℕ) (hL : 1 ≤ L) (h : L * l < c + L) (hc : c ≤ N) :
    (l : ℝ) ≤ (N : ℝ) / L + 1 := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have h1 : ((L * l : ℕ) : ℝ) ≤ (N : ℝ) + L := by
    have : L * l ≤ N + L := by omega
    exact_mod_cast this
  push_cast at h1
  rw [div_add_one hL'.ne', le_div_iff₀ hL']
  linarith

theorem holds_small (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (N : ℕ) (W F : ℝ)
    (hS : Std P R Adj N W F) (k n : ℕ) (hk : k ≤ P.M) : Holds P R Adj N W F (.locP k n) := by
  intro addr ins hin hlive
  obtain ⟨⟨hM2, hL1, hnL, -, -, -, -⟩, hR, hsymm⟩ := hS
  have hM : 1 ≤ P.M := by omega
  obtain ⟨hsort, -, -, -, -, -⟩ := hin
  have hI0 : SInv P R Adj addr k n [] [] Inst.fresh [] := by
    refine ⟨⟨[], ?_, by simp [BinsRel]⟩, by simp, by simp, by simp; omega, by simp, by simp⟩
    simp [Inst.normalize, Inst.initOf, hk]
  have hcnt : cntOf P.M W F (Real.logb 2 N) (.locP k n) = 0 := by simp [cntOf, hk]
  have hown : ownBins P (.locP k n) = 1 := by simp [ownBins, hk]
  have hcols : ∀ {H ls s cs}, SInv P R Adj addr k n H ls s cs →
      (cs.toFinset.card : ℝ) ≤ (P.L : ℝ) / P.M * ls.length := by
    intro H ls s cs hI
    exact cols_card P R Adj addr hM hnL hR hsymm ls
      (fun l hl => ⟨(hI.each l hl).1, sinv_len_le hI l hl, (hI.each l hl).2.2⟩) cs hI.cols
  rcases List.eq_nil_or_concat ins with rfl | ⟨xs, x, rfl⟩
  · refine ⟨0, 0, [], ?_⟩
    simp [instRun, hcnt, hown, ownExt]
  rw [List.concat_eq_append] at hsort hlive ⊢
  unfold Live at hlive
  rw [instRun_snoc, List.dropLast_concat] at hlive
  obtain ⟨ls, hI⟩ := srun P R Adj addr k n hL1 xs [] [] _ [] hI0
    (by simpa using (List.pairwise_append.1 (by simpa using hsort)).1) hlive
  simp only [List.nil_append] at hI
  have hv : ∀ h ∈ xs.map Prod.fst, h < x.1 := by
    intro h hh
    rw [List.map_append, List.pairwise_append] at hsort
    exact hsort.2.2 h hh x.1 (by simp)
  have hlenx : (xs.map Prod.fst).length = xs.length := by simp
  cases ho : (locStep P R (AdjAt Adj x.1) x.1 (.locP k n) addr x.2
      (instRun P R Adj (.locP k n) addr xs Inst.fresh).1).2.2 with
  | none =>
    obtain ⟨ls', hI'⟩ := sinv_step P R Adj addr k n hL1 hI x.1 x.2 hv ho
    refine ⟨ls'.length, 0, [], ?_, ?_, by simp [ownExt], fun _ => le_rfl, by simp [hcnt], by simp,
      by simp, ?_⟩
    · rw [instRun_snoc]
      have := hcols hI'
      simpa using this
    · have := nb_real P.L ls'.length _ (xs ++ [x]).length hL1 hI'.cnt2 (by simp)
      simp only [hown, List.map, List.sum_nil, add_zero]
      exact this
    · intro o h
      rw [instRun_snoc, ho] at h
      simp at h
  | some o =>
    obtain ⟨hc, hcard, hsub⟩ := sinv_step_some P R hR Adj addr k n hI x.1 x.2 o ho
    refine ⟨ls.length, 1, [], ?_, ?_, by simp [ownExt], ?_, by simp [hcnt], by simp, by simp, ?_⟩
    · rw [instRun_snoc, hc]
      have h1 := hcols hI
      have h2 : ((instRun P R Adj (.locP k n) addr xs Inst.fresh).2.1 ++
          [(addr ++ [2, 0, 0], 0)]).toFinset.card ≤
          (instRun P R Adj (.locP k n) addr xs Inst.fresh).2.1.toFinset.card + 1 := by
        rw [List.toFinset_append]
        exact (Finset.card_union_le _ _).trans (by simp)
      have h3 : ((((instRun P R Adj (.locP k n) addr xs Inst.fresh).2.1 ++
          [(addr ++ [2, 0, 0], 0)]).toFinset.card : ℕ) : ℝ) ≤
          ((instRun P R Adj (.locP k n) addr xs Inst.fresh).2.1.toFinset.card : ℝ) + 1 := by
        exact_mod_cast h2
      simp only [Nat.cast_one]
      linarith
    · have := nb_real P.L ls.length _ (xs ++ [x]).length hL1 hI.cnt2 (by simp)
      simp only [hown, List.map, List.sum_nil, add_zero]
      exact this
    · intro h
      exfalso
      apply h o
      rw [instRun_snoc, ho]
      simp
    · intro o' h
      rw [instRun_snoc, ho] at h
      simp only [List.getLast?_concat, Option.some.injEq] at h
      subst h
      refine ⟨?_, ?_, ?_⟩
      · rw [← Finset.card_pos, hcard]; omega
      · intro y hy
        rcases hsub y hy with rfl | h
        · simp
        · simp only [List.mem_toFinset, List.map_append, List.mem_append]
          exact Or.inl h
      · rw [hcard, fB_small P.M k hk]

end OnlineColoringKYY.Supplement.Dev.T626.PartSB
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626
open Classical OnlineColoringKYY.Supplement
/-! ### Case lemmas (one Part each) -/
alias holds_small := OnlineColoringKYY.Supplement.Dev.T626.PartSB.holds_small

end OnlineColoringKYY.Supplement.Dev.T626
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartSB
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
/-! ## LOC′(k), `k > M` (Algorithm 5) -/
/-- The run of the CB(k, k, ν) child on the inputs sent to it. -/
noncomputable def cbRun (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (addr : List ℕ)
    (k n : ℕ) (insCB : List (ℕ × Finset (Finset ℕ))) : Inst × List Color × List (Option Out) :=
  instRun P R Adj (.cb k k (nuOf P k n)) (addr ++ [8, 0, 0]) insCB Inst.fresh

theorem cbRun_snoc (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (addr : List ℕ)
    (k n : ℕ) (insCB : List (ℕ × Finset (Finset ℕ))) (v : ℕ) (C : Finset (Finset ℕ)) :
    cbRun P R Adj addr k n (insCB ++ [(v, C)]) =
      ((locStep P R (AdjAt Adj v) v (.cb k k (nuOf P k n)) (addr ++ [8, 0, 0]) C
          (cbRun P R Adj addr k n insCB).1).1,
        (cbRun P R Adj addr k n insCB).2.1 ++
          [(locStep P R (AdjAt Adj v) v (.cb k k (nuOf P k n)) (addr ++ [8, 0, 0]) C
            (cbRun P R Adj addr k n insCB).1).2.1],
        (cbRun P R Adj addr k n insCB).2.2 ++
          [(locStep P R (AdjAt Adj v) v (.cb k k (nuOf P k n)) (addr ++ [8, 0, 0]) C
            (cbRun P R Adj addr k n insCB).1).2.2]) := by
  unfold cbRun
  rw [instRun_snoc]

structure BInv (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (addr : List ℕ) (k n : ℕ)
    (H : List ℕ) (ls : List (List ℕ)) (insCB : List (ℕ × Finset (Finset ℕ))) (s : Inst)
    (cs : List Color) : Prop where
  st : ∃ bins, Inst.normalize P (.locP k n) s = .big bins (cbRun P R Adj addr k n insCB).1 ∧
    BinsRel P R Adj addr bins ls
  nodup : ls.flatten.Nodup
  each : ∀ l ∈ ls, l ≠ [] ∧ l.length ≤ P.L ∧ l.Pairwise (· < ·) ∧ (∀ x ∈ l, x ∈ H) ∧
    cliquesIn Adj (P.M + 1) l.toFinset = ∅
  inc : ls.countP (fun l => decide (l.length < P.L)) ≤ Jof P k n
  cbv : (insCB.map Prod.fst).Sublist H
  cbC : ∀ x ∈ insCB, Jof P k n ≤ x.2.card ∧ ∀ S ∈ x.2, S.card = P.M ∧ ∃ l ∈ ls, S ⊆ l.toFinset
  size : ls.flatten.length + insCB.length ≤ H.length
  cols : ∀ c ∈ cs, (∃ i, ∃ h : i < ls.length, c ∈ binCols P R Adj addr i ls[i]) ∨
    c ∈ (cbRun P R Adj addr k n insCB).2.1

/-- Each bin list extends the old one. -/
def Grow (ls ls' : List (List ℕ)) : Prop :=
  ∀ j (hj : j < ls.length), ∃ hj' : j < ls'.length, ∃ w, ls'[j] = ls[j] ++ w

theorem grow_mem {ls ls' : List (List ℕ)} (hg : Grow ls ls') {t : Finset ℕ}
    (h : ∃ L ∈ ls, t ⊆ L.toFinset) : ∃ L ∈ ls', t ⊆ L.toFinset := by
  obtain ⟨L, hL, ht⟩ := h
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hL
  obtain ⟨hj', w, hw⟩ := hg j hj
  refine ⟨ls'[j], List.getElem_mem hj', ht.trans ?_⟩
  rw [hw, List.toFinset_append]
  exact Finset.subset_union_left

theorem binCols_grow (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (addr : List ℕ)
    {ls ls' : List (List ℕ)} (hg : Grow ls ls') {c : Color}
    (h : ∃ i, ∃ hi : i < ls.length, c ∈ binCols P R Adj addr i ls[i]) :
    ∃ i, ∃ hi : i < ls'.length, c ∈ binCols P R Adj addr i ls'[i] := by
  obtain ⟨j, hj, hc⟩ := h
  obtain ⟨hj', w, hw⟩ := hg j hj
  refine ⟨j, hj', ?_⟩
  rw [hw]
  unfold binCols at hc ⊢
  rw [c65Run_append]
  exact List.mem_append_left _ hc

theorem grow_set (ls : List (List ℕ)) (j : ℕ) (hj : j < ls.length) (v : ℕ) :
    Grow ls (ls.set j (ls[j] ++ [v])) := by
  intro i hi
  refine ⟨by simpa using hi, ?_⟩
  rw [List.getElem_set]
  split_ifs with h
  · subst h; exact ⟨[v], rfl⟩
  · exact ⟨[], by simp⟩

theorem grow_append (ls : List (List ℕ)) (L : List ℕ) : Grow ls (ls ++ [L]) := by
  intro i hi
  refine ⟨by simp; omega, [], ?_⟩
  rw [List.getElem_append_left hi]
  simp

theorem flatten_set_perm (v : ℕ) : ∀ (ls : List (List ℕ)) (j : ℕ) (hj : j < ls.length),
    (ls.set j (ls[j] ++ [v])).flatten.Perm (ls.flatten ++ [v])
  | [], _, hj => by simp at hj
  | L :: ls, 0, _ => by
    simp only [List.set_cons_zero, List.flatten_cons, List.getElem_cons_zero, List.append_assoc]
    exact List.Perm.append_left L List.perm_append_comm
  | L :: ls, j + 1, hj => by
    simp only [List.set_cons_succ, List.flatten_cons, List.getElem_cons_succ, List.append_assoc]
    exact List.Perm.append_left L (flatten_set_perm v ls j (by simpa using hj))

theorem binsRel_fst {P : LocParams} {R : Resolver} {Adj : ℕ → ℕ → Prop} {addr : List ℕ}
    {bins : List (Finset ℕ × (ℕ × CFState))} {ls : List (List ℕ)}
    (h : BinsRel P R Adj addr bins ls) : bins.map Prod.fst = ls.map List.toFinset := by
  obtain ⟨hl, hb⟩ := h
  apply List.ext_getElem (by simp [hl])
  intro j h1 h2
  simp only [List.getElem_map]
  rw [hb j (by simpa using h1) (by simpa using h2)]
  rfl

theorem binsRel_mem {P : LocParams} {R : Resolver} {Adj : ℕ → ℕ → Prop} {addr : List ℕ}
    {bins : List (Finset ℕ × (ℕ × CFState))} {ls : List (List ℕ)}
    (hb : BinsRel P R Adj addr bins ls) {b : Finset ℕ × (ℕ × CFState)} (h : b ∈ bins) :
    ∃ L ∈ ls, b.1 = L.toFinset := by
  obtain ⟨hl, hbk⟩ := hb
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem h
  have hk' : k < ls.length := hl ▸ hk
  exact ⟨ls[k], List.getElem_mem hk', by rw [hbk k hk hk']; rfl⟩

theorem incOf_eq {P : LocParams} {R : Resolver} {Adj : ℕ → ℕ → Prop} {addr : List ℕ}
    {bins : List (Finset ℕ × (ℕ × CFState))} {ls : List (List ℕ)}
    (h : BinsRel P R Adj addr bins ls) (hnd : ls.flatten.Nodup) (hne : ∀ L ∈ ls, L ≠ []) :
    incOf P bins = ls.countP (fun L => decide (L.length < P.L)) := by
  unfold incOf
  rw [← List.countP_eq_length_filter]
  have : bins.countP (fun b => decide (1 ≤ b.1.card ∧ b.1.card < P.L)) =
      (bins.map Prod.fst).countP (fun B => decide (1 ≤ B.card ∧ B.card < P.L)) := by
    rw [List.countP_map]; rfl
  rw [this, binsRel_fst h, List.countP_map]
  apply List.countP_congr
  intro L hL
  have hLn : L.Nodup := (List.nodup_flatten.1 hnd).1 L hL
  have hc : L.toFinset.card = L.length := List.toFinset_card_of_nodup hLn
  have hpos : 0 < L.length := List.length_pos_iff.2 (hne L hL)
  simp only [Function.comp, hc, decide_eq_true_eq]
  omega

theorem reject_card (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (addr : List ℕ)
    (hM : 1 ≤ P.M) {v : ℕ} {bins : List (Finset ℕ × (ℕ × CFState))}
    {ls : List (List ℕ)} (hb : BinsRel P R Adj addr bins ls) (hnd : ls.flatten.Nodup)
    (hfree : ∀ L ∈ ls, cliquesIn Adj (P.M + 1) L.toFinset = ∅)
    (hrej : ∀ k (hk : k < bins.length), ¬ OkB P (AdjAt Adj v) v bins[k].1) :
    ls.countP (fun L => decide (L.length < P.L)) ≤ (Cset P (AdjAt Adj v) v bins).card := by
  obtain ⟨hl, hbk⟩ := hb
  rw [List.countP_eq_length_filter]
  have key : ∀ L ∈ ls.filter (fun L => decide (L.length < P.L)),
      ∃ t ∈ Cset P (AdjAt Adj v) v bins, t.Nonempty ∧ t ⊆ L.toFinset := by
    intro L hL
    rw [List.mem_filter] at hL
    obtain ⟨hL, hlt⟩ := hL
    simp only [decide_eq_true_eq] at hlt
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hL
    have hk' : k < bins.length := hl ▸ hk
    have hbkk := hbk k hk' hk
    have hLn : ls[k].Nodup := (List.nodup_flatten.1 hnd).1 _ hL
    have hcard : ls[k].toFinset.card = ls[k].length := List.toFinset_card_of_nodup hLn
    have hne : cliquesIn (AdjAt Adj v) (P.M + 1) (insert v ls[k].toFinset) ≠ ∅ := by
      intro h0
      apply hrej k hk'
      rw [hbkk]
      unfold OkB binSt
      exact ⟨(by rw [hcard]; exact hlt : ls[k].toFinset.card < P.L), h0⟩
    obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.2 hne
    rw [mem_cliquesIn] at hs
    obtain ⟨hsS, hsc, hscl⟩ := hs
    have hvs : v ∈ s := by
      by_contra hvs
      have hsub' : s ⊆ ls[k].toFinset := (Finset.subset_insert_iff_of_notMem hvs).1 hsS
      have : s ∈ cliquesIn Adj (P.M + 1) ls[k].toFinset := by
        rw [mem_cliquesIn]
        exact ⟨hsub', hsc, fun a ha b hb' hab => (hscl a ha b hb' hab).2.2⟩
      rw [hfree _ hL] at this
      simp at this
    have herase : s.erase v ⊆ ls[k].toFinset := by
      intro x hx
      obtain ⟨hxv, hxs⟩ := Finset.mem_erase.1 hx
      rcases Finset.mem_insert.1 (hsS hxs) with h | h
      · exact absurd h hxv
      · exact h
    refine ⟨s.erase v, ?_, ?_, herase⟩
    · rw [mem_Cset]
      refine ⟨bins[k], List.getElem_mem hk', ?_, ?_⟩
      · rw [mem_cliquesIn]
        refine ⟨?_, ?_, ?_⟩
        · rw [hbkk]; exact herase
        · rw [Finset.card_erase_of_mem hvs, hsc]
          omega
        · intro a ha b hb' hab
          exact hscl a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb') hab
      · intro u hu
        obtain ⟨huv, hus⟩ := Finset.mem_erase.1 hu
        exact hscl v hvs u hus (Ne.symm huv)
    · rw [← Finset.card_pos, Finset.card_erase_of_mem hvs, hsc]
      omega
  choose! f hf using key
  have hpw : List.Pairwise List.Disjoint (ls.filter (fun L => decide (L.length < P.L))) :=
    (List.nodup_flatten.1 hnd).2.sublist List.filter_sublist
  have hnd' : ((ls.filter (fun L => decide (L.length < P.L))).map f).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    refine hpw.imp_of_mem ?_
    intro L1 L2 h1 h2 hd heq
    obtain ⟨_, hne1, hs1⟩ := hf L1 h1
    obtain ⟨_, _, hs2⟩ := hf L2 h2
    obtain ⟨x, hx⟩ := hne1
    have hx1 := List.mem_toFinset.1 (hs1 hx)
    have hx2 := List.mem_toFinset.1 (hs2 (heq ▸ hx))
    exact hd hx1 hx2
  calc (ls.filter (fun L => decide (L.length < P.L))).length
      = ((ls.filter (fun L => decide (L.length < P.L))).map f).length := by simp
    _ = ((ls.filter (fun L => decide (L.length < P.L))).map f).toFinset.card :=
        (List.toFinset_card_of_nodup hnd').symm
    _ ≤ _ := by
      apply Finset.card_le_card
      intro t ht
      rw [List.mem_toFinset, List.mem_map] at ht
      obtain ⟨L, hL, rfl⟩ := ht
      exact (hf L hL).1

theorem cliquesIn_single (Adj : ℕ → ℕ → Prop) (M v : ℕ) (hM : 1 ≤ M) :
    cliquesIn Adj (M + 1) ({v} : Finset ℕ) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro t ht
  rw [mem_cliquesIn] at ht
  have := Finset.card_le_card ht.1
  rw [ht.2.1, Finset.card_singleton] at this
  omega

theorem bstep (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (addr : List ℕ) (k n : ℕ)
    (hM : 1 ≤ P.M) (hL : 1 ≤ P.L) {H : List ℕ} {ls : List (List ℕ)}
    {insCB : List (ℕ × Finset (Finset ℕ))} {s : Inst} {cs : List Color}
    (hI : BInv P R Adj addr k n H ls insCB s cs) (v : ℕ) (Cv : Finset (Finset ℕ))
    (hv : ∀ h ∈ H, h < v) :
    ∃ ls' insCB', BInv P R Adj addr k n (H ++ [v]) ls' insCB'
        (locStep P R (AdjAt Adj v) v (.locP k n) addr Cv s).1
        (cs ++ [(locStep P R (AdjAt Adj v) v (.locP k n) addr Cv s).2.1]) ∧
      ((insCB' = insCB ∧ (locStep P R (AdjAt Adj v) v (.locP k n) addr Cv s).2.2 = none) ∨
        ∃ C, insCB' = insCB ++ [(v, C)] ∧
          (locStep P R (AdjAt Adj v) v (.locP k n) addr Cv s).2.2 =
            (locStep P R (AdjAt Adj v) v (.cb k k (nuOf P k n)) (addr ++ [8, 0, 0]) C
              (cbRun P R Adj addr k n insCB).1).2.2.map (fun o => (∅, Out.verts o))) := by
  obtain ⟨bins, hn, hb⟩ := hI.st
  have hvf : v ∉ ls.flatten := by
    intro h
    obtain ⟨l, hl, hvl⟩ := List.mem_flatten.1 h
    exact lt_irrefl v (hv v ((hI.each l hl).2.2.2.1 v hvl))
  have heachH : ∀ l ∈ ls, l ≠ [] ∧ l.length ≤ P.L ∧ l.Pairwise (· < ·) ∧ (∀ x ∈ l, x ∈ H ++ [v]) ∧
      cliquesIn Adj (P.M + 1) l.toFinset = ∅ := by
    intro l hl
    obtain ⟨a, b, c, d, e⟩ := hI.each l hl
    exact ⟨a, b, c, fun x hx => List.mem_append_left _ (d x hx), e⟩
  have hcbvH : (insCB.map Prod.fst).Sublist (H ++ [v]) := hI.cbv.trans (List.sublist_append_left H [v])
  rcases step_big_cases P R (AdjAt Adj v) v k n addr Cv s bins _ hn with
    ⟨hrej, hinc, heq⟩ | ⟨j, hj, hok, heq⟩ | ⟨hinc, heq⟩ <;> rw [heq]
  · -- the CB instance colors `v`
    refine ⟨ls, insCB ++ [(v, Cset P (AdjAt Adj v) v bins)],
      { st := ⟨bins, by rw [cbRun_snoc]; rfl, hb⟩, nodup := hI.nodup, each := heachH, inc := hI.inc,
        cbv := ?_, cbC := ?_, size := ?_, cols := ?_ }, Or.inr ⟨_, rfl, rfl⟩⟩
    · simpa using hI.cbv.append (List.Sublist.refl [v])
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hI.cbC x hx
      rw [List.mem_singleton] at hx
      subst hx
      refine ⟨?_, ?_⟩
      · rw [← hinc, incOf_eq hb hI.nodup (fun l hl => (hI.each l hl).1)]
        exact reject_card P R Adj addr hM hb hI.nodup (fun l hl => (hI.each l hl).2.2.2.2) hrej
      · intro S hS
        rw [mem_Cset] at hS
        obtain ⟨b, hbm, hS, -⟩ := hS
        rw [mem_cliquesIn] at hS
        obtain ⟨l, hl, hbl⟩ := binsRel_mem hb hbm
        exact ⟨hS.2.1, l, hl, hbl ▸ hS.1⟩
    · have := hI.size
      simp only [List.length_append, List.length_singleton]
      omega
    · intro c hc
      rcases List.mem_append.1 hc with hc | hc
      · rcases hI.cols c hc with h | h
        · exact Or.inl h
        · right; rw [cbRun_snoc]; exact List.mem_append_left _ h
      · rw [List.mem_singleton] at hc
        subst hc
        right; rw [cbRun_snoc]; simp
  · -- `v` joins bin `j`
    obtain ⟨hbl, hbk⟩ := hb
    have hjl : j < ls.length := hbl ▸ hj
    have hbj := hbk j hj hjl
    have hLn : ls[j].Nodup := (List.nodup_flatten.1 hI.nodup).1 _ (List.getElem_mem hjl)
    have hcard : ls[j].toFinset.card = ls[j].length := List.toFinset_card_of_nodup hLn
    rw [hbj] at hok ⊢
    unfold OkB binSt at hok
    simp only at hok
    have hperm := flatten_set_perm v ls j hjl
    have hg := grow_set ls j hjl v
    have hold := hI.each _ (List.getElem_mem hjl)
    refine ⟨ls.set j (ls[j] ++ [v]), insCB,
      { st := ⟨_, rfl, ?_, ?_⟩, nodup := ?_, each := ?_, inc := ?_, cbv := hcbvH,
        cbC := ?_, size := ?_, cols := ?_ }, Or.inl ⟨rfl, rfl⟩⟩
    · simp [hbl]
    · intro i h1 h2
      rw [List.getElem_set, List.getElem_set]
      split_ifs with hij
      · subst hij; rw [binSt_snoc]
      · exact hbk i (by simpa using h1) (by simpa using h2)
    · rw [hperm.nodup_iff, List.nodup_append]
      exact ⟨hI.nodup, List.nodup_singleton v, fun a ha b hb hab => by
        simp at hb; subst hb; subst hab; exact hvf ha⟩
    · intro L hL
      rcases List.mem_or_eq_of_mem_set hL with hL | rfl
      · exact heachH L hL
      refine ⟨by simp, by simp; omega, ?_, ?_, ?_⟩
      · rw [List.pairwise_append]
        exact ⟨hold.2.2.1, by simp, fun a ha b hb => by
          simp at hb; subst hb; exact hv a (hold.2.2.2.1 a ha)⟩
      · intro x hx
        rcases List.mem_append.1 hx with h | h
        · exact List.mem_append_left _ (hold.2.2.2.1 x h)
        · exact List.mem_append_right _ h
      · rw [toFinset_concat, ← cliquesIn_adjAt Adj v, hok.2]
        intro a ha
        rcases Finset.mem_insert.1 ha with rfl | ha
        · exact le_rfl
        · exact le_of_lt (hv a (hold.2.2.2.1 a (List.mem_toFinset.1 ha)))
    · have h1 := List.countP_set (p := fun L => decide (L.length < P.L)) (a := ls[j] ++ [v]) hjl
      have h2 := hI.inc
      split_ifs at h1 with ha hb1 hb2
      · have := (List.countP_pos_iff (p := fun L => decide (L.length < P.L))).2
          ⟨ls[j], List.getElem_mem hjl, ha⟩
        omega
      · omega
      · simp at ha hb2; omega
      · omega
    · intro x hx
      obtain ⟨h1, h3⟩ := hI.cbC x hx
      exact ⟨h1, fun S hS => ⟨(h3 S hS).1, grow_mem hg (h3 S hS).2⟩⟩
    · have := hI.size
      rw [hperm.length_eq]
      simp only [List.length_append, List.length_singleton]
      omega
    · intro c hc
      rcases List.mem_append.1 hc with hc | hc
      · rcases hI.cols c hc with h | h
        · exact Or.inl (binCols_grow P R Adj addr hg h)
        · exact Or.inr h
      · rw [List.mem_singleton] at hc
        subst hc
        left
        refine ⟨j, by simpa using hjl, ?_⟩
        rw [List.getElem_set_self, binCols_snoc]
        simp [binSt]
  · -- a new bin
    have hinc' := incOf_eq hb hI.nodup (fun L hL => (hI.each L hL).1)
    obtain ⟨hbl, hbk⟩ := hb
    have hg := grow_append ls [v]
    refine ⟨ls ++ [[v]], insCB,
      { st := ⟨_, rfl, ?_, ?_⟩, nodup := ?_, each := ?_, inc := ?_, cbv := hcbvH,
        cbC := ?_, size := ?_, cols := ?_ }, Or.inl ⟨rfl, rfl⟩⟩
    · simp [hbl]
    · intro i h1 h2
      by_cases hi : i < bins.length
      · rw [List.getElem_append_left hi, List.getElem_append_left (hbl ▸ hi)]
        exact hbk i hi (hbl ▸ hi)
      · have hi1 : i = bins.length := by simp at h1; omega
        subst hi1
        rw [List.getElem_concat_length rfl, List.getElem_concat_length hbl]
        rw [show ([v] : List ℕ) = [] ++ [v] from rfl, binSt_snoc, binSt_nil]
        rfl
    · rw [List.flatten_append, List.nodup_append]
      refine ⟨hI.nodup, by simp, fun a ha b hb hab => ?_⟩
      simp at hb; subst hb; subst hab; exact hvf ha
    · intro L hL
      rcases List.mem_append.1 hL with hL | hL
      · exact heachH L hL
      rw [List.mem_singleton] at hL
      subst hL
      refine ⟨by simp, by simp; omega, by simp, by simp, ?_⟩
      simpa using cliquesIn_single Adj P.M v hM
    · rw [List.countP_append]
      have h1 := List.countP_le_length (p := fun L => decide (L.length < P.L)) (l := [[v]])
      have h2 := hI.inc
      simp only [List.length_singleton] at h1
      omega
    · intro x hx
      obtain ⟨h1, h3⟩ := hI.cbC x hx
      exact ⟨h1, fun S hS => ⟨(h3 S hS).1, grow_mem hg (h3 S hS).2⟩⟩
    · have := hI.size
      simp only [List.flatten_append, List.length_append, List.length_singleton,
        List.flatten_cons, List.flatten_nil, List.append_nil]
      omega
    · intro c hc
      rcases List.mem_append.1 hc with hc | hc
      · rcases hI.cols c hc with h | h
        · exact Or.inl (binCols_grow P R Adj addr hg h)
        · exact Or.inr h
      · rw [List.mem_singleton] at hc
        subst hc
        left
        refine ⟨ls.length, by simp, ?_⟩
        rw [List.getElem_concat_length rfl]
        rw [show ([v] : List ℕ) = [] ++ [v] from rfl, binCols_snoc, binSt_nil, ← hbl]
        exact List.mem_append_right _ (List.mem_singleton_self _)

theorem brun (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (addr : List ℕ) (k n : ℕ)
    (hM : 1 ≤ P.M) (hL : 1 ≤ P.L) (xs : List (ℕ × Finset (Finset ℕ))) :
    ∀ (H : List ℕ) (ls : List (List ℕ)) (insCB : List (ℕ × Finset (Finset ℕ))) (s : Inst)
      (cs : List Color),
      BInv P R Adj addr k n H ls insCB s cs → (∀ o ∈ (cbRun P R Adj addr k n insCB).2.2, o = none) →
      (H ++ xs.map Prod.fst).Pairwise (· < ·) →
      (∀ o ∈ (instRun P R Adj (.locP k n) addr xs s).2.2, o = none) →
      ∃ ls' insCB', BInv P R Adj addr k n (H ++ xs.map Prod.fst) ls' insCB'
        (instRun P R Adj (.locP k n) addr xs s).1 (cs ++ (instRun P R Adj (.locP k n) addr xs s).2.1) ∧
        ∀ o ∈ (cbRun P R Adj addr k n insCB').2.2, o = none := by
  induction xs with
  | nil => intro H ls insCB s cs hI hc _ _; exact ⟨ls, insCB, by simpa [instRun] using hI, hc⟩
  | cons x xs ih =>
    intro H ls insCB s cs hI hc hs ho
    simp only [instRun, List.mem_cons, forall_eq_or_imp] at ho
    have hv : ∀ h ∈ H, h < x.1 := by
      intro h hh
      rw [List.map_cons, List.pairwise_append] at hs
      exact hs.2.2 h hh x.1 List.mem_cons_self
    obtain ⟨ls1, insCB1, h1, hd⟩ := bstep P R Adj addr k n hM hL hI x.1 x.2 hv
    have hc1 : ∀ o ∈ (cbRun P R Adj addr k n insCB1).2.2, o = none := by
      rcases hd with ⟨rfl, -⟩ | ⟨C, rfl, hout⟩
      · exact hc
      · rw [ho.1] at hout
        rw [cbRun_snoc]
        intro o hoo
        rcases List.mem_append.1 hoo with h | h
        · exact hc o h
        · rw [List.mem_singleton] at h
          subst h
          cases h' : (locStep P R (AdjAt Adj x.1) x.1 (.cb k k (nuOf P k n)) (addr ++ [8, 0, 0]) C
            (cbRun P R Adj addr k n insCB).1).2.2 with
          | none => rfl
          | some o => rw [h'] at hout; simp at hout
    obtain ⟨ls2, insCB2, h2, hc2⟩ := ih (H ++ [x.1]) ls1 insCB1 _ _ h1 hc1 (by simpa using hs) ho.2
    refine ⟨ls2, insCB2, ?_, hc2⟩
    simpa [instRun] using h2

/-! ## Counting for Algorithm 5 -/
theorem mem_foldr_union (l : List (Finset (Finset ℕ))) (x : Finset ℕ) :
    x ∈ l.foldr (· ∪ ·) ∅ ↔ ∃ s ∈ l, x ∈ s := by
  induction l with
  | nil => simp
  | cons s l ih => simp [ih]

theorem mem_foldr_union' {β : Type} (g : β → Finset (Finset ℕ)) (l : List β) (x : Finset ℕ) :
    x ∈ l.foldr (fun L acc => g L ∪ acc) ∅ ↔ ∃ L ∈ l, x ∈ g L := by
  induction l with
  | nil => simp
  | cons s l ih => simp [ih]

theorem card_foldr_union_le {β : Type} (g : β → Finset (Finset ℕ)) (l : List β) :
    (l.foldr (fun L acc => g L ∪ acc) ∅).card ≤ (l.map (fun L => (g L).card)).sum := by
  induction l with
  | nil => simp
  | cons s l ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left ih _)

theorem mem_inVerts (ins : List (ℕ × Finset (Finset ℕ))) (y : ℕ) :
    y ∈ inVerts ins ↔ ∃ x ∈ ins, ∃ S ∈ x.2, y ∈ S := by
  induction ins with
  | nil => simp [inVerts]
  | cons x xs ih =>
    simp only [inVerts, List.map_cons, List.foldr_cons] at ih ⊢
    rw [Finset.mem_union, ih, Finset.mem_sup]
    simp

theorem union_bound (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (addr : List ℕ) (k n : ℕ)
    (hM : 1 ≤ P.M) {H : List ℕ} {ls : List (List ℕ)}
    {insCB : List (ℕ × Finset (Finset ℕ))} {s : Inst} {cs : List Color}
    (hI : BInv P R Adj addr k n H ls insCB s cs) :
    ((insCB.map Prod.snd).foldr (· ∪ ·) ∅).card ≤ ls.flatten.length * P.L ^ (P.M - 1) := by
  have hsub2 : (insCB.map Prod.snd).foldr (· ∪ ·) ∅ ⊆
      ls.foldr (fun L acc => L.toFinset.powersetCard P.M ∪ acc) ∅ := by
    intro t ht
    rw [mem_foldr_union] at ht
    obtain ⟨s, hs, ht⟩ := ht
    rw [List.mem_map] at hs
    obtain ⟨a, ha, rfl⟩ := hs
    obtain ⟨hc1, L, hL, htL⟩ := (hI.cbC a ha).2 t ht
    rw [mem_foldr_union']
    exact ⟨L, hL, Finset.mem_powersetCard.2 ⟨htL, hc1⟩⟩
  calc _ ≤ _ := Finset.card_le_card hsub2
    _ ≤ (ls.map (fun L => (L.toFinset.powersetCard P.M).card)).sum := card_foldr_union_le _ _
    _ ≤ (ls.map (fun L => L.length * P.L ^ (P.M - 1))).sum := by
        apply List.sum_le_sum
        intro L hL
        rw [Finset.card_powersetCard]
        have h1 := List.toFinset_card_le L
        have h2 := (hI.each L hL).2.1
        obtain ⟨q, hq⟩ : ∃ q, P.M = q + 1 := ⟨P.M - 1, by omega⟩
        rw [hq, Nat.add_sub_cancel]
        calc L.toFinset.card.choose (q + 1) ≤ L.toFinset.card ^ (q + 1) := Nat.choose_le_pow _ _
          _ = L.toFinset.card * L.toFinset.card ^ q := by ring
          _ ≤ L.length * P.L ^ q :=
              Nat.mul_le_mul h1 (Nat.pow_le_pow_left (h1.trans h2) q)
    _ = (ls.map List.length).sum * P.L ^ (P.M - 1) := List.sum_map_mul_right _ _ _
    _ = ls.flatten.length * P.L ^ (P.M - 1) := by rw [List.length_flatten]

theorem bins_count (c : ℕ) : ∀ ls : List (List ℕ),
    c * ls.length ≤ (ls.map List.length).sum + c * ls.countP (fun L => decide (L.length < c))
  | [] => by simp
  | L :: ls => by
    have ih := bins_count c ls
    simp only [List.length_cons, List.map_cons, List.sum_cons, List.countP_cons]
    split_ifs with h
    · nlinarith
    · simp at h
      nlinarith

theorem binColSet_card (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (addr : List ℕ)
    (hM : 1 ≤ P.M) (hL : nSeq P.M (P.M + 1) ≤ P.L) (hR : R.Valid)
    (hsymm : ∀ a b, Adj a b → Adj b a) (ls : List (List ℕ))
    (hls : ∀ l ∈ ls, l.Pairwise (· < ·) ∧ l.length ≤ P.L ∧ cliquesIn Adj (P.M + 1) l.toFinset = ∅) :
    (((Finset.range ls.length).biUnion
      (fun i => (binCols P R Adj addr i (ls.getD i [])).toFinset)).card : ℝ) ≤
      (P.L : ℝ) / P.M * ls.length := by
  have h1 : ((Finset.range ls.length).biUnion
      (fun i => (binCols P R Adj addr i (ls.getD i [])).toFinset)).card ≤
      ∑ i ∈ Finset.range ls.length, (binCols P R Adj addr i (ls.getD i [])).toFinset.card :=
    Finset.card_biUnion_le
  have h2 : ((∑ i ∈ Finset.range ls.length,
      (binCols P R Adj addr i (ls.getD i [])).toFinset.card : ℕ) : ℝ) ≤
      ∑ i ∈ Finset.range ls.length, (P.L : ℝ) / P.M := by
    rw [Nat.cast_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_range] at hi
    rw [List.getD_eq_getElem _ _ hi]
    obtain ⟨a, b, c⟩ := hls _ (List.getElem_mem hi)
    exact binCols_card P R Adj addr hM hL hR hsymm i _ a b c
  have h3 : (((Finset.range ls.length).biUnion
      (fun i => (binCols P R Adj addr i (ls.getD i [])).toFinset)).card : ℝ) ≤
      ((∑ i ∈ Finset.range ls.length,
      (binCols P R Adj addr i (ls.getD i [])).toFinset.card : ℕ) : ℝ) := by exact_mod_cast h1
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
  linarith

theorem Jof_pos (P : LocParams) (k n : ℕ) : 1 ≤ Jof P k n := le_max_left _ _

theorem Jof_le (P : LocParams) (k n : ℕ) (hL : 1 ≤ P.L) (hn : 1 ≤ n) : Jof P k n ≤ n := by
  unfold Jof
  apply max_le hn
  apply Nat.floor_le_of_le
  have h1 : (1 : ℝ) ≤ max (P.L : ℝ) ((n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ 5)) :=
    le_max_of_le_left (by exact_mod_cast hL)
  exact div_le_self (by positivity) h1

theorem bsummary (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (N : ℕ) (W F : ℝ)
    (hS : Std P R Adj N W F) (k n : ℕ) (hk : P.M < k)
    (IH : ∀ ν, Holds P R Adj N W F (.cb k k ν)) (addr : List ℕ)
    (ins : List (ℕ × Finset (Finset ℕ))) (hin : InOK P N W ins (.locP k n))
    (ls : List (List ℕ)) (insCB : List (ℕ × Finset (Finset ℕ))) (s : Inst) (cs : List Color)
    (outs : List (Option Out))
    (hI : BInv P R Adj addr k n (ins.map Prod.fst) ls insCB s cs)
    (hcs : (instRun P R Adj (.locP k n) addr ins Inst.fresh).2.1 = cs)
    (hout : (instRun P R Adj (.locP k n) addr ins Inst.fresh).2.2 = outs)
    (hlive : Live (cbRun P R Adj addr k n insCB).2.2)
    (hrel : ∀ o', outs.getLast? = some (some o') →
      ∃ o, (cbRun P R Adj addr k n insCB).2.2.getLast? = some (some o) ∧ o' = (∅, Out.verts o))
    (hnone : (∀ o', outs.getLast? ≠ some (some o')) →
      ∀ o, (cbRun P R Adj addr k n insCB).2.2.getLast? ≠ some (some o)) :
    Summary P R Adj N W F (.locP k n) addr ins := by
  obtain ⟨⟨hM2, hL1, hnL, hW1, hF1, hfB, hnu⟩, hR, hsymm⟩ := hS
  have hM : 1 ≤ P.M := by omega
  obtain ⟨hsort, hlenN, hkM2, hlen_n, hn1, hn2⟩ := hin
  have hJ1 := Jof_pos P k n
  have hJn := Jof_le P k n hL1 hn1
  have hJpos : (0 : ℝ) < (Jof P k n : ℝ) := by exact_mod_cast hJ1
  have hLpow : (1 : ℝ) ≤ (P.L : ℝ) ^ (P.M - 1) := one_le_pow₀ (by exact_mod_cast hL1)
  have hnuJ : nuOf P k n * (Jof P k n : ℝ) = 2 * (n : ℝ) * (P.L : ℝ) ^ (P.M - 1) := by
    unfold nuOf
    field_simp
  have hnu1 : 1 ≤ nuOf P k n := by
    unfold nuOf
    rw [le_div_iff₀ hJpos]
    have : (Jof P k n : ℝ) ≤ n := by exact_mod_cast hJn
    have hn0 : (0 : ℝ) ≤ n := by positivity
    nlinarith
  have hlenH : (ins.map Prod.fst).length = ins.length := by simp
  have hsize := hI.size
  rw [hlenH] at hsize
  -- the child's good inputs
  have hU := union_bound P R Adj addr k n hM hI
  have hflat : ls.flatten.length ≤ n := by omega
  have hInOK : InOK P N W insCB (.cb k k (nuOf P k n)) := by
    refine ⟨List.Pairwise.sublist hI.cbv hsort, by omega, hk.le, le_rfl, hk, hkM2, hnu1,
      hnu k n hk hkM2 hn1 hn2, ?_⟩
    intro x hx
    obtain ⟨hJx, hSx⟩ := hI.cbC x hx
    refine ⟨Finset.card_pos.1 (by omega), fun S hS => (hSx S hS).1, ?_⟩
    have h1 : ((((insCB.map Prod.snd).foldr (· ∪ ·) ∅).card : ℕ) : ℝ) ≤
        (n : ℝ) * (P.L : ℝ) ^ (P.M - 1) := by
      have : ((insCB.map Prod.snd).foldr (· ∪ ·) ∅).card ≤ n * P.L ^ (P.M - 1) :=
        hU.trans (Nat.mul_le_mul_right _ hflat)
      exact_mod_cast this
    have h2 : (Jof P k n : ℝ) ≤ (x.2.card : ℝ) := by exact_mod_cast hJx
    have h3 : nuOf P k n * (Jof P k n : ℝ) ≤ nuOf P k n * (x.2.card : ℝ) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have hn0 : (0 : ℝ) ≤ (n : ℝ) * (P.L : ℝ) ^ (P.M - 1) := by positivity
    linarith
  obtain ⟨nbc, extc, sizes, c1, c2, c3, c4, c5, c6, c7, c8⟩ :=
    IH (nuOf P k n) (addr ++ [8, 0, 0]) insCB hInOK hlive
  change ((cbRun P R Adj addr k n insCB).2.1.toFinset.card : ℝ) ≤ _ at c1
  change ((∀ o, (cbRun P R Adj addr k n insCB).2.2.getLast? ≠ some (some o)) → _) at c4
  change ∀ o, (cbRun P R Adj addr k n insCB).2.2.getLast? = some (some o) → _ at c8
  have hls : ∀ l ∈ ls, l.Pairwise (· < ·) ∧ l.length ≤ P.L ∧ cliquesIn Adj (P.M + 1) l.toFinset = ∅ :=
    fun l hl => ⟨(hI.each l hl).2.2.1, (hI.each l hl).2.1, (hI.each l hl).2.2.2.2⟩
  have hBC := binColSet_card P R Adj addr hM hnL hR hsymm ls hls
  refine ⟨ls.length + nbc, extc, sizes, ?_, ?_, ?_, ?_, ?_, ?_, c7, ?_⟩
  · rw [hcs]
    have hsub : cs.toFinset ⊆ (Finset.range ls.length).biUnion
        (fun i => (binCols P R Adj addr i (ls.getD i [])).toFinset) ∪
        (cbRun P R Adj addr k n insCB).2.1.toFinset := by
      intro c hc
      rw [List.mem_toFinset] at hc
      rcases hI.cols c hc with ⟨i, hi, hci⟩ | h
      · apply Finset.mem_union_left
        rw [Finset.mem_biUnion]
        refine ⟨i, Finset.mem_range.2 hi, ?_⟩
        rw [List.getD_eq_getElem _ _ hi, List.mem_toFinset]
        exact hci
      · exact Finset.mem_union_right _ (List.mem_toFinset.2 h)
    have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have h2 : (cs.toFinset.card : ℝ) ≤ (((Finset.range ls.length).biUnion
        (fun i => (binCols P R Adj addr i (ls.getD i [])).toFinset)).card : ℝ) +
        ((cbRun P R Adj addr k n insCB).2.1.toFinset.card : ℝ) := by exact_mod_cast h1
    push_cast
    nlinarith
  · have hown : ownBins P (.locP k n) = (Jof P k n : ℝ) := by simp [ownBins, not_le.2 hk]
    have hown0 : ownBins P (.cb k k (nuOf P k n)) = 0 := rfl
    rw [hown0, add_zero] at c2
    rw [hown]
    have hb := bins_count P.L ls
    have hbc : P.L * ls.length ≤ ls.flatten.length + P.L * Jof P k n := by
      rw [List.length_flatten]
      have := Nat.mul_le_mul_left P.L hI.inc
      omega
    have hL' : (0 : ℝ) < P.L := by exact_mod_cast hL1
    have hr : (ls.length : ℝ) ≤ (ls.flatten.length : ℝ) / P.L + Jof P k n := by
      rw [div_add' _ _ _ hL'.ne', le_div_iff₀ hL']
      have : ((P.L * ls.length : ℕ) : ℝ) ≤ ((ls.flatten.length + P.L * Jof P k n : ℕ) : ℝ) := by
        exact_mod_cast hbc
      push_cast at this
      linarith
    have hsz : ((ls.flatten.length : ℝ) + (insCB.length : ℝ)) ≤ (ins.length : ℝ) := by
      exact_mod_cast hsize
    have hdiv : (ls.flatten.length : ℝ) / P.L + (insCB.length : ℝ) / P.L ≤ (ins.length : ℝ) / P.L := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right hsz hL'.le
    push_cast
    linarith
  · have : ownExt (.cb k k (nuOf P k n)) = 0 := rfl
    rw [this] at c3
    simp only [ownExt]
    omega
  · intro h
    rw [hout] at h
    exact c4 (hnone h)
  · have : cntOf P.M W F (Real.logb 2 N) (.locP k n) =
        cntOf P.M W F (Real.logb 2 N) (.cb k k (nuOf P k n)) := by
      simp [cntOf, not_le.2 hk]
    rw [this]; exact c5
  · have : depOf P.M (.locP k n) = depOf P.M (.cb k k (nuOf P k n)) := rfl
    rw [this]
    exact c6.trans (Nat.mul_le_mul_right _ (by omega))
  · intro o' h
    rw [hout] at h
    obtain ⟨o, ho, rfl⟩ := hrel o' h
    obtain ⟨h1, h2, h3⟩ := c8 o ho
    refine ⟨h1, ?_, ?_⟩
    · intro y hy
      have hy' := h2 hy
      rw [Finset.mem_union] at hy'
      rw [List.mem_toFinset]
      rcases hy' with hy' | hy'
      · rw [List.mem_toFinset] at hy'
        exact hI.cbv.subset hy'
      · rw [mem_inVerts] at hy'
        obtain ⟨x, hx, S, hS, hyS⟩ := hy'
        obtain ⟨-, l, hl, hSl⟩ := (hI.cbC x hx).2 S hS
        exact (hI.each l hl).2.2.2.1 y (List.mem_toFinset.1 (hSl hyS))
    · rw [← fB_big P.M k hM hk]
      exact h3

theorem holds_big (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (N : ℕ) (W F : ℝ)
    (hS : Std P R Adj N W F) (k n : ℕ) (hk : P.M < k)
    (IH : ∀ ν, Holds P R Adj N W F (.cb k k ν)) : Holds P R Adj N W F (.locP k n) := by
  intro addr ins hin hlive
  have hS' := hS
  obtain ⟨⟨hM2, hL1, -, -, -, -, -⟩, -, -⟩ := hS'
  have hM : 1 ≤ P.M := by omega
  have hI0 : BInv P R Adj addr k n [] [] [] Inst.fresh [] := by
    refine ⟨⟨[], ?_, by simp [BinsRel]⟩, by simp, by simp, by simp, by simp, by simp, by simp,
      by simp⟩
    simp [Inst.normalize, Inst.initOf, not_le.2 hk, cbRun, instRun]
  have hc0 : ∀ o ∈ (cbRun P R Adj addr k n []).2.2, o = none := by simp [cbRun, instRun]
  rcases List.eq_nil_or_concat ins with rfl | ⟨xs, x, rfl⟩
  · refine bsummary P R Adj N W F hS k n hk IH addr [] hin [] [] Inst.fresh [] [] hI0
      (by simp [instRun]) (by simp [instRun]) (by simp [Live, cbRun, instRun]) ?_ ?_
    · intro o' h; simp at h
    · intro _ o h; simp [cbRun, instRun] at h
  rw [List.concat_eq_append] at hin hlive ⊢
  have hsort := hin.1
  unfold Live at hlive
  rw [instRun_snoc, List.dropLast_concat] at hlive
  obtain ⟨ls, insCB, hI, hc⟩ := brun P R Adj addr k n hM hL1 xs [] [] [] _ [] hI0 hc0
    (by simpa using (List.pairwise_append.1 (by simpa using hsort)).1) hlive
  simp only [List.nil_append] at hI
  have hv : ∀ h ∈ xs.map Prod.fst, h < x.1 := by
    intro h hh
    rw [List.map_append, List.pairwise_append] at hsort
    exact hsort.2.2 h hh x.1 (by simp)
  obtain ⟨ls', insCB', hI', hd⟩ := bstep P R Adj addr k n hM hL1 hI x.1 x.2 hv
  have hmap : (xs ++ [x]).map Prod.fst = xs.map Prod.fst ++ [x.1] := by simp
  rw [← hmap] at hI'
  rcases hd with ⟨rfl, hnone⟩ | ⟨C, rfl, hout⟩
  · refine bsummary P R Adj N W F hS k n hk IH addr (xs ++ [x]) hin ls' _ _ _ _ hI'
      (by rw [instRun_snoc]) (by rw [instRun_snoc]) ?_ ?_ ?_
    · intro o ho; exact hc o (List.dropLast_subset _ ho)
    · intro o' h
      rw [List.getLast?_concat, hnone] at h
      simp at h
    · intro _ o h
      have := hc _ (List.mem_of_getLast? h)
      simp at this
  · refine bsummary P R Adj N W F hS k n hk IH addr (xs ++ [x]) hin ls' (insCB ++ [(x.1, C)]) _ _ _ hI'
      (by rw [instRun_snoc]) (by rw [instRun_snoc]) ?_ ?_ ?_
    · intro o ho
      rw [cbRun_snoc, List.dropLast_concat] at ho
      exact hc o ho
    · intro o' h
      rw [List.getLast?_concat, hout] at h
      simp only [Option.some.injEq, Option.map_eq_some_iff] at h
      obtain ⟨o, ho, rfl⟩ := h
      refine ⟨o, ?_, rfl⟩
      rw [cbRun_snoc, List.getLast?_concat, ho]
    · intro hno o h
      rw [cbRun_snoc, List.getLast?_concat] at h
      simp only [Option.some.injEq] at h
      apply hno (∅, Out.verts o)
      rw [List.getLast?_concat, hout, h]
      rfl

end OnlineColoringKYY.Supplement.Dev.T626.PartSB
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626
open Classical OnlineColoringKYY.Supplement
alias holds_big := OnlineColoringKYY.Supplement.Dev.T626.PartSB.holds_big

end OnlineColoringKYY.Supplement.Dev.T626
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartLC
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
variable (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (v : ℕ) (addr : List ℕ)
  (Cv : Finset (Finset ℕ))
/-! ## Unfolding lemmas -/
theorem step_loc_lt (k t cnt : ℕ) (cur : Inst) (h : cnt < 2 ^ t) :
    locStep P R Adj v (.loc k) addr Cv (.loc t cnt cur) =
      (.loc t (cnt + 1) (locStep P R Adj v (.locP k (2 ^ t)) (addr ++ [3, t, 0]) ∅ cur).1,
        (locStep P R Adj v (.locP k (2 ^ t)) (addr ++ [3, t, 0]) ∅ cur).2.1,
        (locStep P R Adj v (.locP k (2 ^ t)) (addr ++ [3, t, 0]) ∅ cur).2.2) := by
  conv_lhs => rw [locStep]
  simp [Nat.not_le.2 h]

theorem step_loc_full (k t cnt : ℕ) (cur : Inst) (h : 2 ^ t ≤ cnt) :
    locStep P R Adj v (.loc k) addr Cv (.loc t cnt cur) =
      locStep P R Adj v (.loc k) addr Cv (.loc (t + 1) 0 .fresh) := by
  conv_lhs => rw [locStep]
  conv_rhs => rw [locStep]
  simp [h]

theorem normalize_idem (m : Mode) (s : Inst) :
    Inst.normalize P m (Inst.normalize P m s) = Inst.normalize P m s := by
  cases s <;> try rfl
  cases m <;> simp only [Inst.normalize, Inst.initOf] <;> split_ifs <;> rfl

theorem step_normalize (m : Mode) (s : Inst) :
    locStep P R Adj v m addr Cv s = locStep P R Adj v m addr Cv (Inst.normalize P m s) := by
  conv_lhs => rw [locStep.eq_def]
  conv_rhs => rw [locStep.eq_def]
  rw [normalize_idem]

theorem step_loc_fresh (k : ℕ) :
    locStep P R Adj v (.loc k) addr Cv .fresh =
      locStep P R Adj v (.loc k) addr Cv (.loc 0 0 .fresh) :=
  step_normalize P R Adj v addr Cv _ _

theorem step_cb_fresh (k ℓ : ℕ) (ν : ℝ) (hℓ : ℓ ≤ P.M) :
    locStep P R Adj v (.cb k ℓ ν) addr Cv .fresh =
      locStep P R Adj v (.cb k ℓ ν) addr Cv (.cbBase .fresh []) := by
  rw [step_normalize]
  simp [Inst.normalize, Inst.initOf, hℓ]

theorem step_cbBase (k ℓ : ℕ) (ν : ℝ) (h0 : 0 < P.M) (hk : P.M ≤ k) (s : Inst)
    (cs : List (ℕ × Finset (Finset ℕ))) :
    locStep P R Adj v (.cb k ℓ ν) addr Cv (.cbBase s cs) =
      (.cbBase (locStep P R Adj v (.loc (k - P.M)) (addr ++ [4, 0, 0]) ∅ s).1 (cs ++ [(v, Cv)]),
        (locStep P R Adj v (.loc (k - P.M)) (addr ++ [4, 0, 0]) ∅ s).2.1,
        (locStep P R Adj v (.loc (k - P.M)) (addr ++ [4, 0, 0]) ∅ s).2.2.map
          (fun o => (o.2.image (fun x => R.adj addr x (lookupC (cs ++ [(v, Cv)]) x)), o.2))) := by
  conv_lhs => rw [locStep]
  simp [h0, hk]

end OnlineColoringKYY.Supplement.Dev.T626.PartLC
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartLC
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
variable (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (addr : List ℕ)
/-! ## Run lemmas -/
abbrev Inp : Type := List (ℕ × Finset (Finset ℕ))

def strip (ins : Inp) : Inp := ins.map (fun x => (x.1, (∅ : Finset (Finset ℕ))))

@[simp] theorem strip_fst (ins : Inp) : (strip ins).map Prod.fst = ins.map Prod.fst := by
  simp [strip]

@[simp] theorem strip_length (ins : Inp) : (strip ins).length = ins.length := by
  simp [strip]

@[simp] theorem strip_nil : strip [] = [] := rfl

@[simp] theorem strip_cons (x : ℕ × Finset (Finset ℕ)) (xs : Inp) :
    strip (x :: xs) = (x.1, ∅) :: strip xs := rfl

theorem instRun_append (m : Mode) (xs ys : Inp) (s : Inst) :
    instRun P R Adj m addr (xs ++ ys) s =
      ((instRun P R Adj m addr ys (instRun P R Adj m addr xs s).1).1,
        (instRun P R Adj m addr xs s).2.1 ++
          (instRun P R Adj m addr ys (instRun P R Adj m addr xs s).1).2.1,
        (instRun P R Adj m addr xs s).2.2 ++
          (instRun P R Adj m addr ys (instRun P R Adj m addr xs s).1).2.2) := by
  induction xs generalizing s with
  | nil => simp [instRun]
  | cons x xs ih => simp [instRun, ih]

theorem instRun_len (m : Mode) (xs : Inp) (s : Inst) :
    (instRun P R Adj m addr xs s).2.2.length = xs.length := by
  induction xs generalizing s with
  | nil => simp [instRun]
  | cons x xs ih => simp [instRun, ih]

theorem instRun_congr (m : Mode) (s1 s2 : Inst)
    (h : ∀ v A Cv, locStep P R A v m addr Cv s1 = locStep P R A v m addr Cv s2) (xs : Inp) :
    (instRun P R Adj m addr xs s1).2 = (instRun P R Adj m addr xs s2).2 := by
  cases xs with
  | nil => simp [instRun]
  | cons x xs => simp [instRun, h]

theorem loc_chunk_run (k t cnt : ℕ) (cur : Inst) (ins : Inp) (h : cnt + ins.length ≤ 2 ^ t) :
    instRun P R Adj (.loc k) addr ins (.loc t cnt cur) =
      (.loc t (cnt + ins.length)
          (instRun P R Adj (.locP k (2 ^ t)) (addr ++ [3, t, 0]) (strip ins) cur).1,
        (instRun P R Adj (.locP k (2 ^ t)) (addr ++ [3, t, 0]) (strip ins) cur).2.1,
        (instRun P R Adj (.locP k (2 ^ t)) (addr ++ [3, t, 0]) (strip ins) cur).2.2) := by
  induction ins generalizing cnt cur with
  | nil => simp [instRun]
  | cons x xs ih =>
    simp only [List.length_cons] at h
    simp only [instRun, strip_cons]
    rw [step_loc_lt _ _ _ _ _ _ _ _ _ _ (by omega), ih (cnt + 1) _ (by omega)]
    simp only [Prod.mk.injEq, and_true]
    congr 1
    simp only [List.length_cons]
    omega

end OnlineColoringKYY.Supplement.Dev.T626.PartLC
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartLC
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
/-! ## Liveness helpers -/
theorem live_of_append {a b : List (Option Out)} (hb : b ≠ []) (h : Live (a ++ b)) :
    (∀ o ∈ a, o = none) ∧ Live b := by
  unfold Live at *
  rw [List.dropLast_append_of_ne_nil hb] at h
  exact ⟨fun o ho => h o (List.mem_append_left _ ho), fun o ho => h o (List.mem_append_right _ ho)⟩

theorem live_of_none {a : List (Option Out)} (h : ∀ o ∈ a, o = none) : Live a :=
  fun o ho => h o (List.dropLast_subset _ ho)

theorem getLast_of_none {a : List (Option Out)} (h : ∀ o ∈ a, o = none) (o : Out) :
    a.getLast? ≠ some (some o) := by
  intro h'
  have := h _ (List.mem_of_getLast? h')
  simp at this

theorem card_toFinset_append {α : Type} [DecidableEq α] (a b : List α) :
    ((a ++ b).toFinset.card : ℝ) ≤ a.toFinset.card + b.toFinset.card := by
  rw [List.toFinset_append]
  exact_mod_cast Finset.card_union_le _ _

end OnlineColoringKYY.Supplement.Dev.T626.PartLC
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartLC
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
variable (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (N : ℕ) (W F : ℝ) (k : ℕ)
  (addr : List ℕ)
/-! ## LOC(k): the chunk decomposition -/
/-- The instance-count bound of LOC′(k) (independent of `n`). -/
noncomputable def CP : ℝ := cntOf P.M W F (Real.logb 2 N) (.locP k 1)

theorem cntOf_locP (n : ℕ) : cntOf P.M W F (Real.logb 2 N) (.locP k n) = CP P N W F k := by
  simp [CP, cntOf]

theorem loc_chunks (IH : ∀ n, Holds P R Adj N W F (.locP k n)) (hk : k ≤ P.M ^ 2) :
    ∀ (n t : ℕ) (ins : Inp), ins.length = n → ins ≠ [] → (ins.map Prod.fst).Pairwise (· < ·) →
      2 ^ t + ins.length ≤ N + 1 →
      Live (instRun P R Adj (.loc k) addr ins (.loc t 0 .fresh)).2.2 →
      ∃ (T nb ext : ℕ) (sizes : List ℕ), t ≤ T ∧ 2 ^ T < ins.length + 2 ^ t ∧
        ins.length + 2 ^ t ≤ 2 ^ (T + 1) ∧
        ((instRun P R Adj (.loc k) addr ins (.loc t 0 .fresh)).2.1.toFinset.card : ℝ) ≤
          (P.L : ℝ) / P.M * nb + ext ∧
        (nb : ℝ) ≤ (ins.length : ℝ) / P.L +
          ∑ i ∈ Finset.Ico t (T + 1), ownBins P (.locP k (2 ^ i)) +
          (sizes.map (fun x : ℕ => 8 * ((x : ℕ) : ℝ) ^ (1 - 1 / (P.M : ℝ) ^ 10))).sum ∧
        ext ≤ sizes.length + 1 ∧
        ((∀ o, (instRun P R Adj (.loc k) addr ins (.loc t 0 .fresh)).2.2.getLast? ≠
          some (some o)) → ext ≤ sizes.length) ∧
        (sizes.length : ℝ) ≤ ((T : ℝ) + 1 - t) * CP P N W F k ∧
        sizes.sum ≤ ins.length * (k / P.M) ∧
        (∀ x ∈ sizes, 1 ≤ x ∧ x ≤ N) ∧
        (∀ o, (instRun P R Adj (.loc k) addr ins (.loc t 0 .fresh)).2.2.getLast? =
          some (some o) → OutOK P ins (.loc k) o) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro t ins hn hne hsort hN hlive
  have hlen : 0 < ins.length := List.length_pos_iff.2 hne
  have h2t : 0 < 2 ^ t := by positivity
  by_cases hle : ins.length ≤ 2 ^ t
  · have hrun := loc_chunk_run P R Adj addr k t 0 .fresh ins (by omega)
    rw [hrun] at hlive ⊢
    obtain ⟨nb, ext, sizes, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
      IH (2 ^ t) (addr ++ [3, t, 0]) (strip ins)
        ⟨by simpa using hsort, by simp; omega, hk, by simpa using hle, Nat.one_le_two_pow,
          by omega⟩ hlive
    refine ⟨t, nb, ext, sizes, le_rfl, by omega, by rw [pow_succ]; omega, h1, ?_, ?_, h4, ?_, ?_,
      h7, ?_⟩
    · simpa using h2
    · simpa [ownExt] using h3
    · rw [cntOf_locP] at h5; simpa using h5
    · simpa [depOf] using h6
    · intro o ho
      have := h8 o ho
      simpa [OutOK] using this
  · push Not at hle
    set c := ins.take (2 ^ t) with hc
    set r := ins.drop (2 ^ t) with hr
    have hclen : c.length = 2 ^ t := by simp [hc]; omega
    have hrlen : r.length = ins.length - 2 ^ t := by simp [hr]
    have hrne : r ≠ [] := by
      intro h; rw [h] at hrlen; simp at hrlen; omega
    have hsplit : ins = c ++ r := (List.take_append_drop _ _).symm
    have hcong := instRun_congr P R Adj addr (.loc k) (.loc t (0 + c.length)
        (instRun P R Adj (.locP k (2 ^ t)) (addr ++ [3, t, 0]) (strip c) .fresh).1)
      (.loc (t + 1) 0 .fresh)
      (fun v A Cv => step_loc_full P R A v addr Cv k t _ _ (by omega)) r
    have hrun : (instRun P R Adj (.loc k) addr ins (.loc t 0 .fresh)).2 =
        ((instRun P R Adj (.locP k (2 ^ t)) (addr ++ [3, t, 0]) (strip c) .fresh).2.1 ++
          (instRun P R Adj (.loc k) addr r (.loc (t + 1) 0 .fresh)).2.1,
         (instRun P R Adj (.locP k (2 ^ t)) (addr ++ [3, t, 0]) (strip c) .fresh).2.2 ++
          (instRun P R Adj (.loc k) addr r (.loc (t + 1) 0 .fresh)).2.2) := by
      conv_lhs => rw [hsplit, instRun_append, loc_chunk_run P R Adj addr k t 0 .fresh c (by omega)]
      simp only
      rw [hcong]
    have hcol := congrArg Prod.fst hrun
    have hout := congrArg Prod.snd hrun
    simp only at hcol hout
    rw [hcol, hout]
    rw [hout] at hlive
    have hrout : (instRun P R Adj (.loc k) addr r (.loc (t + 1) 0 .fresh)).2.2 ≠ [] := by
      rw [← List.length_pos_iff, instRun_len]; exact List.length_pos_iff.2 hrne
    obtain ⟨hnone, hliver⟩ := live_of_append hrout hlive
    obtain ⟨T, nb2, ext2, s2, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ :=
      ihn r.length (by omega) (t + 1) r rfl hrne
        (hsort.sublist ((List.drop_sublist _ _).map _))
        (by rw [pow_succ, hrlen]; omega) hliver
    obtain ⟨nb1, ext1, s1, f1, f2, f3, f4, f5, f6, f7, f8⟩ :=
      IH (2 ^ t) (addr ++ [3, t, 0]) (strip c)
        ⟨by simpa [hc] using hsort.sublist ((List.take_sublist (2 ^ t) ins).map Prod.fst),
          by simp; omega, hk,
          by simp; omega, Nat.one_le_two_pow, by omega⟩ (live_of_none hnone)
    have f4' := f4 (getLast_of_none hnone)
    have hlast : ∀ y, ((instRun P R Adj (.locP k (2 ^ t)) (addr ++ [3, t, 0]) (strip c) .fresh).2.2 ++
          (instRun P R Adj (.loc k) addr r (.loc (t + 1) 0 .fresh)).2.2).getLast? = y ↔
        (instRun P R Adj (.loc k) addr r (.loc (t + 1) 0 .fresh)).2.2.getLast? = y := by
      intro y; rw [List.getLast?_append_of_ne_nil _ hrout]
    have hlenR : (ins.length : ℝ) = c.length + r.length := by
      rw [hsplit, List.length_append]; push_cast; ring
    refine ⟨T, nb1 + nb2, ext1 + ext2, s1 ++ s2, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [pow_succ] at g1; omega
    · rw [pow_succ] at g2; omega
    · refine (card_toFinset_append _ _).trans ?_
      push_cast
      linarith
    · rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]
      simp only [List.map_append, List.sum_append, strip_length] at f2 ⊢
      rw [hlenR, add_div]
      push_cast
      linarith
    · simp only [List.length_append]; simp only [ownExt] at f3; omega
    · intro hno
      have := g6 (fun o h => hno o ((hlast _).2 h))
      simp only [List.length_append]; omega
    · rw [cntOf_locP] at f5
      have e : ((T : ℝ) + 1 - t) * CP P N W F k =
          CP P N W F k + ((T : ℝ) + 1 - ((t + 1 : ℕ) : ℝ)) * CP P N W F k := by push_cast; ring
      rw [e, List.length_append]; push_cast; linarith
    · rw [List.sum_append]
      simp only [depOf, strip_length] at f6
      have : ins.length = c.length + r.length := by rw [hsplit, List.length_append]
      rw [this, add_mul]
      exact Nat.add_le_add f6 g8
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact f7 x hx
      · exact g9 x hx
    · intro o ho
      have h := g10 o ((hlast _).1 ho)
      simp only [OutOK] at h ⊢
      refine ⟨h.1, h.2.1.trans ?_, h.2.2⟩
      intro y hy
      simp only [List.mem_toFinset] at hy ⊢
      exact ((List.drop_sublist _ _).map _).subset hy

end OnlineColoringKYY.Supplement.Dev.T626.PartLC
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartLC
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
/-! ## Numerics -/
theorem cC_nonneg (M : ℕ) (W F : ℝ) (k : ℕ) (fL : ℕ → ℝ) (hW : 0 ≤ W) (hF : 0 ≤ F)
    (hf : ∀ j, 0 ≤ fL j) : ∀ ℓ, 0 ≤ cC M W F k fL ℓ := by
  intro ℓ
  induction ℓ with
  | zero => simp [cC, hf]
  | succ ℓ ih =>
    simp only [cC]
    split_ifs
    · exact hf _
    · exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hW) (hf _))
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hW) hF) ih)

theorem cL_nonneg (M : ℕ) (W F lg : ℝ) (hW : 0 ≤ W) (hF : 0 ≤ F) (hlg : 0 ≤ lg) :
    ∀ k, 0 ≤ cL M W F lg k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [cL]
    split_ifs
    · norm_num
    · have := cC_nonneg M W F k (fun j => if _h : j < k then cL M W F lg j else 0) hW hF (fun j => by
        split_ifs with h
        exacts [ih j h, le_rfl]) k
      exact add_nonneg zero_le_one (mul_nonneg (by linarith) this)

theorem lg_nonneg (N : ℕ) : 0 ≤ Real.logb 2 N := by
  rcases N.eq_zero_or_pos with h | h
  · simp [h]
  · exact Real.logb_nonneg one_lt_two (by exact_mod_cast h)

theorem cL_bound (M : ℕ) (W F lg : ℝ) (hW : 0 ≤ W) (hF : 0 ≤ F) (k T : ℕ) (hT : (T : ℝ) ≤ lg) :
    1 + ((T : ℝ) + 1) * cntOf M W F lg (.locP k 1) ≤ cL M W F lg k := by
  rw [cL]
  by_cases h : k ≤ M
  · simp [cntOf, h]
  · simp only [cntOf, h, if_false]
    have hC := cC_nonneg M W F k (fun j => if _h : j < k then cL M W F lg j else 0) hW hF
      (fun j => by
        split_ifs with h
        exacts [cL_nonneg M W F lg hW hF ((Nat.cast_nonneg T).trans hT) j, le_rfl]) k
    have := mul_le_mul_of_nonneg_right (show (T : ℝ) + 1 ≤ lg + 1 by linarith) hC
    linarith

theorem Jof_le (P : LocParams) (k n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    (Jof P k n : ℝ) ≤ (n : ℝ) ^ (1 - 1 / (k : ℝ) ^ 5) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hk5 : (1 : ℝ) ≤ (k : ℝ) ^ 5 := one_le_pow₀ (by exact_mod_cast hk)
  have he : 1 / (k : ℝ) ^ 5 ≤ 1 := by rw [div_le_one (by linarith)]; exact hk5
  have hpos : 0 < (n : ℝ) ^ (1 / (k : ℝ) ^ 5) := Real.rpow_pos_of_pos (by linarith) _
  unfold Jof
  rw [Nat.cast_max, Nat.cast_one]
  apply max_le
  · exact Real.one_le_rpow hn' (by linarith)
  · refine (Nat.floor_le (by positivity)).trans ?_
    rw [Real.rpow_sub (by linarith), Real.rpow_one]
    exact div_le_div_of_nonneg_left (by linarith) hpos (le_max_right _ _)

theorem pow_rpow_eq (δ : ℝ) (i : ℕ) : ((2 : ℝ) ^ (1 - δ)) ^ i = (((2 ^ i : ℕ) : ℕ) : ℝ) ^ (1 - δ) := by
  rw [← Real.rpow_mul_natCast (by norm_num), Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num), mul_comm]

theorem delta_le (M : ℕ) (hM : 2 ≤ M) : 1 / (M : ℝ) ^ 10 ≤ 1 / 2 := by
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have : (2 : ℝ) ≤ (M : ℝ) ^ 10 := le_trans hM' (le_self_pow₀ (by linarith) (by norm_num))
  exact one_div_le_one_div_of_le (by norm_num) this

theorem ownBins_le (P : LocParams) (hM : 2 ≤ P.M) (k : ℕ) (hk : k ≤ P.M ^ 2) (i : ℕ) :
    ownBins P (.locP k (2 ^ i)) ≤ ((2 : ℝ) ^ (1 - 1 / (P.M : ℝ) ^ 10)) ^ i := by
  have hδ := delta_le P.M hM
  have hδ0 : 0 ≤ 1 / (P.M : ℝ) ^ 10 := by positivity
  rw [pow_rpow_eq]
  have hn1 : (1 : ℝ) ≤ ((2 ^ i : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
  simp only [ownBins]
  split_ifs with h
  · exact Real.one_le_rpow hn1 (by linarith)
  · push Not at h
    refine (Jof_le P k (2 ^ i) (by omega) Nat.one_le_two_pow).trans ?_
    apply Real.rpow_le_rpow_of_exponent_le hn1
    have h1 : k ^ 5 ≤ P.M ^ 10 := by
      calc k ^ 5 ≤ (P.M ^ 2) ^ 5 := Nat.pow_le_pow_left hk 5
        _ = P.M ^ 10 := by ring
    have h2 : (k : ℝ) ^ 5 ≤ (P.M : ℝ) ^ 10 := by exact_mod_cast h1
    have h3 : 1 / (P.M : ℝ) ^ 10 ≤ 1 / (k : ℝ) ^ 5 :=
      one_div_le_one_div_of_le (pow_pos (by exact_mod_cast (by omega : 0 < k)) 5) h2
    linarith

theorem ownBins_sum (P : LocParams) (hM : 2 ≤ P.M) (k : ℕ) (hk : k ≤ P.M ^ 2) (T x : ℕ)
    (hx : 2 ^ T ≤ x) :
    ∑ i ∈ Finset.range (T + 1), ownBins P (.locP k (2 ^ i)) ≤
      8 * (x : ℝ) ^ (1 - 1 / (P.M : ℝ) ^ 10) := by
  have hδ := delta_le P.M hM
  have hδ0 : 0 ≤ 1 / (P.M : ℝ) ^ 10 := by positivity
  refine (Finset.sum_le_sum (fun i _ => ownBins_le P hM k hk i)).trans ?_
  set δ := 1 / (P.M : ℝ) ^ 10 with hδdef
  have haT : ((2 : ℝ) ^ (1 - δ)) ^ T ≤ (x : ℝ) ^ (1 - δ) := by
    rw [pow_rpow_eq]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hx) (by linarith)
  set a := (2 : ℝ) ^ (1 - δ) with ha
  have ha0 : 0 < a := by positivity
  have ha2 : 2 ≤ a ^ 2 := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    calc (2 : ℝ) = 2 ^ (1 : ℝ) := by simp
      _ ≤ 2 ^ ((1 - δ) * ((2 : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
  have ha87 : 8 / 7 ≤ a := by nlinarith
  rw [geom_sum_eq (by linarith : a ≠ 1) (T + 1), div_le_iff₀ (by linarith), pow_succ]
  nlinarith [mul_le_mul_of_nonneg_right haT (show 0 ≤ a - 1 by linarith), pow_nonneg ha0.le T]

/-! ## Theorem: LOC(k) -/
theorem holds_loc (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (N : ℕ) (W F : ℝ)
    (hS : Std P R Adj N W F) (k : ℕ) (IH : ∀ n, Holds P R Adj N W F (.locP k n)) :
    Holds P R Adj N W F (.loc k) := by
  intro addr ins hin hlive
  obtain ⟨hsort, hlenN, hk⟩ := hin
  obtain ⟨⟨hM, hL, -, hW, hF, -, -⟩, -, -⟩ := hS
  have hcong := instRun_congr P R Adj addr (.loc k) .fresh (.loc 0 0 .fresh)
    (fun v A Cv => step_loc_fresh P R A v addr Cv k) ins
  unfold Summary
  rw [hcong]
  rw [hcong] at hlive
  by_cases hne : ins = []
  · subst hne
    refine ⟨0, 0, [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [instRun]
    · simp [ownBins]
    · simp
    · simp
    · simpa [cntOf] using cL_nonneg P.M W F _ (by linarith) (by linarith) (lg_nonneg N) k
    · simp
    · simp
    · simp [instRun]
  · obtain ⟨T, nb, ext, sizes, -, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ :=
      loc_chunks P R Adj N W F k addr IH hk ins.length 0 ins rfl hne hsort (by simp; omega) hlive
    have hlen : 0 < ins.length := List.length_pos_iff.2 hne
    simp only [pow_zero] at g1
    have hTx : 2 ^ T ≤ ins.length := by omega
    have hTN : (T : ℝ) ≤ Real.logb 2 N := by
      rw [Real.le_logb_iff_rpow_le one_lt_two (by exact_mod_cast (by omega : 0 < N)),
        Real.rpow_natCast]
      exact_mod_cast hTx.trans hlenN
    refine ⟨nb, ext, ins.length :: sizes, g3, ?_, ?_, ?_, ?_, ?_, ?_, g10⟩
    · have hs := ownBins_sum P hM k hk T ins.length hTx
      rw [Finset.range_eq_Ico] at hs
      simp only [List.map_cons, List.sum_cons, ownBins]
      linarith
    · simp only [List.length_cons, ownExt]; omega
    · intro hno; have := g6 hno; simp only [List.length_cons]; omega
    · have hb := cL_bound P.M W F (Real.logb 2 N) (by linarith) (by linarith) k T hTN
      simp only [CP] at g7
      simp only [List.length_cons, cntOf]
      push_cast
      simp only [Nat.cast_zero, sub_zero] at g7
      linarith
    · simp only [List.sum_cons, depOf, mul_add, mul_one]
      linarith
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨hlen, hlenN⟩
      · exact g9 x hx

end OnlineColoringKYY.Supplement.Dev.T626.PartLC
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626
open Classical OnlineColoringKYY.Supplement
alias holds_loc := OnlineColoringKYY.Supplement.Dev.T626.PartLC.holds_loc

end OnlineColoringKYY.Supplement.Dev.T626
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartLC
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
variable (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (addr : List ℕ)
/-! ## CB(k, M, ν) -/
theorem cb_run (k ℓ : ℕ) (ν : ℝ) (h0 : 0 < P.M) (hk : P.M ≤ k) (ins : Inp) :
    ∀ (s : Inst) (cs : Inp),
    (instRun P R Adj (.cb k ℓ ν) addr ins (.cbBase s cs)).2.1 =
      (instRun P R Adj (.loc (k - P.M)) (addr ++ [4, 0, 0]) (strip ins) s).2.1 ∧
    (instRun P R Adj (.cb k ℓ ν) addr ins (.cbBase s cs)).2.2.map Option.isSome =
      (instRun P R Adj (.loc (k - P.M)) (addr ++ [4, 0, 0]) (strip ins) s).2.2.map Option.isSome ∧
    (instRun P R Adj (.cb k ℓ ν) addr ins (.cbBase s cs)).2.2.getLast? =
      (instRun P R Adj (.loc (k - P.M)) (addr ++ [4, 0, 0]) (strip ins) s).2.2.getLast?.map
        (Option.map (fun o => (o.2.image (fun x => R.adj addr x (lookupC (cs ++ ins) x)), o.2))) := by
  induction ins with
  | nil => intro s cs; simp [instRun]
  | cons x xs ih =>
    intro s cs
    obtain ⟨ih1, ih2, ih3⟩ := ih
      (locStep P R (AdjAt Adj x.1) x.1 (.loc (k - P.M)) (addr ++ [4, 0, 0]) ∅ s).1 (cs ++ [x])
    simp only [instRun, strip_cons, step_cbBase P R _ x.1 addr x.2 k ℓ ν h0 hk, Prod.mk.eta]
    refine ⟨by rw [ih1], by simp [ih2], ?_⟩
    rw [List.getLast?_cons, List.getLast?_cons, ih3]
    cases xs with
    | nil => simp [instRun]
    | cons y ys =>
      obtain ⟨z, hz⟩ : ∃ z, (instRun P R Adj (.loc (k - P.M)) (addr ++ [4, 0, 0]) (strip (y :: ys))
          (locStep P R (AdjAt Adj x.1) x.1 (.loc (k - P.M)) (addr ++ [4, 0, 0]) ∅ s).1).2.2.getLast?
            = some z := by
        apply Option.ne_none_iff_exists'.1
        rw [Ne, List.getLast?_eq_none_iff, ← List.length_eq_zero_iff, instRun_len]
        simp
      rw [hz]
      simp [List.append_assoc]

theorem live_of_isSome {a b : List (Option Out)} (h : a.map Option.isSome = b.map Option.isSome)
    (ha : Live a) : Live b := by
  intro o ho
  have h' : a.dropLast.map Option.isSome = b.dropLast.map Option.isSome := by
    rw [List.map_dropLast, h, ← List.map_dropLast]
  have : o.isSome ∈ a.dropLast.map Option.isSome := by
    rw [h']; exact List.mem_map_of_mem ho
  obtain ⟨o', ho', he⟩ := List.mem_map.1 this
  rw [ha o' ho'] at he
  cases o with
  | none => rfl
  | some _ => simp at he

theorem mem_inVerts (ins : Inp) (y : ℕ) (p : ℕ × Finset (Finset ℕ)) (hp : p ∈ ins)
    (hy : y ∈ p.2.sup id) : y ∈ inVerts ins := by
  induction ins with
  | nil => simp at hp
  | cons q qs ih =>
    simp only [inVerts, List.map_cons, List.foldr_cons, Finset.mem_union] at ih ⊢
    rcases List.mem_cons.1 hp with rfl | hp
    · exact Or.inl hy
    · exact Or.inr (ih hp)

theorem lookupC_mem (ins : Inp) (x : ℕ) (hx : x ∈ ins.map Prod.fst) :
    ∃ p ∈ ins, lookupC ins x = p.2 := by
  unfold lookupC
  cases h : ins.find? (fun p => p.1 = x) with
  | none =>
    exfalso
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    have := List.find?_eq_none.1 h p hp
    simp at this
  | some p => exact ⟨p, List.mem_of_find?_eq_some h, by simp⟩

end OnlineColoringKYY.Supplement.Dev.T626.PartLC
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartLC
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
theorem holds_cbBase (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (N : ℕ) (W F : ℝ)
    (hS : Std P R Adj N W F) (k ℓ : ℕ) (ν : ℝ) (hℓ : ℓ ≤ P.M)
    (IH : Holds P R Adj N W F (.loc (k - P.M))) : Holds P R Adj N W F (.cb k ℓ ν) := by
  intro addr ins hin hlive
  obtain ⟨hsort, hlenN, hMℓ, -, hMk, hkM2, -, -, hC⟩ := hin
  obtain ⟨⟨hM, -, -, -, -, -, -⟩, hR, -⟩ := hS
  have h0 : 0 < P.M := by omega
  have hcong := instRun_congr P R Adj addr (.cb k ℓ ν) .fresh (.cbBase .fresh [])
    (fun v A Cv => step_cb_fresh P R A v addr Cv k ℓ ν hℓ) ins
  obtain ⟨e1, e2, e3⟩ := cb_run P R Adj addr k ℓ ν h0 hMk.le ins .fresh []
  rw [← hcong] at e1 e2 e3
  simp only [List.nil_append] at e3
  have hlive' := live_of_isSome e2 hlive
  obtain ⟨nb, ext, sizes, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    IH (addr ++ [4, 0, 0]) (strip ins) ⟨by simpa using hsort, by simpa using hlenN, by omega⟩ hlive'
  obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
  unfold Summary
  rw [e1, e3]
  refine ⟨nb, ext, sizes, h1, by simpa [ownBins] using h2, by simpa [ownExt] using h3, ?_, ?_, ?_,
    h7, ?_⟩
  · intro hno
    apply h4
    intro o ho
    apply hno (o.2.image (fun x => R.adj addr x (lookupC ins x)), o.2)
    rw [ho]; rfl
  · have hlt : k - P.M < k := by omega
    simpa [cntOf, cC, hℓ, hlt] using h5
  · have : (k - P.M) / P.M + 1 = k / P.M := by
      rw [← Nat.add_div_right _ h0, Nat.sub_add_cancel hMk.le]
    simpa [depOf, this] using h6
  · intro o' ho'
    simp only [Option.map_eq_some_iff] at ho'
    obtain ⟨y, hy, o, rfl, rfl⟩ := ho'
    obtain ⟨hne, hsub, hcard⟩ := h8 o hy
    simp only [strip_fst] at hsub
    -- each chosen clique
    have key : ∀ x ∈ o.2, R.adj addr x (lookupC ins x) ⊆ inVerts ins ∧
        (R.adj addr x (lookupC ins x)).card = P.M := by
      intro x hx
      have hx' : x ∈ ins.map Prod.fst := by simpa using hsub hx
      obtain ⟨p, hp, hpe⟩ := lookupC_mem ins x hx'
      obtain ⟨hpne, hpM, -⟩ := hC p hp
      rw [hpe]
      have hmem := hR.2.2.1 addr x p.2 hpne
      refine ⟨fun y hy => mem_inVerts ins y p hp ?_, hpM _ hmem⟩
      exact (Finset.le_sup (f := id) hmem) hy
    simp only [OutOK, Out.verts]
    refine ⟨hne.mono Finset.subset_union_right, ?_, ?_⟩
    · apply Finset.union_subset
      · apply Finset.sup_le
        intro S hS
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hS
        exact (key x hx).1.trans Finset.subset_union_right
      · intro y hy
        exact Finset.mem_union_left _ (by simpa using hsub hy)
    · refine (Finset.card_union_le _ _).trans ?_
      have hA : ((o.2.image (fun x => R.adj addr x (lookupC ins x))).sup id).card ≤
          P.M * o.2.card := by
        rw [Finset.sup_image, Finset.sup_eq_biUnion]
        refine Finset.card_biUnion_le.trans ?_
        simp only [Function.comp_apply, id_eq]
        rw [Finset.sum_congr rfl (fun x hx => (key x hx).2), Finset.sum_const, smul_eq_mul,
          mul_comm]
      simp only [gB, hℓ, if_true]
      nlinarith

end OnlineColoringKYY.Supplement.Dev.T626.PartLC
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626
open Classical OnlineColoringKYY.Supplement
alias holds_cbBase := OnlineColoringKYY.Supplement.Dev.T626.PartLC.holds_cbBase

end OnlineColoringKYY.Supplement.Dev.T626
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartCS
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
/-! ## Lemma 6.13 -/
theorem union_lb {α : Type} [DecidableEq α] (ν : ℝ) (hν : 0 < ν) (f : ℕ → Finset α) (s : ℕ)
    (hint : ∀ i j, i < j → j < s → 2 * ν * ((f i ∩ f j).card : ℝ) ≤ (f i).card) :
    ∀ m, m ≤ s → ∑ i ∈ Finset.range m, ((f i).card : ℝ) * (1 - ((m : ℝ) - 1 - i) / (2 * ν)) ≤
      (((Finset.range m).biUnion f).card : ℝ) := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have ih := ih (by omega)
    rw [Finset.range_add_one, Finset.biUnion_insert]
    have h1 := Finset.card_union_add_card_inter (f m) ((Finset.range m).biUnion f)
    have h2 : ((f m ∩ (Finset.range m).biUnion f).card : ℝ) ≤
        ∑ i ∈ Finset.range m, ((f i).card : ℝ) / (2 * ν) := by
      rw [Finset.inter_biUnion]
      refine (Nat.cast_le.2 Finset.card_biUnion_le).trans ?_
      push_cast
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mem_range] at hi
      rw [le_div_iff₀ (by positivity), Finset.inter_comm, mul_comm]
      exact hint i m hi (by omega)
    have e : ∑ i ∈ Finset.range m, ((f i).card : ℝ) * (1 - (((m + 1 : ℕ) : ℝ) - 1 - i) / (2 * ν)) =
        ∑ i ∈ Finset.range m, ((f i).card : ℝ) * (1 - ((m : ℝ) - 1 - i) / (2 * ν)) -
          ∑ i ∈ Finset.range m, ((f i).card : ℝ) / (2 * ν) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      push_cast
      field_simp
      ring
    rw [Finset.sum_insert Finset.notMem_range_self, e]
    have h1' : ((f m ∪ (Finset.range m).biUnion f).card : ℝ) +
        ((f m ∩ (Finset.range m).biUnion f).card : ℝ) =
          (f m).card + ((Finset.range m).biUnion f).card := by exact_mod_cast h1
    have e2 : ((m + 1 : ℕ) : ℝ) - 1 - m = 0 := by push_cast; ring
    rw [e2]
    simp only [zero_div, sub_zero, mul_one]
    linarith

theorem sum_range_cast (s : ℕ) : ∑ i ∈ Finset.range s, (i : ℝ) = (s : ℝ) * ((s : ℝ) - 1) / 2 := by
  induction s with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- Paper's Lemma 6.13 (from KYY27). -/
theorem kyy_lemma {α : Type} [DecidableEq α] (ν : ℝ) (hν : 1 ≤ ν) (S : Finset α)
    (A : List (Finset α)) (hsub : ∀ a ∈ A, a ⊆ S) (hbig : ∀ a ∈ A, (S.card : ℝ) ≤ ν * a.card)
    (hS : S.Nonempty)
    (hint : ∀ i j (hi : i < A.length) (hj : j < A.length), i < j →
      2 * ν * ((A.get ⟨i, hi⟩ ∩ A.get ⟨j, hj⟩).card : ℝ) < (A.get ⟨i, hi⟩).card) :
    (A.length : ℝ) < 2 * ν := by
  by_contra hcon
  push Not at hcon
  have hν0 : 0 < ν := by linarith
  set s := ⌈2 * ν⌉₊ with hs
  have hs1 : 2 * ν ≤ s := Nat.le_ceil _
  have hs2 : (s : ℝ) < 2 * ν + 1 := Nat.ceil_lt_add_one (by positivity)
  have hsn : s ≤ A.length := Nat.ceil_le.2 hcon
  set f : ℕ → Finset α := fun i => A.getD i ∅ with hfdef
  have hf : ∀ i (hi : i < A.length), f i = A.get ⟨i, hi⟩ := by
    intro i hi; simp [f, List.getElem?_eq_getElem hi]
  have hint' : ∀ i j, i < j → j < s → 2 * ν * ((f i ∩ f j).card : ℝ) ≤ (f i).card := by
    intro i j hij hj
    rw [hf i (by omega), hf j (by omega)]
    exact (hint i j _ _ hij).le
  have hlb := union_lb ν hν0 f s hint' s le_rfl
  have hsub' : (Finset.range s).biUnion f ⊆ S := by
    intro y hy
    obtain ⟨i, hi, hy⟩ := Finset.mem_biUnion.1 hy
    rw [Finset.mem_range] at hi
    rw [hf i (by omega)] at hy
    exact hsub _ (List.get_mem _ _) hy
  have hcard : (((Finset.range s).biUnion f).card : ℝ) ≤ S.card := by
    exact_mod_cast Finset.card_le_card hsub'
  have hbig' : ∀ i < s, (S.card : ℝ) / ν ≤ (f i).card := by
    intro i hi
    rw [div_le_iff₀ hν0, mul_comm, hf i (by omega)]
    exact hbig _ (List.get_mem _ _)
  have hterm : ∀ i ∈ Finset.range s, (S.card : ℝ) / ν * (1 - ((s : ℝ) - 1 - i) / (2 * ν)) ≤
      ((f i).card : ℝ) * (1 - ((s : ℝ) - 1 - i) / (2 * ν)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    apply mul_le_mul_of_nonneg_right (hbig' i hi)
    have : ((s : ℝ) - 1 - i) / (2 * ν) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      linarith
    linarith
  have hsum := Finset.sum_le_sum hterm
  have e : ∀ i ∈ Finset.range s, (S.card : ℝ) / ν * (1 - ((s : ℝ) - 1 - i) / (2 * ν)) =
      (S.card : ℝ) / ν * (1 - ((s : ℝ) - 1) / (2 * ν)) + (S.card : ℝ) / (2 * ν ^ 2) * i := by
    intro i _
    field_simp
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    ← Finset.mul_sum, sum_range_cast, nsmul_eq_mul] at hsum
  have hx : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  set x : ℝ := (S.card : ℝ)
  have key : x < x * s * (4 * ν - s + 1) / (4 * ν ^ 2) := by
    rw [lt_div_iff₀ (by positivity)]
    have : (s : ℝ) * (4 * ν - s + 1) - 4 * ν ^ 2 = ((s : ℝ) - 2 * ν) * (2 * ν + 1 - s) + 2 * ν := by
      ring
    have h3 : 0 ≤ ((s : ℝ) - 2 * ν) * (2 * ν + 1 - s) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have e3 : (s : ℝ) * (x / ν * (1 - ((s : ℝ) - 1) / (2 * ν))) +
      x / (2 * ν ^ 2) * ((s : ℝ) * ((s : ℝ) - 1) / 2) = x * s * (4 * ν - s + 1) / (4 * ν ^ 2) := by
    field_simp
    ring
  linarith

end OnlineColoringKYY.Supplement.Dev.T626.PartCS
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626
open Classical OnlineColoringKYY.Supplement

end OnlineColoringKYY.Supplement.Dev.T626
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartCS
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
/-! ## Basic helpers (copied from PartLC / PartSB) -/
abbrev Inp : Type := List (ℕ × Finset (Finset ℕ))

abbrev Sub : Type := ℕ × ℕ × Finset (Finset ℕ) × Inst × Option Out

def key (e : Sub) : ℕ × ℕ := (e.1, e.2.1)

def strip (ins : Inp) : Inp := ins.map (fun x => (x.1, (∅ : Finset (Finset ℕ))))

@[simp] theorem strip_fst (ins : Inp) : (strip ins).map Prod.fst = ins.map Prod.fst := by
  simp [strip]

@[simp] theorem strip_length (ins : Inp) : (strip ins).length = ins.length := by
  simp [strip]

@[simp] theorem strip_nil : strip [] = [] := rfl

theorem strip_append (xs ys : Inp) : strip (xs ++ ys) = strip xs ++ strip ys := by
  simp [strip]

end OnlineColoringKYY.Supplement.Dev.T626.PartCS
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartCS
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
variable (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop)
theorem instRun_append (m : Mode) (addr : List ℕ) (xs ys : Inp) (s : Inst) :
    instRun P R Adj m addr (xs ++ ys) s =
      ((instRun P R Adj m addr ys (instRun P R Adj m addr xs s).1).1,
        (instRun P R Adj m addr xs s).2.1 ++
          (instRun P R Adj m addr ys (instRun P R Adj m addr xs s).1).2.1,
        (instRun P R Adj m addr xs s).2.2 ++
          (instRun P R Adj m addr ys (instRun P R Adj m addr xs s).1).2.2) := by
  induction xs generalizing s with
  | nil => simp [instRun]
  | cons x xs ih => simp [instRun, ih]

theorem instRun_snoc (m : Mode) (addr : List ℕ) (xs : Inp) (x : ℕ × Finset (Finset ℕ)) (s : Inst) :
    instRun P R Adj m addr (xs ++ [x]) s =
      ((locStep P R (AdjAt Adj x.1) x.1 m addr x.2 (instRun P R Adj m addr xs s).1).1,
        (instRun P R Adj m addr xs s).2.1 ++
          [(locStep P R (AdjAt Adj x.1) x.1 m addr x.2 (instRun P R Adj m addr xs s).1).2.1],
        (instRun P R Adj m addr xs s).2.2 ++
          [(locStep P R (AdjAt Adj x.1) x.1 m addr x.2 (instRun P R Adj m addr xs s).1).2.2]) := by
  rw [instRun_append]; simp [instRun]

theorem instRun_len (m : Mode) (addr : List ℕ) (xs : Inp) (s : Inst) :
    (instRun P R Adj m addr xs s).2.2.length = xs.length := by
  induction xs generalizing s with
  | nil => simp [instRun]
  | cons x xs ih => simp [instRun, ih]

@[simp] theorem instRun_nil (m : Mode) (addr : List ℕ) (s : Inst) :
    instRun P R Adj m addr [] s = (s, [], []) := rfl

end OnlineColoringKYY.Supplement.Dev.T626.PartCS
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartCS
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
theorem live_of_append {a b : List (Option Out)} (hb : b ≠ []) (h : Live (a ++ b)) :
    (∀ o ∈ a, o = none) ∧ Live b := by
  unfold Live at *
  rw [List.dropLast_append_of_ne_nil hb] at h
  exact ⟨fun o ho => h o (List.mem_append_left _ ho), fun o ho => h o (List.mem_append_right _ ho)⟩

theorem live_of_none {a : List (Option Out)} (h : ∀ o ∈ a, o = none) : Live a :=
  fun o ho => h o (List.dropLast_subset _ ho)

theorem live_snoc {a : List (Option Out)} (h : ∀ o ∈ a, o = none) (y : Option Out) :
    Live (a ++ [y]) := by
  intro o ho
  rw [List.dropLast_concat] at ho
  exact h o ho

theorem none_of_live {a : List (Option Out)} (h : Live a) (h2 : a.getLast?.getD none = none) :
    ∀ o ∈ a, o = none := by
  intro o ho
  rcases List.eq_nil_or_concat a with rfl | ⟨L, b, rfl⟩
  · simp at ho
  · simp only [List.concat_eq_append] at h h2 ho
    rw [List.getLast?_concat] at h2
    simp only [Option.getD_some] at h2
    rcases List.mem_append.1 ho with ho | ho
    · apply h; rw [List.dropLast_concat]; exact ho
    · simp at ho; rw [ho, h2]

theorem mem_inVerts (ins : Inp) (y : ℕ) :
    y ∈ inVerts ins ↔ ∃ x ∈ ins, ∃ S ∈ x.2, y ∈ S := by
  induction ins with
  | nil => simp [inVerts]
  | cons x xs ih =>
    simp only [inVerts, List.map_cons, List.foldr_cons] at ih ⊢
    rw [Finset.mem_union, ih, Finset.mem_sup]
    simp

theorem mem_foldr_union (l : List (Finset (Finset ℕ))) (x : Finset ℕ) :
    x ∈ l.foldr (· ∪ ·) ∅ ↔ ∃ s ∈ l, x ∈ s := by
  induction l with
  | nil => simp
  | cons s l ih => simp [ih]

theorem lookupC_eq (ins : Inp) (hnd : (ins.map Prod.fst).Nodup) (p : ℕ × Finset (Finset ℕ))
    (hp : p ∈ ins) : lookupC ins p.1 = p.2 := by
  unfold lookupC
  cases h : ins.find? (fun q => q.1 = p.1) with
  | none =>
    exfalso
    have := List.find?_eq_none.1 h p hp
    simp at this
  | some q =>
    have hq := List.mem_of_find?_eq_some h
    have hq1 : q.1 = p.1 := by simpa using List.find?_some h
    have : q = p := List.inj_on_of_nodup_map hnd hq hp hq1
    simp [this]

theorem lookupQ_cases (Q : List (ℕ × Finset ℕ)) (i : ℕ) :
    lookupQ Q i = ∅ ∨ ∃ q ∈ Q, lookupQ Q i = q.2 := by
  unfold lookupQ
  cases h : Q.find? (fun p => p.1 = i) with
  | none => simp
  | some q => exact Or.inr ⟨q, List.mem_of_find?_eq_some h, by simp⟩

/-! ## Numerics (copied from PartLC) -/
theorem cC_nonneg (M : ℕ) (W F : ℝ) (k : ℕ) (fL : ℕ → ℝ) (hW : 0 ≤ W) (hF : 0 ≤ F)
    (hf : ∀ j, 0 ≤ fL j) : ∀ ℓ, 0 ≤ cC M W F k fL ℓ := by
  intro ℓ
  induction ℓ with
  | zero => simp [cC, hf]
  | succ ℓ ih =>
    simp only [cC]
    split_ifs
    · exact hf _
    · exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hW) (hf _))
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hW) hF) ih)

theorem cL_nonneg (M : ℕ) (W F lg : ℝ) (hW : 0 ≤ W) (hF : 0 ≤ F) (hlg : 0 ≤ lg) :
    ∀ k, 0 ≤ cL M W F lg k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [cL]
    split_ifs
    · norm_num
    · have := cC_nonneg M W F k (fun j => if _h : j < k then cL M W F lg j else 0) hW hF (fun j => by
        split_ifs with h
        exacts [ih j h, le_rfl]) k
      exact add_nonneg zero_le_one (mul_nonneg (by linarith) this)

theorem lg_nonneg (N : ℕ) : 0 ≤ Real.logb 2 N := by
  rcases N.eq_zero_or_pos with h | h
  · simp [h]
  · exact Real.logb_nonneg one_lt_two (by exact_mod_cast h)

/-! ## Algorithm 6: one step -/
noncomputable def candOf (ν : ℝ) (subs : List Sub) (Cv : Finset (Finset ℕ)) : Finset (ℕ × ℕ) :=
  ((subs.filter (fun e =>
      e.2.2.2.2 = none ∧ ((e.2.2.1 ∩ Cv).card : ℝ) ≥ (e.2.2.1.card : ℝ) / (2 * ν))).map
    (fun e => (e.1, e.2.1))).toFinset

def famStep (f : Sub) (acc : Out) : Out := match f.2.2.2.2 with
  | some o => (acc.1 ∪ o.1, acc.2 ∪ o.2)
  | none => acc

def famOut (Q : List (ℕ × Finset ℕ)) (subs : List Sub) (i : ℕ) : Out :=
  (subs.filter (fun f => f.1 = i)).foldr famStep (∅, lookupQ Q i)

end OnlineColoringKYY.Supplement.Dev.T626.PartCS
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartCS
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
variable (P : LocParams) (R : Resolver) (A : ℕ → ℕ → Prop) (v : ℕ) (addr : List ℕ)
  (Cv : Finset (Finset ℕ)) (k ℓ : ℕ) (ν : ℝ) (s : Inst) (t : ℕ) (cur : Inst)
  (Q : List (ℕ × Finset ℕ)) (subs : List Sub) (cs : Inp)
theorem step_sub (hn : Inst.normalize P (.cb k ℓ ν) s = .cbStep t cur Q subs cs)
    (h : 0 < ℓ ∧ ℓ ≤ k) (hc : (candOf ν subs Cv).Nonempty) (idx : ℕ)
    (hidx : idx = subs.findIdx (fun e => decide ((e.1, e.2.1) = R.inst addr v (candOf ν subs Cv))))
    (e : Sub) (he : e = subs.getD idx (0, 0, ∅, Inst.fresh, none)) :
    locStep P R A v (.cb k ℓ ν) addr Cv s =
      (.cbStep t cur Q (subs.set idx (e.1, e.2.1, e.2.2.1,
          (locStep P R A v (.cb k (ℓ - 1) (2 * ν)) (addr ++ [5, e.1, e.2.1]) (e.2.2.1 ∩ Cv)
            e.2.2.2.1).1,
          (locStep P R A v (.cb k (ℓ - 1) (2 * ν)) (addr ++ [5, e.1, e.2.1]) (e.2.2.1 ∩ Cv)
            e.2.2.2.1).2.2)) (cs ++ [(v, Cv)]),
        (locStep P R A v (.cb k (ℓ - 1) (2 * ν)) (addr ++ [5, e.1, e.2.1]) (e.2.2.1 ∩ Cv)
            e.2.2.2.1).2.1,
        if ((subs.set idx (e.1, e.2.1, e.2.2.1,
          (locStep P R A v (.cb k (ℓ - 1) (2 * ν)) (addr ++ [5, e.1, e.2.1]) (e.2.2.1 ∩ Cv)
            e.2.2.2.1).1,
          (locStep P R A v (.cb k (ℓ - 1) (2 * ν)) (addr ++ [5, e.1, e.2.1]) (e.2.2.1 ∩ Cv)
            e.2.2.2.1).2.2)).filter (fun f => f.1 = e.1)).all (fun f => f.2.2.2.2.isSome) then
          some (famOut Q (subs.set idx (e.1, e.2.1, e.2.2.1,
          (locStep P R A v (.cb k (ℓ - 1) (2 * ν)) (addr ++ [5, e.1, e.2.1]) (e.2.2.1 ∩ Cv)
            e.2.2.2.1).1,
          (locStep P R A v (.cb k (ℓ - 1) (2 * ν)) (addr ++ [5, e.1, e.2.1]) (e.2.2.1 ∩ Cv)
            e.2.2.2.1).2.2)) e.1)
        else none) := by
  subst hidx he
  rw [locStep.eq_def, hn]
  simp only [dif_pos h]
  unfold candOf at hc
  rw [if_pos hc]
  rfl

theorem step_locN (hn : Inst.normalize P (.cb k ℓ ν) s = .cbStep t cur Q subs cs)
    (h : 0 < ℓ ∧ ℓ ≤ k) (hc : ¬ (candOf ν subs Cv).Nonempty)
    (hr : (locStep P R A v (.loc (k - ℓ)) (addr ++ [6, t, 0]) ∅ cur).2.2 = none) :
    locStep P R A v (.cb k ℓ ν) addr Cv s =
      (.cbStep t (locStep P R A v (.loc (k - ℓ)) (addr ++ [6, t, 0]) ∅ cur).1 Q subs
        (cs ++ [(v, Cv)]), (locStep P R A v (.loc (k - ℓ)) (addr ++ [6, t, 0]) ∅ cur).2.1, none) := by
  rw [locStep.eq_def, hn]
  simp only [dif_pos h]
  unfold candOf at hc
  rw [if_neg hc]
  simp only [hr]

theorem step_locS (hn : Inst.normalize P (.cb k ℓ ν) s = .cbStep t cur Q subs cs)
    (h : 0 < ℓ ∧ ℓ ≤ k) (hc : ¬ (candOf ν subs Cv).Nonempty) (o : Out)
    (hr : (locStep P R A v (.loc (k - ℓ)) (addr ++ [6, t, 0]) ∅ cur).2.2 = some o) :
    locStep P R A v (.cb k ℓ ν) addr Cv s =
      (.cbStep (t + 1) .fresh (Q ++ [(t, o.2)])
        (subs ++ o.2.toList.map (fun x => (t, x, lookupC (cs ++ [(v, Cv)]) x, Inst.fresh, none)))
        (cs ++ [(v, Cv)]), (locStep P R A v (.loc (k - ℓ)) (addr ++ [6, t, 0]) ∅ cur).2.1, none) := by
  rw [locStep.eq_def, hn]
  simp only [dif_pos h]
  unfold candOf at hc
  rw [if_neg hc]
  simp only [hr]

end OnlineColoringKYY.Supplement.Dev.T626.PartCS
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartCS
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
/-! ## List helpers -/
theorem map_set_self {α β : Type} (f : α → β) (l : List α) (i : ℕ) (hi : i < l.length) (a : α)
    (h : f a = f l[i]) : (l.set i a).map f = l.map f := by
  rw [List.map_set]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  rw [List.getElem_set]
  split_ifs with hj
  · subst hj; simp [h]
  · rfl

theorem mem_set_cases {α : Type} {l : List α} {i : ℕ} {a b : α} (h : b ∈ l.set i a) :
    b = a ∨ b ∈ l := (List.mem_or_eq_of_mem_set h).symm

theorem mem_set_of_ne {α : Type} {l : List α} {i : ℕ} (hi : i < l.length) {a b : α} (hb : b ∈ l)
    (hne : l[i] ≠ b) : b ∈ l.set i a := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
  have hji : i ≠ j := by rintro rfl; exact hne rfl
  have : (l.set i a)[j]'(by simpa using hj) = l[j] := List.getElem_set_ne hji _
  rw [← this]
  exact List.getElem_mem _

theorem mem_set_self {α : Type} {l : List α} {i : ℕ} (hi : i < l.length) (a : α) :
    a ∈ l.set i a := by
  have : (l.set i a)[i]'(by simpa using hi) = a := List.getElem_set_self _
  have h2 := List.getElem_mem (l := l.set i a) (by simpa using hi : i < (l.set i a).length)
  rwa [this] at h2

theorem filter_len_count (l : List Sub) (i : ℕ) :
    (l.filter (fun f => decide (f.1 = i))).length = (l.map (·.1)).count i := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.filter_cons, List.map_cons, List.count_cons]
    by_cases h : a.1 = i
    · simp [h, ih]
    · simp [h, ih]

theorem length_le_count (l : List ℕ) (s : Finset ℕ) (hs : ∀ a ∈ l, a ∈ s) (c : ℕ)
    (hc : ∀ i, l.count i ≤ c) : l.length ≤ s.card * c := by
  have : l.length = ∑ i ∈ s, l.count i := by
    clear hc
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.length_cons, List.count_cons]
      rw [ih (fun b hb => hs b (List.mem_cons_of_mem _ hb)), Finset.sum_add_distrib]
      simp only [beq_iff_eq]
      rw [Finset.sum_ite_eq s a]
      simp [hs a List.mem_cons_self]
  rw [this]
  calc ∑ i ∈ s, l.count i ≤ ∑ _i ∈ s, c := Finset.sum_le_sum (fun i _ => hc i)
    _ = s.card * c := by simp

end OnlineColoringKYY.Supplement.Dev.T626.PartCS
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartCS
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
variable (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (k ℓ : ℕ) (ν : ℝ) (addr : List ℕ)
/-! ## The run invariant of Algorithm 6 -/
/-- The run of the LOC(k − ℓ) instance of round `j`. -/
noncomputable def locR (j : ℕ) (g : Inp) : Inst × List Color × List (Option Out) :=
  instRun P R Adj (.loc (k - ℓ)) (addr ++ [6, j, 0]) (strip g) .fresh

/-- The run of the sub-instance with key `q`. -/
noncomputable def subR (q : ℕ × ℕ) (g : Inp) : Inst × List Color × List (Option Out) :=
  instRun P R Adj (.cb k (ℓ - 1) (2 * ν)) (addr ++ [5, q.1, q.2]) g .fresh

noncomputable def mainR (pre : Inp) : Inst × List Color × List (Option Out) :=
  instRun P R Adj (.cb k ℓ ν) addr pre .fresh

theorem locR_snoc (j : ℕ) (g : Inp) (x : ℕ × Finset (Finset ℕ)) :
    locR P R Adj k ℓ addr j (g ++ [x]) =
      ((locStep P R (AdjAt Adj x.1) x.1 (.loc (k - ℓ)) (addr ++ [6, j, 0]) ∅
          (locR P R Adj k ℓ addr j g).1).1,
        (locR P R Adj k ℓ addr j g).2.1 ++ [(locStep P R (AdjAt Adj x.1) x.1 (.loc (k - ℓ))
          (addr ++ [6, j, 0]) ∅ (locR P R Adj k ℓ addr j g).1).2.1],
        (locR P R Adj k ℓ addr j g).2.2 ++ [(locStep P R (AdjAt Adj x.1) x.1 (.loc (k - ℓ))
          (addr ++ [6, j, 0]) ∅ (locR P R Adj k ℓ addr j g).1).2.2]) := by
  unfold locR
  rw [strip_append]
  exact instRun_snoc P R Adj _ _ _ (x.1, ∅) _

theorem subR_snoc (q : ℕ × ℕ) (g : Inp) (x : ℕ × Finset (Finset ℕ)) :
    subR P R Adj k ℓ ν addr q (g ++ [x]) =
      ((locStep P R (AdjAt Adj x.1) x.1 (.cb k (ℓ - 1) (2 * ν)) (addr ++ [5, q.1, q.2]) x.2
          (subR P R Adj k ℓ ν addr q g).1).1,
        (subR P R Adj k ℓ ν addr q g).2.1 ++ [(locStep P R (AdjAt Adj x.1) x.1
          (.cb k (ℓ - 1) (2 * ν)) (addr ++ [5, q.1, q.2]) x.2 (subR P R Adj k ℓ ν addr q g).1).2.1],
        (subR P R Adj k ℓ ν addr q g).2.2 ++ [(locStep P R (AdjAt Adj x.1) x.1
          (.cb k (ℓ - 1) (2 * ν)) (addr ++ [5, q.1, q.2]) x.2
          (subR P R Adj k ℓ ν addr q g).1).2.2]) := by
  unfold subR
  exact instRun_snoc P R Adj _ _ _ _ _

theorem mainR_snoc (pre : Inp) (x : ℕ × Finset (Finset ℕ)) :
    mainR P R Adj k ℓ ν addr (pre ++ [x]) =
      ((locStep P R (AdjAt Adj x.1) x.1 (.cb k ℓ ν) addr x.2 (mainR P R Adj k ℓ ν addr pre).1).1,
        (mainR P R Adj k ℓ ν addr pre).2.1 ++
          [(locStep P R (AdjAt Adj x.1) x.1 (.cb k ℓ ν) addr x.2
            (mainR P R Adj k ℓ ν addr pre).1).2.1],
        (mainR P R Adj k ℓ ν addr pre).2.2 ++
          [(locStep P R (AdjAt Adj x.1) x.1 (.cb k ℓ ν) addr x.2
            (mainR P R Adj k ℓ ν addr pre).1).2.2]) := by
  unfold mainR
  exact instRun_snoc P R Adj _ _ _ _ _

structure Inv (pre : Inp) (t : ℕ) (Q : List (ℕ × Finset ℕ)) (subs : List Sub) (rnd : ℕ → Inp)
    (gin : ℕ × ℕ → Inp) : Prop where
  st : Inst.normalize P (.cb k ℓ ν) (mainR P R Adj k ℓ ν addr pre).1 =
    .cbStep t (locR P R Adj k ℓ addr t (rnd t)).1 Q subs pre
  t1 : 1 ≤ t
  rndE : ∀ j, t < j → rnd j = []
  rndS : ∀ j, (rnd j).Sublist pre
  fin : ∀ j, 1 ≤ j → j < t → Live (locR P R Adj k ℓ addr j (rnd j)).2.2
  curN : ∀ o ∈ (locR P R Adj k ℓ addr t (rnd t)).2.2, o = none
  ent : ∀ e ∈ subs, e.2.2.2.1 = (subR P R Adj k ℓ ν addr (key e) (gin (key e))).1 ∧
    Live (subR P R Adj k ℓ ν addr (key e) (gin (key e))).2.2 ∧
    (subR P R Adj k ℓ ν addr (key e) (gin (key e))).2.2.getLast?.getD none = e.2.2.2.2
  nodup : (subs.map key).Nodup
  ginE : ∀ q, q ∉ subs.map key → gin q = []
  fam : ∀ i, (subs.map (·.1)).count i ≤ fB P.M (k - ℓ)
  keyR : ∀ e ∈ subs, 1 ≤ e.1 ∧ e.1 < t
  stat : ∀ e ∈ subs, ∃ p ∈ rnd e.1, p.1 = e.2.1 ∧ p.2 = e.2.2.1
  ginS : ∀ q, ((gin q).map Prod.fst).Sublist (pre.map Prod.fst)
  ginI : ∀ q, ∀ p ∈ gin q, ∃ p' ∈ pre, p'.1 = p.1 ∧ p.2 ⊆ p'.2
  ginOK : ∀ e ∈ subs, ∀ p ∈ gin (key e), p.2 ⊆ e.2.2.1 ∧ (e.2.2.1.card : ℝ) ≤ 2 * ν * p.2.card
  Qok : ∀ q ∈ Q, q.2 ⊆ (pre.map Prod.fst).toFinset ∧ q.2.card ≤ fB P.M (k - ℓ)
  sep : ∀ e ∈ subs, e.2.2.2.2 = none → ∀ j, e.1 < j → ∀ p ∈ rnd j,
    2 * ν * ((e.2.2.1 ∩ p.2).card : ℝ) < e.2.2.1.card
  alive : (∀ o ∈ (mainR P R Adj k ℓ ν addr pre).2.2, o = none) →
    ∀ i, 1 ≤ i → i < t → ∃ e ∈ subs, e.1 = i ∧ e.2.2.2.2 = none
  bound : (t : ℝ) - 1 < 2 * ν
  count : ∑ j ∈ Finset.Icc 1 t, (rnd j).length + ∑ q ∈ (subs.map key).toFinset, (gin q).length ≤
    pre.length
  cols : ∀ c ∈ (mainR P R Adj k ℓ ν addr pre).2.1,
    (∃ j ∈ Finset.Icc 1 t, c ∈ (locR P R Adj k ℓ addr j (rnd j)).2.1) ∨
    (∃ q ∈ subs.map key, c ∈ (subR P R Adj k ℓ ν addr q (gin q)).2.1)
  last : ∀ o, (mainR P R Adj k ℓ ν addr pre).2.2.getLast? = some (some o) →
    ∃ i, (∃ e ∈ subs, e.1 = i) ∧
      (subs.filter (fun f => f.1 = i)).all (fun f => f.2.2.2.2.isSome) ∧ o = famOut Q subs i

/-- Paper's Lemma 6.14: the number of rounds. -/
theorem round_bound (U : Finset (Finset ℕ)) (pre : Inp)
    (hU : ∀ p ∈ pre, p.2 ⊆ U ∧ p.2.Nonempty ∧ (U.card : ℝ) ≤ ν * p.2.card) (hν : 1 ≤ ν)
    (t : ℕ) (subs : List Sub) (rnd : ℕ → Inp) (rndS : ∀ j, (rnd j).Sublist pre)
    (stat : ∀ e ∈ subs, ∃ p ∈ rnd e.1, p.1 = e.2.1 ∧ p.2 = e.2.2.1)
    (sep : ∀ e ∈ subs, e.2.2.2.2 = none → ∀ j, e.1 < j → ∀ p ∈ rnd j,
      2 * ν * ((e.2.2.1 ∩ p.2).card : ℝ) < e.2.2.1.card)
    (alive : ∀ i, 1 ≤ i → i < t → ∃ e ∈ subs, e.1 = i ∧ e.2.2.2.2 = none) :
    (t : ℝ) - 1 < 2 * ν := by
  rcases Nat.lt_or_ge t 2 with ht | ht
  · have : (t : ℝ) ≤ 1 := by exact_mod_cast (by omega : t ≤ 1)
    linarith
  choose! d hd using alive
  set A : List (Finset (Finset ℕ)) := (List.range (t - 1)).map (fun i => (d (i + 1)).2.2.1) with hA
  have hAlen : A.length = t - 1 := by simp [A]
  have hAget : ∀ i (hi : i < A.length), A.get ⟨i, hi⟩ = (d (i + 1)).2.2.1 := by
    intro i hi; simp [A]
  have hdi : ∀ i, i < t - 1 → d (i + 1) ∈ subs ∧ (d (i + 1)).1 = i + 1 ∧ (d (i + 1)).2.2.2.2 = none :=
    fun i hi => hd (i + 1) (by omega) (by omega)
  have hmem : ∀ a ∈ A, ∃ p ∈ pre, p.2 = a := by
    intro a ha
    simp only [A, List.mem_map, List.mem_range] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    obtain ⟨h1, -, -⟩ := hdi i hi
    obtain ⟨p, hp, -, hp2⟩ := stat _ h1
    exact ⟨p, (rndS _).subset hp, hp2⟩
  have hk := kyy_lemma ν hν U A
    (fun a ha => by obtain ⟨p, hp, rfl⟩ := hmem a ha; exact (hU p hp).1)
    (fun a ha => by obtain ⟨p, hp, rfl⟩ := hmem a ha; exact (hU p hp).2.2)
    (by
      obtain ⟨p, hp, hpa⟩ := hmem ((d 1).2.2.1) (by simp [A]; exact ⟨0, by omega, rfl⟩)
      exact (hU p hp).2.1.mono (hU p hp).1)
    (by
      intro i j hi hj hij
      rw [hAget, hAget]
      rw [hAlen] at hi hj
      obtain ⟨hi1, hi2, hi3⟩ := hdi i hi
      obtain ⟨hj1, hj2, -⟩ := hdi j hj
      obtain ⟨p, hp, -, hp2⟩ := stat _ hj1
      rw [hj2] at hp
      have := sep _ hi1 hi3 (j + 1) (by omega) p hp
      rwa [hp2] at this)
  rw [hAlen] at hk
  have : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  linarith

end OnlineColoringKYY.Supplement.Dev.T626.PartCS
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartCS
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
/-! ## The three kinds of steps -/
theorem fst_toFinset_mono (pre : Inp) (x : ℕ × Finset (Finset ℕ)) :
    (pre.map Prod.fst).toFinset ⊆ ((pre ++ [x]).map Prod.fst).toFinset := by
  intro y; simp only [List.mem_toFinset, List.map_append, List.mem_append]; tauto

theorem cand_empty {ν : ℝ} (hν : 0 < ν) {subs : List Sub} {Cv : Finset (Finset ℕ)}
    (hc : ¬ (candOf ν subs Cv).Nonempty) :
    ∀ e ∈ subs, e.2.2.2.2 = none → 2 * ν * ((e.2.2.1 ∩ Cv).card : ℝ) < e.2.2.1.card := by
  intro e he hn
  by_contra hcon
  push Not at hcon
  apply hc
  refine ⟨(e.1, e.2.1), ?_⟩
  unfold candOf
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
  refine ⟨e, ⟨he, hn, ?_⟩, rfl⟩
  rw [ge_iff_le, div_le_iff₀ (by positivity)]; linarith

theorem sum_update_len (rnd : ℕ → Inp) (t : ℕ) (ht : 1 ≤ t) (x : ℕ × Finset (Finset ℕ)) :
    ∑ j ∈ Finset.Icc 1 t, (Function.update rnd t (rnd t ++ [x]) j).length =
      ∑ j ∈ Finset.Icc 1 t, (rnd j).length + 1 := by
  have hm : t ∈ Finset.Icc 1 t := Finset.mem_Icc.2 ⟨ht, le_rfl⟩
  rw [← Finset.add_sum_erase _ _ hm, ← Finset.add_sum_erase _ _ hm, Function.update_self]
  have : ∑ j ∈ (Finset.Icc 1 t).erase t, (Function.update rnd t (rnd t ++ [x]) j).length =
      ∑ j ∈ (Finset.Icc 1 t).erase t, (rnd j).length :=
    Finset.sum_congr rfl (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
  rw [this, List.length_append, List.length_singleton]
  omega

end OnlineColoringKYY.Supplement.Dev.T626.PartCS
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartCS
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
variable (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (k ℓ : ℕ) (ν : ℝ) (addr : List ℕ)
theorem inv_sub (hR : R.Valid) (hℓ : 0 < ℓ ∧ ℓ ≤ k) (hν : 0 < ν) (pre : Inp)
    (x : ℕ × Finset (Finset ℕ)) (t : ℕ) (Q : List (ℕ × Finset ℕ)) (subs : List Sub)
    (rnd : ℕ → Inp) (gin : ℕ × ℕ → Inp) (I : Inv P R Adj k ℓ ν addr pre t Q subs rnd gin)
    (hnone : ∀ o ∈ (mainR P R Adj k ℓ ν addr pre).2.2, o = none)
    (hc : (candOf ν subs x.2).Nonempty) :
    ∃ t' Q' subs' rnd' gin', Inv P R Adj k ℓ ν addr (pre ++ [x]) t' Q' subs' rnd' gin' := by
  have hkk := hR.2.2.2 addr x.1 _ hc
  obtain ⟨e0, he0, ⟨he0n, he0c⟩, hkey⟩ : ∃ e0 ∈ subs, (e0.2.2.2.2 = none ∧
      ((e0.2.2.1 ∩ x.2).card : ℝ) ≥ (e0.2.2.1.card : ℝ) / (2 * ν)) ∧
      (e0.1, e0.2.1) = R.inst addr x.1 (candOf ν subs x.2) := by
    have h := hkk
    unfold candOf at h
    simp only [List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq] at h
    obtain ⟨e, ⟨he, hc⟩, hk⟩ := h
    exact ⟨e, he, hc, hk⟩
  set kk := R.inst addr x.1 (candOf ν subs x.2) with hkkdef
  set idx := subs.findIdx (fun e => decide ((e.1, e.2.1) = kk)) with hidx
  have hidxlt : idx < subs.length := List.findIdx_lt_length_of_exists ⟨e0, he0, by simp [hkey]⟩
  have hsi : subs[idx] = e0 := by
    have h1 : decide ((subs[idx].1, subs[idx].2.1) = kk) = true := List.findIdx_getElem (w := hidxlt)
    simp only [decide_eq_true_eq] at h1
    exact List.inj_on_of_nodup_map I.nodup (List.getElem_mem _) he0
      (by simp only [key]; rw [h1, hkey])
  have hget : e0 = subs.getD idx (0, 0, ∅, Inst.fresh, none) := by
    rw [List.getD_eq_getElem _ _ hidxlt, hsi]
  have hstep := step_sub P R (AdjAt Adj x.1) x.1 addr x.2 k ℓ ν _ t _ Q subs pre I.st hℓ hc idx
    hidx e0 hget
  have hmain := mainR_snoc P R Adj k ℓ ν addr pre x
  rw [hstep] at hmain
  simp only [Prod.mk.eta] at hmain
  obtain ⟨hst0, hlive0, hlast0⟩ := I.ent e0 he0
  set q0 := key e0 with hq0
  set newp : ℕ × Finset (Finset ℕ) := (x.1, e0.2.2.1 ∩ x.2) with hnewp
  set res := locStep P R (AdjAt Adj x.1) x.1 (.cb k (ℓ - 1) (2 * ν)) (addr ++ [5, e0.1, e0.2.1])
    (e0.2.2.1 ∩ x.2) e0.2.2.2.1 with hres
  have hsubR : subR P R Adj k ℓ ν addr q0 (gin q0 ++ [newp]) =
      (res.1, (subR P R Adj k ℓ ν addr q0 (gin q0)).2.1 ++ [res.2.1],
        (subR P R Adj k ℓ ν addr q0 (gin q0)).2.2 ++ [res.2.2]) := by
    rw [subR_snoc, ← hst0]
    rfl
  set a : Sub := (e0.1, e0.2.1, e0.2.2.1, res.1, res.2.2) with ha
  set subs' := subs.set idx a with hsubs'
  have hmapK : subs'.map key = subs.map key :=
    map_set_self key subs idx hidxlt a (by rw [hsi]; rfl)
  have hmap1 : subs'.map (·.1) = subs.map (·.1) :=
    map_set_self _ subs idx hidxlt a (by rw [hsi])
  have haMem : a ∈ subs' := mem_set_self hidxlt a
  have hcases : ∀ f ∈ subs', f = a ∨ f ∈ subs := fun f hf => mem_set_cases hf
  have hnodup' : (subs'.map key).Nodup := hmapK ▸ I.nodup
  have hkeyEq : ∀ f ∈ subs', key f = q0 → f = a :=
    fun f hf h => List.inj_on_of_nodup_map hnodup' hf haMem h
  have hold : ∀ f ∈ subs, key f ≠ q0 → f ∈ subs' :=
    fun f hf h => mem_set_of_ne hidxlt hf (by rw [hsi]; rintro rfl; exact h rfl)
  have hq0mem : q0 ∈ subs.map key := List.mem_map_of_mem he0
  set gin' := Function.update gin q0 (gin q0 ++ [newp]) with hgin'
  have hgin_ne : ∀ q, q ≠ q0 → gin' q = gin q := fun q h => Function.update_of_ne h _ _
  have hgin_eq : gin' q0 = gin q0 ++ [newp] := Function.update_self _ _ _
  have hnone0 : ∀ o ∈ (subR P R Adj k ℓ ν addr q0 (gin q0)).2.2, o = none :=
    none_of_live hlive0 (hlast0.trans he0n)
  have hka : key a = q0 := rfl
  refine ⟨t, Q, subs', rnd, gin', ?_⟩
  exact {
    st := by rw [hmain]; rfl
    t1 := I.t1
    rndE := I.rndE
    rndS := fun j => (I.rndS j).trans (List.sublist_append_left _ _)
    fin := I.fin
    curN := I.curN
    ent := by
      intro f hf
      by_cases hk : key f = q0
      · obtain rfl := hkeyEq f hf hk
        rw [hka, hgin_eq, hsubR]
        refine ⟨rfl, live_snoc hnone0 _, by simp [a]⟩
      · rcases hcases f hf with rfl | hf'
        · exact absurd hka hk
        · rw [hgin_ne _ hk]; exact I.ent f hf'
    nodup := hnodup'
    ginE := by
      intro q hq
      rw [hmapK] at hq
      have : q ≠ q0 := fun h => hq (h ▸ hq0mem)
      rw [hgin_ne q this]; exact I.ginE q hq
    fam := by intro i; rw [hmap1]; exact I.fam i
    keyR := by
      intro f hf
      rcases hcases f hf with rfl | hf'
      · exact I.keyR e0 he0
      · exact I.keyR f hf'
    stat := by
      intro f hf
      rcases hcases f hf with rfl | hf'
      · exact I.stat e0 he0
      · exact I.stat f hf'
    ginS := by
      intro q
      by_cases hq : q = q0
      · subst hq; rw [hgin_eq]
        simp only [List.map_append, List.map_cons, List.map_nil]
        exact (I.ginS _).append (List.Sublist.refl _)
      · rw [hgin_ne q hq]; exact (I.ginS q).trans (by simp)
    ginI := by
      intro q p hp
      by_cases hq : q = q0
      · subst hq; rw [hgin_eq] at hp
        rcases List.mem_append.1 hp with hp | hp
        · obtain ⟨p', h1, h2, h3⟩ := I.ginI _ p hp
          exact ⟨p', List.mem_append_left _ h1, h2, h3⟩
        · rw [List.mem_singleton] at hp; subst hp
          exact ⟨x, List.mem_append_right _ (List.mem_singleton_self _), rfl,
            Finset.inter_subset_right⟩
      · rw [hgin_ne q hq] at hp
        obtain ⟨p', h1, h2, h3⟩ := I.ginI q p hp
        exact ⟨p', List.mem_append_left _ h1, h2, h3⟩
    ginOK := by
      intro f hf p hp
      by_cases hk : key f = q0
      · obtain rfl := hkeyEq f hf hk
        rw [hka, hgin_eq] at hp
        rcases List.mem_append.1 hp with hp | hp
        · exact I.ginOK e0 he0 p hp
        · rw [List.mem_singleton] at hp; subst hp
          refine ⟨Finset.inter_subset_left, ?_⟩
          rw [ge_iff_le, div_le_iff₀ (by positivity)] at he0c
          change (e0.2.2.1.card : ℝ) ≤ 2 * ν * ((e0.2.2.1 ∩ x.2).card : ℝ)
          linarith
      · rcases hcases f hf with rfl | hf'
        · exact absurd hka hk
        · rw [hgin_ne _ hk] at hp; exact I.ginOK f hf' p hp
    Qok := fun q hq => ⟨(I.Qok q hq).1.trans (fst_toFinset_mono pre x), (I.Qok q hq).2⟩
    sep := by
      intro f hf hfn j hj p hp
      rcases hcases f hf with rfl | hf'
      · exact I.sep e0 he0 he0n j hj p hp
      · exact I.sep f hf' hfn j hj p hp
    alive := by
      intro hnew i hi1 hit
      rw [hmain] at hnew
      have hout := hnew _ (List.mem_append_right _ (List.mem_singleton_self _))
      by_cases hie : i = e0.1
      · subst hie
        by_contra hcon
        push Not at hcon
        have hall : (subs'.filter (fun f => f.1 = e0.1)).all (fun f => f.2.2.2.2.isSome) = true := by
          rw [List.all_eq_true]
          intro f hf
          rw [List.mem_filter, decide_eq_true_eq] at hf
          rw [Option.isSome_iff_ne_none]
          exact hcon f hf.1 hf.2
        rw [if_pos hall] at hout
        exact absurd hout (by simp)
      · obtain ⟨f, hf, hf1, hfn⟩ := I.alive hnone i hi1 hit
        refine ⟨f, hold f hf ?_, hf1, hfn⟩
        intro h
        apply hie
        rw [← hf1]
        have := congrArg Prod.fst h
        simpa [key, hq0] using this
    bound := I.bound
    count := by
      have h := I.count
      have hm : q0 ∈ (subs.map key).toFinset := List.mem_toFinset.2 hq0mem
      rw [← Finset.add_sum_erase _ _ hm] at h
      rw [hmapK, ← Finset.add_sum_erase _ _ hm]
      have : ∑ q ∈ (subs.map key).toFinset.erase q0, (gin' q).length =
          ∑ q ∈ (subs.map key).toFinset.erase q0, (gin q).length :=
        Finset.sum_congr rfl (fun q hq => by rw [hgin_ne q (Finset.ne_of_mem_erase hq)])
      rw [this, hgin_eq, List.length_append, List.length_append]
      simp only [List.length_singleton]
      omega
    cols := by
      intro c hc
      rw [hmain] at hc
      simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · rcases I.cols c hc with h | ⟨q, hq, hcq⟩
        · exact Or.inl h
        · refine Or.inr ⟨q, hmapK ▸ hq, ?_⟩
          by_cases hqq : q = q0
          · subst hqq; rw [hgin_eq, hsubR]; exact List.mem_append_left _ hcq
          · rw [hgin_ne q hqq]; exact hcq
      · refine Or.inr ⟨q0, hmapK ▸ hq0mem, ?_⟩
        rw [hgin_eq, hsubR]; simp
    last := by
      intro o ho
      rw [hmain] at ho
      simp only [List.getLast?_concat, Option.some.injEq] at ho
      by_cases hall : (subs'.filter (fun f => f.1 = e0.1)).all (fun f => f.2.2.2.2.isSome) = true
      · rw [if_pos hall] at ho
        exact ⟨e0.1, ⟨a, haMem, rfl⟩, hall, (Option.some.inj ho).symm⟩
      · rw [if_neg hall] at ho
        exact absurd ho (by simp) }

theorem inv_locN (hℓ : 0 < ℓ ∧ ℓ ≤ k) (hν : 0 < ν) (pre : Inp)
    (x : ℕ × Finset (Finset ℕ)) (t : ℕ) (Q : List (ℕ × Finset ℕ)) (subs : List Sub)
    (rnd : ℕ → Inp) (gin : ℕ × ℕ → Inp) (I : Inv P R Adj k ℓ ν addr pre t Q subs rnd gin)
    (hnone : ∀ o ∈ (mainR P R Adj k ℓ ν addr pre).2.2, o = none)
    (hc : ¬ (candOf ν subs x.2).Nonempty)
    (hr : (locStep P R (AdjAt Adj x.1) x.1 (.loc (k - ℓ)) (addr ++ [6, t, 0]) ∅
      (locR P R Adj k ℓ addr t (rnd t)).1).2.2 = none) :
    ∃ t' Q' subs' rnd' gin', Inv P R Adj k ℓ ν addr (pre ++ [x]) t' Q' subs' rnd' gin' := by
  have hstep := step_locN P R (AdjAt Adj x.1) x.1 addr x.2 k ℓ ν _ t _ Q subs pre I.st hℓ hc hr
  have hmain := mainR_snoc P R Adj k ℓ ν addr pre x
  rw [hstep] at hmain
  simp only [Prod.mk.eta] at hmain
  have hlocR := locR_snoc P R Adj k ℓ addr t (rnd t) x
  set res := locStep P R (AdjAt Adj x.1) x.1 (.loc (k - ℓ)) (addr ++ [6, t, 0]) ∅
    (locR P R Adj k ℓ addr t (rnd t)).1 with hres
  set rnd' := Function.update rnd t (rnd t ++ [x]) with hrnd'
  have hrnd_ne : ∀ j, j ≠ t → rnd' j = rnd j := fun j h => Function.update_of_ne h _ _
  have hrnd_eq : rnd' t = rnd t ++ [x] := Function.update_self _ _ _
  have hsubset : ∀ j, ∀ p ∈ rnd j, p ∈ rnd' j := by
    intro j p hp
    by_cases hj : j = t
    · subst hj; rw [hrnd_eq]; exact List.mem_append_left _ hp
    · rw [hrnd_ne j hj]; exact hp
  have hcolsub : ∀ j, ∀ c ∈ (locR P R Adj k ℓ addr j (rnd j)).2.1,
      c ∈ (locR P R Adj k ℓ addr j (rnd' j)).2.1 := by
    intro j c hc
    by_cases hj : j = t
    · subst hj; rw [hrnd_eq, hlocR]; exact List.mem_append_left _ hc
    · rw [hrnd_ne j hj]; exact hc
  have hce := cand_empty hν hc
  refine ⟨t, Q, subs, rnd', gin, ?_⟩
  exact {
    st := by rw [hmain, hrnd_eq, hlocR]; rfl
    t1 := I.t1
    rndE := fun j hj => by rw [hrnd_ne j (by omega)]; exact I.rndE j hj
    rndS := by
      intro j
      by_cases hj : j = t
      · subst hj; rw [hrnd_eq]; exact (I.rndS _).append (List.Sublist.refl _)
      · rw [hrnd_ne j hj]; exact (I.rndS j).trans (List.sublist_append_left _ _)
    fin := fun j h1 h2 => by rw [hrnd_ne j (by omega)]; exact I.fin j h1 h2
    curN := by
      rw [hrnd_eq, hlocR]
      intro o ho
      rcases List.mem_append.1 ho with ho | ho
      · exact I.curN o ho
      · rw [List.mem_singleton] at ho; rw [ho]; exact hr
    ent := I.ent
    nodup := I.nodup
    ginE := I.ginE
    fam := I.fam
    keyR := I.keyR
    stat := by
      intro e he
      obtain ⟨p, hp, h⟩ := I.stat e he
      exact ⟨p, hsubset _ p hp, h⟩
    ginS := fun q => (I.ginS q).trans (by simp)
    ginI := by
      intro q p hp
      obtain ⟨p', h1, h2, h3⟩ := I.ginI q p hp
      exact ⟨p', List.mem_append_left _ h1, h2, h3⟩
    ginOK := I.ginOK
    Qok := fun q hq => ⟨(I.Qok q hq).1.trans (fst_toFinset_mono pre x), (I.Qok q hq).2⟩
    sep := by
      intro e he hn j hj p hp
      by_cases hjt : j = t
      · subst hjt
        rw [hrnd_eq] at hp
        rcases List.mem_append.1 hp with hp | hp
        · exact I.sep e he hn _ hj p hp
        · rw [List.mem_singleton] at hp; subst hp; exact hce e he hn
      · rw [hrnd_ne j hjt] at hp; exact I.sep e he hn j hj p hp
    alive := fun _ => I.alive hnone
    bound := I.bound
    count := by
      have h := I.count
      rw [sum_update_len rnd t I.t1 x, List.length_append, List.length_singleton]
      omega
    cols := by
      intro c hc
      rw [hmain] at hc
      simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · rcases I.cols c hc with ⟨j, hj, hcj⟩ | h
        · exact Or.inl ⟨j, hj, hcolsub j c hcj⟩
        · exact Or.inr h
      · refine Or.inl ⟨t, Finset.mem_Icc.2 ⟨I.t1, le_rfl⟩, ?_⟩
        rw [hrnd_eq, hlocR]; simp
    last := by
      intro o ho
      rw [hmain] at ho
      simp at ho }

theorem inv_locS (hℓ : 0 < ℓ ∧ ℓ ≤ k) (hν1 : 1 ≤ ν) (N : ℕ) (W F : ℝ) (hkM : k ≤ P.M ^ 2)
    (IHL : Holds P R Adj N W F (.loc (k - ℓ))) (U : Finset (Finset ℕ)) (pre : Inp)
    (x : ℕ × Finset (Finset ℕ))
    (hsort : ((pre ++ [x]).map Prod.fst).Pairwise (· < ·)) (hN : (pre ++ [x]).length ≤ N)
    (hU : ∀ p ∈ pre ++ [x], p.2 ⊆ U ∧ p.2.Nonempty ∧ (U.card : ℝ) ≤ ν * p.2.card)
    (t : ℕ) (Q : List (ℕ × Finset ℕ)) (subs : List Sub)
    (rnd : ℕ → Inp) (gin : ℕ × ℕ → Inp) (I : Inv P R Adj k ℓ ν addr pre t Q subs rnd gin)
    (hnone : ∀ o ∈ (mainR P R Adj k ℓ ν addr pre).2.2, o = none)
    (hc : ¬ (candOf ν subs x.2).Nonempty) (o : Out)
    (hr : (locStep P R (AdjAt Adj x.1) x.1 (.loc (k - ℓ)) (addr ++ [6, t, 0]) ∅
      (locR P R Adj k ℓ addr t (rnd t)).1).2.2 = some o) :
    ∃ t' Q' subs' rnd' gin', Inv P R Adj k ℓ ν addr (pre ++ [x]) t' Q' subs' rnd' gin' := by
  have hν : 0 < ν := by linarith
  have hstep := step_locS P R (AdjAt Adj x.1) x.1 addr x.2 k ℓ ν _ t _ Q subs pre I.st hℓ hc o hr
  have hmain := mainR_snoc P R Adj k ℓ ν addr pre x
  rw [hstep] at hmain
  simp only [Prod.mk.eta] at hmain
  have hlocR := locR_snoc P R Adj k ℓ addr t (rnd t) x
  set res := locStep P R (AdjAt Adj x.1) x.1 (.loc (k - ℓ)) (addr ++ [6, t, 0]) ∅
    (locR P R Adj k ℓ addr t (rnd t)).1 with hres
  set rnd' := Function.update rnd t (rnd t ++ [x]) with hrnd'
  have hrnd_ne : ∀ j, j ≠ t → rnd' j = rnd j := fun j h => Function.update_of_ne h _ _
  have hrnd_eq : rnd' t = rnd t ++ [x] := Function.update_self _ _ _
  have hsubset : ∀ j, ∀ p ∈ rnd j, p ∈ rnd' j := by
    intro j p hp
    by_cases hj : j = t
    · subst hj; rw [hrnd_eq]; exact List.mem_append_left _ hp
    · rw [hrnd_ne j hj]; exact hp
  have hcolsub : ∀ j, ∀ c ∈ (locR P R Adj k ℓ addr j (rnd j)).2.1,
      c ∈ (locR P R Adj k ℓ addr j (rnd' j)).2.1 := by
    intro j c hc
    by_cases hj : j = t
    · subst hj; rw [hrnd_eq, hlocR]; exact List.mem_append_left _ hc
    · rw [hrnd_ne j hj]; exact hc
  have hce := cand_empty hν hc
  have hrS : (rnd t ++ [x]).Sublist (pre ++ [x]) := (I.rndS t).append (List.Sublist.refl _)
  -- the certificate
  have hliveL : Live (locR P R Adj k ℓ addr t (rnd t ++ [x])).2.2 := by
    rw [hlocR]; exact live_snoc I.curN _
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hout⟩ := IHL (addr ++ [6, t, 0]) (strip (rnd t ++ [x]))
    ⟨by rw [strip_fst]; exact hsort.sublist (hrS.map Prod.fst), by rw [strip_length]; exact hrS.length_le.trans hN,
      by omega⟩ hliveL
  obtain ⟨hX1, hX2, hX3⟩ := hout o (by
    show (locR P R Adj k ℓ addr t (rnd t ++ [x])).2.2.getLast? = _
    rw [hlocR]; simp [hr])
  rw [strip_fst] at hX2
  set X := o.2 with hX
  have hnd : ((pre ++ [x]).map Prod.fst).Nodup := hsort.imp (fun h => ne_of_lt h)
  set batch : List Sub := X.toList.map (fun y => (t, y, lookupC (pre ++ [x]) y, Inst.fresh, none))
    with hbatch
  have hbmem : ∀ e ∈ batch, ∃ y ∈ X, e = (t, y, lookupC (pre ++ [x]) y, Inst.fresh, none) := by
    intro e he
    simp only [batch, List.mem_map, Finset.mem_toList] at he
    obtain ⟨y, hy, rfl⟩ := he
    exact ⟨y, hy, rfl⟩
  have hold_lt : ∀ e ∈ subs, e.1 < t := fun e he => (I.keyR e he).2
  have hginb : ∀ y, gin (t, y) = [] := by
    intro y
    apply I.ginE
    intro hm
    obtain ⟨e, he, hk⟩ := List.mem_map.1 hm
    have := hold_lt e he
    simp only [key, Prod.mk.injEq] at hk
    omega
  have hsubs' : ∀ e ∈ subs ++ batch, e ∈ subs ∨ ∃ y ∈ X,
      e = (t, y, lookupC (pre ++ [x]) y, Inst.fresh, none) := by
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact Or.inl he
    · exact Or.inr (hbmem e he)
  have rndS' : ∀ j, (rnd' j).Sublist (pre ++ [x]) := by
    intro j
    by_cases hj : j = t
    · subst hj; rw [hrnd_eq]; exact hrS
    · rw [hrnd_ne j hj]; exact (I.rndS j).trans (List.sublist_append_left _ _)
  have stat' : ∀ e ∈ subs ++ batch, ∃ p ∈ rnd' e.1, p.1 = e.2.1 ∧ p.2 = e.2.2.1 := by
    intro e he
    rcases hsubs' e he with he | ⟨y, hy, rfl⟩
    · obtain ⟨p, hp, h⟩ := I.stat e he
      exact ⟨p, hsubset _ p hp, h⟩
    · have hy' := hX2 hy
      rw [List.mem_toFinset, List.mem_map] at hy'
      obtain ⟨p, hp, hp1⟩ := hy'
      refine ⟨p, by rw [hrnd_eq]; exact hp, hp1, ?_⟩
      show p.2 = lookupC (pre ++ [x]) y
      rw [← hp1, lookupC_eq _ hnd p (hrS.subset hp)]
  have sep' : ∀ e ∈ subs ++ batch, e.2.2.2.2 = none → ∀ j, e.1 < j → ∀ p ∈ rnd' j,
      2 * ν * ((e.2.2.1 ∩ p.2).card : ℝ) < e.2.2.1.card := by
    intro e he hn j hj p hp
    rcases hsubs' e he with he' | ⟨y, hy, rfl⟩
    · by_cases hjt : j = t
      · subst hjt
        rw [hrnd_eq] at hp
        rcases List.mem_append.1 hp with hp | hp
        · exact I.sep e he' hn _ hj p hp
        · rw [List.mem_singleton] at hp; subst hp; exact hce e he' hn
      · rw [hrnd_ne j hjt] at hp; exact I.sep e he' hn j hj p hp
    · simp only at hj
      rw [hrnd_ne j (by omega), I.rndE j hj] at hp
      simp at hp
  have alive' : ∀ i, 1 ≤ i → i < t + 1 → ∃ e ∈ subs ++ batch, e.1 = i ∧ e.2.2.2.2 = none := by
    intro i hi1 hit
    rcases Nat.lt_or_ge i t with hit' | hit'
    · obtain ⟨e, he, h1, h2⟩ := I.alive hnone i hi1 hit'
      exact ⟨e, List.mem_append_left _ he, h1, h2⟩
    · obtain ⟨y, hy⟩ := hX1
      refine ⟨(t, y, lookupC (pre ++ [x]) y, Inst.fresh, none), List.mem_append_right _ ?_,
        by simp only; omega, rfl⟩
      simp only [batch, List.mem_map, Finset.mem_toList]
      exact ⟨y, hy, rfl⟩
  have hbK : batch.map key = X.toList.map (fun y => (t, y)) := by
    simp only [batch, List.map_map]; rfl
  have hb1 : batch.map (·.1) = List.replicate X.card t := by
    simp only [batch, List.map_map]
    rw [← Finset.length_toList X, ← List.map_const']
    rfl
  refine ⟨t + 1, Q ++ [(t, X)], subs ++ batch, rnd', gin, ?_⟩
  exact {
    st := by
      rw [hmain, hrnd_ne (t + 1) (by omega), I.rndE (t + 1) (by omega)]
      rfl
    t1 := by omega
    rndE := fun j hj => by rw [hrnd_ne j (by omega)]; exact I.rndE j (by omega)
    rndS := rndS'
    fin := by
      intro j h1 h2
      by_cases hj : j = t
      · subst hj; rw [hrnd_eq]; exact hliveL
      · rw [hrnd_ne j hj]; exact I.fin j h1 (by omega)
    curN := by
      rw [hrnd_ne (t + 1) (by omega), I.rndE (t + 1) (by omega)]
      intro o ho
      simp [locR] at ho
    ent := by
      intro e he
      rcases hsubs' e he with he | ⟨y, hy, rfl⟩
      · exact I.ent e he
      · simp only [key]
        rw [hginb]
        exact ⟨rfl, live_of_none (by simp [subR]), rfl⟩
    nodup := by
      rw [List.map_append, List.nodup_append, hbK]
      refine ⟨I.nodup, (Finset.nodup_toList X).map (fun a b h => by simpa using h), ?_⟩
      intro a ha b hb hab
      subst hab
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
      obtain ⟨y, -, hy⟩ := List.mem_map.1 hb
      have := hold_lt e he
      simp only [key, Prod.mk.injEq] at hy
      omega
    ginE := by
      intro q hq
      apply I.ginE
      intro h; apply hq
      rw [List.map_append]; exact List.mem_append_left _ h
    fam := by
      intro i
      rw [List.map_append, List.count_append, hb1, List.count_replicate]
      by_cases hi : t = i
      · subst hi
        have : (subs.map (·.1)).count t = 0 := by
          rw [List.count_eq_zero]
          intro hm
          obtain ⟨e, he, h⟩ := List.mem_map.1 hm
          have := hold_lt e he
          omega
        simp only [this, beq_self_eq_true, if_true, zero_add]
        exact hX3
      · have := I.fam i
        simp only [beq_iff_eq, hi, if_false, add_zero]
        exact this
    keyR := by
      intro e he
      rcases hsubs' e he with he | ⟨y, hy, rfl⟩
      · have := I.keyR e he; omega
      · simp only; have := I.t1; omega
    stat := stat'
    ginS := fun q => (I.ginS q).trans (by simp)
    ginI := by
      intro q p hp
      obtain ⟨p', h1, h2, h3⟩ := I.ginI q p hp
      exact ⟨p', List.mem_append_left _ h1, h2, h3⟩
    ginOK := by
      intro e he p hp
      rcases hsubs' e he with he | ⟨y, hy, rfl⟩
      · exact I.ginOK e he p hp
      · simp only [key] at hp; rw [hginb] at hp; simp at hp
    Qok := by
      intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · exact ⟨(I.Qok q hq).1.trans (fst_toFinset_mono pre x), (I.Qok q hq).2⟩
      · rw [List.mem_singleton] at hq; subst hq
        refine ⟨hX2.trans ?_, hX3⟩
        intro y hy
        rw [List.mem_toFinset] at hy ⊢
        exact (hrS.map Prod.fst).subset hy
    sep := sep'
    alive := fun _ => alive'
    bound := round_bound ν U (pre ++ [x]) hU hν1 (t + 1) (subs ++ batch) rnd' rndS' stat' sep' alive'
    count := by
      have h := I.count
      have hsub : (subs.map key).toFinset ⊆ ((subs ++ batch).map key).toFinset := by
        intro q hq; rw [List.mem_toFinset] at hq ⊢; rw [List.map_append]
        exact List.mem_append_left _ hq
      rw [← Finset.sum_subset hsub (fun q _ hq => by
        rw [I.ginE q (by simpa using hq)]; rfl)]
      rw [Finset.sum_Icc_succ_top (by omega), hrnd_ne (t + 1) (by omega), I.rndE (t + 1) (by omega),
        sum_update_len rnd t I.t1 x, List.length_append, List.length_singleton]
      simp only [List.length_nil, add_zero]
      omega
    cols := by
      intro c hc
      rw [hmain] at hc
      simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · rcases I.cols c hc with ⟨j, hj, hcj⟩ | ⟨q, hq, hcq⟩
        · refine Or.inl ⟨j, ?_, hcolsub j c hcj⟩
          rw [Finset.mem_Icc] at hj ⊢; omega
        · refine Or.inr ⟨q, ?_, hcq⟩
          rw [List.map_append]; exact List.mem_append_left _ hq
      · refine Or.inl ⟨t, Finset.mem_Icc.2 ⟨I.t1, by omega⟩, ?_⟩
        rw [hrnd_eq, hlocR]; simp
    last := by
      intro o ho
      rw [hmain] at ho
      simp at ho }

/-! ## The whole run -/
theorem inv_init (hℓM : P.M < ℓ) (hν : 0 < ν) :
    Inv P R Adj k ℓ ν addr [] 1 [] [] (fun _ => []) (fun _ => []) where
  st := by
    simp [mainR, Inst.normalize, Inst.initOf, Nat.not_le.2 hℓM, locR, instRun]
  t1 := le_rfl
  rndE := fun _ _ => rfl
  rndS := fun _ => List.Sublist.slnil
  fin := fun j h1 h2 => by omega
  curN := by simp [locR]
  ent := by simp
  nodup := by simp
  ginE := fun _ _ => rfl
  fam := by simp
  keyR := by simp
  stat := by simp
  ginS := by simp
  ginI := by simp
  ginOK := by simp
  Qok := by simp
  sep := by simp
  alive := fun _ i h1 h2 => by omega
  bound := by simp; linarith
  count := by simp
  cols := by simp [mainR]
  last := by simp [mainR]

theorem inv_run (hR : R.Valid) (hℓM : P.M < ℓ) (hℓ : 0 < ℓ ∧ ℓ ≤ k) (hν1 : 1 ≤ ν) (N : ℕ) (W F : ℝ)
    (hkM : k ≤ P.M ^ 2) (IHL : Holds P R Adj N W F (.loc (k - ℓ))) (U : Finset (Finset ℕ))
    (ins : Inp) (hsort : (ins.map Prod.fst).Pairwise (· < ·)) (hN : ins.length ≤ N)
    (hU : ∀ p ∈ ins, p.2 ⊆ U ∧ p.2.Nonempty ∧ (U.card : ℝ) ≤ ν * p.2.card)
    (hlive : Live (mainR P R Adj k ℓ ν addr ins).2.2) :
    ∀ n, n ≤ ins.length → ∃ t Q subs rnd gin,
      Inv P R Adj k ℓ ν addr (ins.take n) t Q subs rnd gin := by
  have hν : 0 < ν := by linarith
  intro n
  induction n with
  | zero => intro _; exact ⟨1, [], [], _, _, by simpa using inv_init P R Adj k ℓ ν addr hℓM hν⟩
  | succ n ih =>
    intro hn
    obtain ⟨t, Q, subs, rnd, gin, I⟩ := ih (by omega)
    have htake : ins.take (n + 1) = ins.take n ++ [ins[n]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]; rfl
    have hnone : ∀ o ∈ (mainR P R Adj k ℓ ν addr (ins.take n)).2.2, o = none := by
      have hsplit : ins = ins.take n ++ ins.drop n := (List.take_append_drop _ _).symm
      have h := hlive
      unfold mainR at h ⊢
      rw [hsplit, instRun_append] at h
      refine (live_of_append ?_ h).1
      rw [← List.length_pos_iff, instRun_len]
      simp; omega
    have hsub : (ins.take (n + 1)).Sublist ins := List.take_sublist _ _
    rw [htake] at hsub ⊢
    have hsort' := hsort.sublist (hsub.map Prod.fst)
    have hN' := hsub.length_le.trans hN
    have hU' : ∀ p ∈ ins.take n ++ [ins[n]], p.2 ⊆ U ∧ p.2.Nonempty ∧
        (U.card : ℝ) ≤ ν * p.2.card := fun p hp => hU p (hsub.subset hp)
    by_cases hc : (candOf ν subs ins[n].2).Nonempty
    · exact inv_sub P R Adj k ℓ ν addr hR hℓ hν _ _ t Q subs rnd gin I hnone hc
    · cases hr : (locStep P R (AdjAt Adj ins[n].1) ins[n].1 (.loc (k - ℓ)) (addr ++ [6, t, 0]) ∅
          (locR P R Adj k ℓ addr t (rnd t)).1).2.2 with
      | none => exact inv_locN P R Adj k ℓ ν addr hℓ hν _ _ t Q subs rnd gin I hnone hc hr
      | some o =>
        exact inv_locS P R Adj k ℓ ν addr hℓ hν1 N W F hkM IHL U _ _ hsort' hN' hU' t Q subs rnd
          gin I hnone hc o hr

end OnlineColoringKYY.Supplement.Dev.T626.PartCS
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartCS
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
/-! ## Combining the children's summaries -/
theorem combine (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (N : ℕ) (W F : ℝ)
    {ι : Type} [DecidableEq ι] (s : Finset ι) (m : ι → Mode) (a : ι → List ℕ) (g : ι → Inp)
    (D : ℕ) (C : ℝ)
    (h : ∀ i ∈ s, Summary P R Adj N W F (m i) (a i) (g i))
    (hb : ∀ i ∈ s, ownBins P (m i) = 0) (he : ∀ i ∈ s, ownExt (m i) = 0)
    (hd : ∀ i ∈ s, depOf P.M (m i) ≤ D)
    (hc : ∀ i ∈ s, cntOf P.M W F (Real.logb 2 N) (m i) ≤ C) :
    ∃ (nb ext : ℕ) (sizes : List ℕ),
      (∑ i ∈ s, ((instRun P R Adj (m i) (a i) (g i) .fresh).2.1.toFinset.card : ℝ)) ≤
        (P.L : ℝ) / P.M * nb + ext ∧
      (nb : ℝ) ≤ ((∑ i ∈ s, (g i).length : ℕ) : ℝ) / P.L +
        (sizes.map (fun x : ℕ => 8 * ((x : ℕ) : ℝ) ^ (1 - 1 / (P.M : ℝ) ^ 10))).sum ∧
      ext ≤ sizes.length ∧ (sizes.length : ℝ) ≤ s.card * C ∧
      sizes.sum ≤ (∑ i ∈ s, (g i).length) * D ∧ (∀ x ∈ sizes, 1 ≤ x ∧ x ≤ N) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, [], by simp, by simp, le_rfl, by simp, by simp, by simp⟩
  | insert i s hi ih =>
    have hm : i ∈ insert i s := Finset.mem_insert_self _ _
    obtain ⟨nb, ext, sz, h1, h2, h3, h4, h5, h6⟩ := ih
      (fun j hj => h j (Finset.mem_insert_of_mem hj)) (fun j hj => hb j (Finset.mem_insert_of_mem hj))
      (fun j hj => he j (Finset.mem_insert_of_mem hj)) (fun j hj => hd j (Finset.mem_insert_of_mem hj))
      (fun j hj => hc j (Finset.mem_insert_of_mem hj))
    obtain ⟨nb', ext', sz', g1, g2, g3, -, g5, g6, g7, -⟩ := h i hm
    rw [hb i hm] at g2
    rw [he i hm] at g3
    have hci := hc i hm
    have hdi := hd i hm
    refine ⟨nb' + nb, ext' + ext, sz' ++ sz, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.sum_insert hi]; push_cast; linarith
    · rw [Finset.sum_insert hi]
      simp only [List.map_append, List.sum_append]
      push_cast at h2 ⊢
      rw [add_div]
      linarith
    · simp only [List.length_append]; omega
    · rw [Finset.card_insert_of_notMem hi]
      simp only [List.length_append]
      push_cast
      linarith
    · rw [Finset.sum_insert hi, List.sum_append, add_mul]
      have := g6.trans (Nat.mul_le_mul_left _ hdi)
      omega
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact g7 x hx
      · exact h6 x hx

/-! ## Family outputs -/
theorem verts_famStep_some (f : Sub) (acc o : Out) (h : f.2.2.2.2 = some o) :
    Out.verts (famStep f acc) = Out.verts acc ∪ Out.verts o := by
  unfold famStep
  rw [h]
  simp only [Out.verts, Finset.sup_union]
  ext y; simp only [Finset.mem_union, Finset.sup_eq_union]; tauto

theorem verts_famStep_none (f : Sub) (acc : Out) (h : f.2.2.2.2 = none) :
    famStep f acc = acc := by
  unfold famStep
  rw [h]

theorem verts_fold (l : List Sub) (init : Out) :
    Out.verts (l.foldr famStep init) = Out.verts init ∪
      (l.map (fun f => (f.2.2.2.2.map Out.verts).getD ∅)).foldr (· ∪ ·) ∅ := by
  induction l with
  | nil => simp
  | cons f l ih =>
    simp only [List.foldr_cons, List.map_cons]
    rcases h : f.2.2.2.2 with _ | o
    · rw [verts_famStep_none f _ h, ih]; simp
    · rw [verts_famStep_some f _ o h, ih]
      simp only [Option.map_some, Option.getD_some]
      ext y; simp only [Finset.mem_union]; tauto

theorem mem_foldr_union_nat (L : List (Finset ℕ)) (y : ℕ) :
    y ∈ L.foldr (· ∪ ·) ∅ ↔ ∃ s ∈ L, y ∈ s := by
  induction L with
  | nil => simp
  | cons s L ih => simp [ih]

theorem card_foldr_union_nat (L : List (Finset ℕ)) :
    (L.foldr (· ∪ ·) ∅).card ≤ (L.map Finset.card).sum := by
  induction L with
  | nil => simp
  | cons s L ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left ih _)

theorem gB_step (M k ℓ : ℕ) (f : ℕ → ℕ) (h : M < ℓ) :
    gB M k f ℓ = f (k - ℓ) * (gB M k f (ℓ - 1) + 1) := by
  obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
  rw [gB, if_neg (by omega), Nat.add_sub_cancel]

theorem cntOf_cb (M : ℕ) (W F lg : ℝ) (k ℓ : ℕ) (ν ν' : ℝ) (h : M < ℓ) (hk : ℓ ≤ k) :
    cntOf M W F lg (.cb k ℓ ν) = 3 * W * cntOf M W F lg (.loc (k - ℓ)) +
      3 * W * F * cntOf M W F lg (.cb k (ℓ - 1) ν') := by
  obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
  simp only [cntOf]
  rw [cC, if_neg (by omega), Nat.add_sub_cancel, dif_pos (by omega)]

/-! ## Theorem: CB(k, ℓ, ν), `ℓ > M` -/
/-- CB(k, ℓ, ν), `ℓ > M` (Algorithm 6), from LOC(k − ℓ) and CB(k, ℓ − 1, ·). -/
theorem holds_cbStep (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (N : ℕ) (W F : ℝ)
    (hS : Std P R Adj N W F) (k ℓ : ℕ) (ν : ℝ) (hℓ : P.M < ℓ)
    (IHL : Holds P R Adj N W F (.loc (k - ℓ))) (IHC : ∀ ν', Holds P R Adj N W F (.cb k (ℓ - 1) ν')) :
    Holds P R Adj N W F (.cb k ℓ ν) := by
  intro addr ins hin hlive
  obtain ⟨hsort, hlenN, hMℓ, hℓk, hMk, hkM2, hν1, hνW, hC⟩ := hin
  obtain ⟨⟨hM, hL, -, hW, hF, hfB, -⟩, hR, -⟩ := hS
  have hν : 0 < ν := by linarith
  set U : Finset (Finset ℕ) := (ins.map Prod.snd).foldr (· ∪ ·) ∅ with hUdef
  have hUp : ∀ p ∈ ins, p.2 ⊆ U ∧ p.2.Nonempty ∧ (U.card : ℝ) ≤ ν * p.2.card :=
    fun p hp => ⟨fun S hS => (mem_foldr_union _ _).2 ⟨p.2, List.mem_map_of_mem hp, hS⟩,
      (hC p hp).1, (hC p hp).2.2⟩
  obtain ⟨t, Q, subs, rnd, gin, I⟩ := inv_run P R Adj k ℓ ν addr hR hℓ ⟨by omega, hℓk⟩ hν1 N W F
    hkM2 IHL U ins hsort hlenN hUp hlive ins.length le_rfl
  rw [List.take_of_length_le le_rfl] at I
  -- the children's summaries
  have hLsum : ∀ j ∈ Finset.Icc 1 t,
      Summary P R Adj N W F (.loc (k - ℓ)) (addr ++ [6, j, 0]) (strip (rnd j)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    apply IHL
    · exact ⟨by rw [strip_fst]; exact hsort.sublist ((I.rndS j).map _),
        by rw [strip_length]; exact (I.rndS j).length_le.trans hlenN, by omega⟩
    · rcases Nat.lt_or_ge j t with hjt | hjt
      · exact I.fin j hj.1 hjt
      · obtain rfl : j = t := by omega
        exact live_of_none I.curN
  have hSnon : ∀ e ∈ subs, e.2.2.1.Nonempty := by
    intro e he
    obtain ⟨p, hp, -, hp2⟩ := I.stat e he
    rw [← hp2]; exact (hC p ((I.rndS _).subset hp)).1
  have hSsum : ∀ q ∈ (subs.map key).toFinset,
      Summary P R Adj N W F (.cb k (ℓ - 1) (2 * ν)) (addr ++ [5, q.1, q.2]) (gin q) := by
    intro q hq
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hq)
    obtain ⟨-, hlv, -⟩ := I.ent e he
    have hpow : (2 : ℝ) ^ (ℓ - P.M) = 2 * 2 ^ (ℓ - 1 - P.M) := by
      rw [show ℓ - P.M = (ℓ - 1 - P.M) + 1 by omega, pow_succ]; ring
    refine IHC (2 * ν) _ _ ⟨hsort.sublist (I.ginS _), ?_, by omega, by omega, hMk, hkM2,
      by linarith, ?_, ?_⟩ hlv
    · have := (I.ginS (key e)).length_le
      simp only [List.length_map] at this
      omega
    · rw [hpow] at hνW; linarith
    · intro p hp
      obtain ⟨hpS, hcard⟩ := I.ginOK e he p hp
      obtain ⟨p', hp', -, hp'2⟩ := I.ginI _ p hp
      have hSpos : (0 : ℝ) < e.2.2.1.card := by exact_mod_cast (hSnon e he).card_pos
      refine ⟨?_, fun S hS => (hC p' hp').2.1 S (hp'2 hS), ?_⟩
      · rw [← Finset.card_pos]
        have : (0 : ℝ) < p.2.card := by
          by_contra hcon; push Not at hcon; nlinarith
        exact_mod_cast this
      · refine le_trans ?_ hcard
        exact_mod_cast Finset.card_le_card (fun S hS => by
          obtain ⟨T, hT, hST⟩ := (mem_foldr_union _ _).1 hS
          obtain ⟨p'', hp'', rfl⟩ := List.mem_map.1 hT
          exact (I.ginOK e he p'' hp'').1 hST)
  have hdepL : depOf P.M (.loc (k - ℓ)) ≤ k / P.M := by
    show (k - ℓ) / P.M + 1 ≤ k / P.M
    rw [← Nat.add_div_right _ (by omega : 0 < P.M)]
    exact Nat.div_le_div_right (by omega)
  obtain ⟨nb1, ext1, s1, a1, a2, a3, a4, a5, a6⟩ := combine P R Adj N W F (Finset.Icc 1 t)
    (fun _ => Mode.loc (k - ℓ)) (fun j => addr ++ [6, j, 0]) (fun j => strip (rnd j)) (k / P.M)
    (cntOf P.M W F (Real.logb 2 N) (.loc (k - ℓ))) hLsum (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => hdepL) (fun _ _ => le_rfl)
  obtain ⟨nb2, ext2, s2, b1, b2, b3, b4, b5, b6⟩ := combine P R Adj N W F ((subs.map key).toFinset)
    (fun _ => Mode.cb k (ℓ - 1) (2 * ν)) (fun q => addr ++ [5, q.1, q.2]) gin (k / P.M)
    (cntOf P.M W F (Real.logb 2 N) (.cb k (ℓ - 1) (2 * ν))) hSsum (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  simp only [strip_length] at a2 a5
  have hcount := I.count
  -- colors
  have hcolsub : (instRun P R Adj (.cb k ℓ ν) addr ins Inst.fresh).2.1.toFinset ⊆
      (Finset.Icc 1 t).biUnion (fun j => (instRun P R Adj (.loc (k - ℓ)) (addr ++ [6, j, 0])
        (strip (rnd j)) Inst.fresh).2.1.toFinset) ∪
      (subs.map key).toFinset.biUnion (fun q => (instRun P R Adj (.cb k (ℓ - 1) (2 * ν))
        (addr ++ [5, q.1, q.2]) (gin q) Inst.fresh).2.1.toFinset) := by
    intro c hc
    rw [List.mem_toFinset] at hc
    rcases I.cols c hc with ⟨j, hj, hcj⟩ | ⟨q, hq, hcq⟩
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨j, hj, List.mem_toFinset.2 hcj⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_biUnion.2 ⟨q, List.mem_toFinset.2 hq, List.mem_toFinset.2 hcq⟩)
  have hcolcard := (Finset.card_le_card hcolsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le))
  have hcolcard' : ((instRun P R Adj (.cb k ℓ ν) addr ins Inst.fresh).2.1.toFinset.card : ℝ) ≤
      ∑ j ∈ Finset.Icc 1 t, ((instRun P R Adj (.loc (k - ℓ)) (addr ++ [6, j, 0])
        (strip (rnd j)) Inst.fresh).2.1.toFinset.card : ℝ) +
      ∑ q ∈ (subs.map key).toFinset, ((instRun P R Adj (.cb k (ℓ - 1) (2 * ν))
        (addr ++ [5, q.1, q.2]) (gin q) Inst.fresh).2.1.toFinset.card : ℝ) := by
    exact_mod_cast hcolcard
  -- counting the children
  have h2pow : (1 : ℝ) ≤ 2 ^ (ℓ - P.M) := one_le_pow₀ (by norm_num)
  have hνW' : ν ≤ W := by nlinarith
  have hT : (t : ℝ) ≤ 3 * W := by have := I.bound; linarith
  have hsubsLen : subs.length ≤ (t - 1) * fB P.M (k - ℓ) := by
    have := length_le_count (subs.map (·.1)) (Finset.Icc 1 (t - 1)) (by
      intro a ha
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
      have := I.keyR e he
      rw [Finset.mem_Icc]; omega) _ I.fam
    simpa using this
  have hK : (((subs.map key).toFinset.card : ℕ) : ℝ) ≤ 3 * W * F := by
    have h1 : (subs.map key).toFinset.card ≤ (t - 1) * fB P.M (k - ℓ) :=
      (List.toFinset_card_le _).trans (by simpa using hsubsLen)
    have h2 : (((t - 1) * fB P.M (k - ℓ) : ℕ) : ℝ) ≤ ((t : ℝ) - 1) * F := by
      push_cast
      rw [Nat.cast_sub I.t1]
      have := hfB (k - ℓ) (by omega)
      have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast I.t1
      push_cast
      exact mul_le_mul_of_nonneg_left this (by linarith)
    have h3 : ((t : ℝ) - 1) * F ≤ 3 * W * F := by
      have := I.bound
      exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have := Nat.cast_le (α := ℝ) |>.2 h1
    linarith
  have cL0 : 0 ≤ cntOf P.M W F (Real.logb 2 N) (.loc (k - ℓ)) :=
    cL_nonneg _ _ _ _ (by linarith) (by linarith) (lg_nonneg N) _
  have cC0 : 0 ≤ cntOf P.M W F (Real.logb 2 N) (.cb k (ℓ - 1) (2 * ν)) :=
    cC_nonneg _ _ _ _ _ (by linarith) (by linarith) (fun j => by
      split_ifs
      · exact cL_nonneg _ _ _ _ (by linarith) (by linarith) (lg_nonneg N) _
      · exact le_rfl) _
  have hLpos : (0 : ℝ) < P.L := by exact_mod_cast hL
  unfold Summary
  refine ⟨nb1 + nb2, ext1 + ext2, s1 ++ s2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · push_cast; linarith
  · simp only [ownBins, List.map_append, List.sum_append, add_zero]
    have hc' : ((∑ j ∈ Finset.Icc 1 t, (rnd j).length : ℕ) : ℝ) +
        ((∑ q ∈ (subs.map key).toFinset, (gin q).length : ℕ) : ℝ) ≤ ins.length := by
      exact_mod_cast hcount
    have : ((∑ j ∈ Finset.Icc 1 t, (rnd j).length : ℕ) : ℝ) / P.L +
        ((∑ q ∈ (subs.map key).toFinset, (gin q).length : ℕ) : ℝ) / P.L ≤ (ins.length : ℝ) / P.L := by
      rw [← add_div]; exact div_le_div_of_nonneg_right hc' hLpos.le
    push_cast at this a2 b2 ⊢
    linarith
  · simp only [ownExt, List.length_append]; omega
  · intro _; simp only [List.length_append]; omega
  · rw [cntOf_cb P.M W F _ k ℓ ν (2 * ν) hℓ hℓk]
    simp only [List.length_append, Nat.card_Icc] at a4 b4 ⊢
    push_cast
    simp only [Nat.add_sub_cancel] at a4
    have e1 := mul_le_mul_of_nonneg_right hT cL0
    have e2 := mul_le_mul_of_nonneg_right hK cC0
    linarith
  · simp only [depOf, List.sum_append]
    have := Nat.add_le_add a5 b5
    rw [← add_mul] at this
    exact this.trans (Nat.mul_le_mul_right _ hcount)
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact a6 x hx
    · exact b6 x hx
  · intro o ho
    obtain ⟨i, ⟨e1, he1, he1i⟩, hall, rfl⟩ := I.last o ho
    set fam := subs.filter (fun f => decide (f.1 = i)) with hfamdef
    have hfam : ∀ f ∈ fam, ∃ o', f.2.2.2.2 = some o' ∧ (Out.verts o').Nonempty ∧
        Out.verts o' ⊆ (ins.map Prod.fst).toFinset ∪ inVerts ins ∧
        (Out.verts o').card ≤ gB P.M k (fB P.M) (ℓ - 1) := by
      intro f hf
      have hs := List.all_eq_true.1 hall f hf
      rw [List.mem_filter, decide_eq_true_eq] at hf
      obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.1 hs
      obtain ⟨-, -, hl⟩ := I.ent f hf.1
      rw [ho'] at hl
      have hl' : (subR P R Adj k ℓ ν addr (key f) (gin (key f))).2.2.getLast? = some (some o') := by
        cases h : (subR P R Adj k ℓ ν addr (key f) (gin (key f))).2.2.getLast? with
        | none => rw [h] at hl; simp at hl
        | some y => rw [h] at hl; simp at hl; rw [hl]
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hout⟩ :=
        hSsum (key f) (List.mem_toFinset.2 (List.mem_map_of_mem hf.1))
      obtain ⟨h1, h2, h3⟩ := hout o' hl'
      refine ⟨o', ho', h1, ?_, h3⟩
      intro y hy
      rcases Finset.mem_union.1 (h2 hy) with hy | hy
      · exact Finset.mem_union_left _ (by
          rw [List.mem_toFinset] at hy ⊢; exact (I.ginS _).subset hy)
      · apply Finset.mem_union_right
        rw [mem_inVerts] at hy ⊢
        obtain ⟨p, hp, S, hS, hyS⟩ := hy
        obtain ⟨p', hp', -, hsub⟩ := I.ginI _ p hp
        exact ⟨p', hp', S, hsub hS, hyS⟩
    have hfamlen : fam.length ≤ fB P.M (k - ℓ) := by
      rw [hfamdef, filter_len_count]; exact I.fam i
    have he1fam : e1 ∈ fam := by
      rw [hfamdef, List.mem_filter, decide_eq_true_eq]; exact ⟨he1, he1i⟩
    have hV := verts_fold fam ((∅ : Finset (Finset ℕ)), lookupQ Q i)
    have hinit : Out.verts ((∅ : Finset (Finset ℕ)), lookupQ Q i) = lookupQ Q i := by
      simp [Out.verts]
    have hQ : lookupQ Q i ⊆ (ins.map Prod.fst).toFinset ∧ (lookupQ Q i).card ≤ fB P.M (k - ℓ) := by
      rcases lookupQ_cases Q i with h | ⟨q, hq, h⟩
      · rw [h]; simp
      · rw [h]; exact I.Qok q hq
    set g : Sub → Finset ℕ := fun f => (f.2.2.2.2.map Out.verts).getD ∅ with hg
    have hgf : ∀ f ∈ fam, (g f).card ≤ gB P.M k (fB P.M) (ℓ - 1) ∧
        g f ⊆ (ins.map Prod.fst).toFinset ∪ inVerts ins := by
      intro f hf
      obtain ⟨o', ho', -, h2, h3⟩ := hfam f hf
      simp only [g, ho', Option.map_some, Option.getD_some]
      exact ⟨h3, h2⟩
    show (Out.verts (fam.foldr famStep (∅, lookupQ Q i))).Nonempty ∧
      Out.verts (fam.foldr famStep (∅, lookupQ Q i)) ⊆ (ins.map Prod.fst).toFinset ∪ inVerts ins ∧
      (Out.verts (fam.foldr famStep (∅, lookupQ Q i))).card ≤ gB P.M k (fB P.M) ℓ
    rw [hV, hinit]
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨o', ho', ⟨y, hy⟩, -, -⟩ := hfam e1 he1fam
      refine ⟨y, Finset.mem_union_right _ ((mem_foldr_union_nat _ _).2 ⟨g e1,
        List.mem_map_of_mem he1fam, ?_⟩)⟩
      simp only [g, ho', Option.map_some, Option.getD_some]; exact hy
    · apply Finset.union_subset (hQ.1.trans Finset.subset_union_left)
      intro y hy
      obtain ⟨s, hs, hys⟩ := (mem_foldr_union_nat _ _).1 hy
      obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hs
      exact (hgf f hf).2 hys
    · refine (Finset.card_union_le _ _).trans ?_
      have hsum : ((fam.map g).map Finset.card).sum ≤ fam.length * gB P.M k (fB P.M) (ℓ - 1) := by
        have := List.sum_le_card_nsmul ((fam.map g).map Finset.card) (gB P.M k (fB P.M) (ℓ - 1))
          (by
            intro x hx
            simp only [List.map_map, List.mem_map, Function.comp_apply] at hx
            obtain ⟨f, hf, rfl⟩ := hx
            exact (hgf f hf).1)
        simpa using this
      have hVl := (card_foldr_union_nat (fam.map g)).trans hsum
      rw [gB_step _ _ _ _ hℓ]
      have := Nat.mul_le_mul_right (gB P.M k (fB P.M) (ℓ - 1)) hfamlen
      nlinarith [hQ.2]

end OnlineColoringKYY.Supplement.Dev.T626.PartCS
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626
open Classical OnlineColoringKYY.Supplement
alias holds_cbStep := OnlineColoringKYY.Supplement.Dev.T626.PartCS.holds_cbStep

end OnlineColoringKYY.Supplement.Dev.T626
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartGL
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
/-! ## Well-founded assembly -/
/-- Well-founded induction over `Mode.meas` from the case lemmas. -/
theorem holds_all (P : LocParams) (R : Resolver) (Adj : ℕ → ℕ → Prop) (N : ℕ) (W F : ℝ)
    (hS : Std P R Adj N W F) (m : Mode) : Holds P R Adj N W F m := by
  have hM : 2 ≤ P.M := hS.1.1
  have wf : WellFounded (InvImage (Prod.Lex (· < ·) (· < ·)) Mode.meas) :=
    InvImage.wf _ (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf)
  induction m using wf.induction with
  | _ m IH =>
  have lexL : ∀ (a b : Mode), a.meas.1 < b.meas.1 →
      InvImage (Prod.Lex (· < ·) (· < ·)) Mode.meas a b := by
    intro a b h
    show Prod.Lex _ _ a.meas b.meas
    rcases ha : a.meas with ⟨a1, a2⟩
    rcases hb : b.meas with ⟨b1, b2⟩
    rw [ha, hb] at h
    exact Prod.Lex.left _ _ h
  have lexR : ∀ (a b : Mode), a.meas.1 = b.meas.1 → a.meas.2 < b.meas.2 →
      InvImage (Prod.Lex (· < ·) (· < ·)) Mode.meas a b := by
    intro a b h1 h2
    show Prod.Lex _ _ a.meas b.meas
    rcases ha : a.meas with ⟨a1, a2⟩
    rcases hb : b.meas with ⟨b1, b2⟩
    rw [ha, hb] at h1 h2
    simp only at h1 h2
    subst h1
    exact Prod.Lex.right _ h2
  cases m with
  | loc k =>
    exact holds_loc P R Adj N W F hS k
      (fun n => IH _ (lexR _ _ (by simp [Mode.meas]) (by simp [Mode.meas])))
  | locP k n =>
    by_cases hk : k ≤ P.M
    · exact holds_small P R Adj N W F hS k n hk
    · exact holds_big P R Adj N W F hS k n (by omega)
        (fun ν => IH _ (lexR _ _ (by simp [Mode.meas]) (by simp [Mode.meas])))
  | cb k ℓ ν =>
    by_cases hv : P.M < k ∧ ℓ ≤ k
    · by_cases hℓ : ℓ ≤ P.M
      · exact holds_cbBase P R Adj N W F hS k ℓ ν hℓ
          (IH _ (lexL _ _ (by simp only [Mode.meas]; omega)))
      · exact holds_cbStep P R Adj N W F hS k ℓ ν (by omega)
          (IH _ (lexL _ _ (by simp only [Mode.meas]; omega)))
          (fun ν' => IH _ (lexR _ _ (by simp [Mode.meas]) (by simp only [Mode.meas]; omega)))
    · intro addr ins hin
      exact absurd ⟨hin.2.2.2.2.1, hin.2.2.2.1⟩ hv

end OnlineColoringKYY.Supplement.Dev.T626.PartGL
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626
open Classical OnlineColoringKYY.Supplement
/-! ### Assembly -/
alias holds_all := OnlineColoringKYY.Supplement.Dev.T626.PartGL.holds_all

end OnlineColoringKYY.Supplement.Dev.T626
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartGL
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
/-! ## Prefix adjacency -/
theorem prefixAdj_eq {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    prefixAdj G v = AdjAt (fun a b => ∃ (ha : a < n) (hb : b < n), G.Adj ⟨a, ha⟩ ⟨b, hb⟩) v.val := by
  funext a b
  apply propext
  have hv := v.isLt
  simp only [prefixAdj, AdjAt, prefixGraph, SimpleGraph.comap_adj]
  constructor
  · rintro ⟨ha, hb, h⟩
    exact ⟨by omega, by omega, by omega, by omega, h⟩
  · rintro ⟨ha, hb, ha', hb', h⟩
    exact ⟨by omega, by omega, h⟩

end OnlineColoringKYY.Supplement.Dev.T626.PartGL
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626
open Classical OnlineColoringKYY.Supplement

end OnlineColoringKYY.Supplement.Dev.T626
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartGL
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
/-! ## The top-level run -/
theorem live_cons_none (xs : List (Option Out)) (h : Live xs) : Live (none :: xs) := by
  intro o ho
  cases xs with
  | nil => simp at ho
  | cons y ys =>
    rw [List.dropLast_cons_cons] at ho
    rcases List.mem_cons.1 ho with rfl | ho
    · rfl
    · exact h o ho

theorem fold_done (P : LocParams) (R : Resolver) (m : Mode) {n : ℕ} (G : SimpleGraph (Fin n))
    (l : List (Fin n)) (s : Inst) (cs : List Color) :
    l.foldl (fun (acc : Inst × Bool × List Color) v =>
      if acc.2.1 then acc else
        let res := locStep P R (prefixAdj G v) v.val m [] ∅ acc.1
        (res.1, res.2.2.isSome, acc.2.2 ++ [res.2.1])) (s, true, cs) = (s, true, cs) := by
  induction l with
  | nil => rfl
  | cons v l ih => simpa using ih

theorem fold_run (P : LocParams) (R : Resolver) (m : Mode) {n : ℕ} (G : SimpleGraph (Fin n))
    (l : List (Fin n)) (s : Inst) (cs : List Color) :
    ∃ pre : List (Fin n), pre <+: l ∧
      Live (instRun P R (fun a b => ∃ (ha : a < n) (hb : b < n), G.Adj ⟨a, ha⟩ ⟨b, hb⟩) m []
        (pre.map (fun v => ((v.val : ℕ), (∅ : Finset (Finset ℕ))))) s).2.2 ∧
      (l.foldl (fun (acc : Inst × Bool × List Color) v =>
        if acc.2.1 then acc else
          let res := locStep P R (prefixAdj G v) v.val m [] ∅ acc.1
          (res.1, res.2.2.isSome, acc.2.2 ++ [res.2.1])) (s, false, cs)).2.2 =
        cs ++ (instRun P R (fun a b => ∃ (ha : a < n) (hb : b < n), G.Adj ⟨a, ha⟩ ⟨b, hb⟩) m []
          (pre.map (fun v => ((v.val : ℕ), (∅ : Finset (Finset ℕ))))) s).2.1 := by
  induction l generalizing s cs with
  | nil =>
    refine ⟨[], List.prefix_refl _, ?_, ?_⟩
    · intro o ho; simp [instRun] at ho
    · simp [instRun]
  | cons v l ih =>
    rw [List.foldl_cons]
    simp only [Bool.false_eq_true, if_false]
    rw [prefixAdj_eq]
    set res := locStep P R (AdjAt (fun a b => ∃ (ha : a < n) (hb : b < n), G.Adj ⟨a, ha⟩ ⟨b, hb⟩)
      v.val) v.val m [] ∅ s with hres
    cases hout : res.2.2 with
    | some o =>
      simp only [Option.isSome_some]
      rw [fold_done]
      refine ⟨[v], List.cons_prefix_cons.2 ⟨rfl, List.nil_prefix⟩, ?_, ?_⟩
      · intro o' ho'; simp [instRun] at ho'
      · simp [instRun, ← hres]
    | none =>
      simp only [Option.isSome_none]
      obtain ⟨pre, hpre, hlive, heq⟩ := ih res.1 (cs ++ [res.2.1])
      refine ⟨v :: pre, List.cons_prefix_cons.2 ⟨rfl, hpre⟩, ?_, ?_⟩
      · simp only [List.map_cons, instRun]
        rw [← hres, hout]
        exact live_cons_none _ hlive
      · rw [heq]
        simp [instRun, ← hres]

/-- The top-level run is an instance run of LOC(M²) on the vertices up to termination. -/
theorem locRun_eq (ε : ℝ) (N : ℕ) (R : Resolver) {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ ins : List (ℕ × Finset (Finset ℕ)),
      (ins.map Prod.fst).Pairwise (· < ·) ∧ ins.length ≤ n ∧
      Live (instRun (locParams ε N) R (fun a b => ∃ (ha : a < n) (hb : b < n), G.Adj ⟨a, ha⟩ ⟨b, hb⟩)
        (.loc (locM ε N ^ 2)) [] ins Inst.fresh).2.2 ∧
      locRun ε N R G = (instRun (locParams ε N) R
        (fun a b => ∃ (ha : a < n) (hb : b < n), G.Adj ⟨a, ha⟩ ⟨b, hb⟩)
        (.loc (locM ε N ^ 2)) [] ins Inst.fresh).2.1 := by
  obtain ⟨pre, hpre, hlive, heq⟩ :=
    fold_run (locParams ε N) R (.loc (locM ε N ^ 2)) G (List.finRange n) Inst.fresh []
  refine ⟨pre.map (fun v => ((v.val : ℕ), (∅ : Finset (Finset ℕ)))), ?_, ?_, hlive, ?_⟩
  · rw [List.map_map]
    have hp : pre.Pairwise (· < ·) := (List.pairwise_lt_finRange n).sublist hpre.sublist
    rw [List.pairwise_map]
    exact hp.imp (fun h => h)
  · simpa using hpre.length_le
  · unfold locRun
    rw [heq, List.nil_append]

end OnlineColoringKYY.Supplement.Dev.T626.PartGL
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626
open Classical OnlineColoringKYY.Supplement
alias locRun_eq := OnlineColoringKYY.Supplement.Dev.T626.PartGL.locRun_eq

end OnlineColoringKYY.Supplement.Dev.T626
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartAC
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
/-!
Closed-form bounds of `ASY.lean`: `nSeq_le`, `fB_le`, `cL_le`, `nu_le`, `holder`.
-/
/-! ### `nSeq_le` -/
theorem nSeq_step_le (A q m : ℕ) (hA : 2 ≤ A) (hq : q + 3 ≤ A + 1) (hm : 2 * A ^ 2 ≤ m) :
    6 * A ^ 2 * (6 * (q + 3) * m ^ (q + 2)) ^ (6 * A ^ 2) ≤ m ^ (6 * (A + 1) ^ 3) := by
  have hA2 : A + 1 ≤ A ^ 2 := by nlinarith
  have hm8 : 8 ≤ m := by nlinarith
  have hm1 : 1 ≤ m := by omega
  have h3 : 3 * m ≤ m ^ 3 := by
    have : m ^ 3 = m * m * m := by ring
    rw [this]; nlinarith
  have h1 : 6 * A ^ 2 ≤ m ^ 3 := by omega
  have h2 : 6 * (q + 3) ≤ m ^ 3 := by omega
  calc 6 * A ^ 2 * (6 * (q + 3) * m ^ (q + 2)) ^ (6 * A ^ 2)
      ≤ m ^ 3 * (m ^ 3 * m ^ (q + 2)) ^ (6 * A ^ 2) := by
        gcongr
    _ = m ^ (3 + (q + 5) * (6 * A ^ 2)) := by
        rw [← pow_add, ← pow_mul, ← pow_add]; ring_nf
    _ ≤ m ^ (6 * (A + 1) ^ 3) := by
        apply Nat.pow_le_pow_right hm1
        have : q + 5 ≤ A + 3 := by omega
        nlinarith

theorem nSeq_aux (A : ℕ) (hA : 1 ≤ A) : ∀ q, q + 2 ≤ A + 1 →
    2 * A ^ 2 ≤ nSeq A (q + 2) ∧ nSeq A (q + 2) ≤ (2 * A ^ 2) ^ ((6 * (A + 1) ^ 3) ^ q) := by
  intro q
  induction q with
  | zero => intro _; simp [nSeq]
  | succ q ih =>
    intro hq
    obtain ⟨h1, h2⟩ := ih (by omega)
    have e : nSeq A (q + 1 + 2) =
        6 * A ^ 2 * (6 * (q + 3) * (nSeq A (q + 2)) ^ (q + 2)) ^ (6 * A ^ 2) := by
      show nSeq A (q + 3) = _
      rw [nSeq]
    rw [e]
    have hpos : 1 ≤ (6 * (q + 3) * (nSeq A (q + 2)) ^ (q + 2)) ^ (6 * A ^ 2) :=
      Nat.one_le_pow _ _ (Nat.mul_pos (by omega) (Nat.pow_pos (by nlinarith)))
    refine ⟨by nlinarith, ?_⟩
    refine (nSeq_step_le A q _ (by omega) (by omega) h1).trans ?_
    calc nSeq A (q + 2) ^ (6 * (A + 1) ^ 3)
        ≤ ((2 * A ^ 2) ^ ((6 * (A + 1) ^ 3) ^ q)) ^ (6 * (A + 1) ^ 3) := Nat.pow_le_pow_left h2 _
      _ = _ := by rw [← pow_mul, ← pow_succ]

theorem two_mul_le_two_pow (A : ℕ) (hA : 1 ≤ A) : 2 * A ≤ 2 ^ A := by
  induction A, hA using Nat.le_induction with
  | base => norm_num
  | succ A hA ih => rw [pow_succ]; omega

theorem nSeq_le (A : ℕ) (hA : 1 ≤ A) : nSeq A (A + 1) ≤ 2 ^ ((A + 1) ^ (8 * (A + 1))) := by
  obtain ⟨-, h⟩ := nSeq_aux A hA (A - 1) (by omega)
  rw [show A - 1 + 2 = A + 1 by omega] at h
  refine h.trans ?_
  have hb : 2 * A ^ 2 ≤ 2 ^ (2 * A) := by
    have := two_mul_le_two_pow A hA
    calc 2 * A ^ 2 ≤ (2 * A) ^ 2 := by nlinarith
      _ ≤ (2 ^ A) ^ 2 := Nat.pow_le_pow_left this 2
      _ = 2 ^ (2 * A) := by rw [← pow_mul, mul_comm]
  refine (Nat.pow_le_pow_left hb _).trans ?_
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by norm_num)
  have hT : 6 * (A + 1) ^ 3 ≤ (A + 1) ^ 6 := by
    have : 8 ≤ (A + 1) ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ (A + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    calc 6 * (A + 1) ^ 3 ≤ (A + 1) ^ 3 * (A + 1) ^ 3 := Nat.mul_le_mul_right _ (by omega)
      _ = (A + 1) ^ 6 := by ring
  calc 2 * A * (6 * (A + 1) ^ 3) ^ (A - 1) ≤ (A + 1) ^ 2 * ((A + 1) ^ 6) ^ (A - 1) := by
        gcongr; nlinarith
    _ = (A + 1) ^ (2 + 6 * (A - 1)) := by rw [← pow_mul, ← pow_add]
    _ ≤ (A + 1) ^ (8 * (A + 1)) := Nat.pow_le_pow_right (by omega) (by omega)

end OnlineColoringKYY.Supplement.Dev.T626.PartAC
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626
open Classical OnlineColoringKYY.Supplement
alias nSeq_le := OnlineColoringKYY.Supplement.Dev.T626.PartAC.nSeq_le

end OnlineColoringKYY.Supplement.Dev.T626
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartAC
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
/-! ### `fB_le` -/
theorem gB_congr (M k : ℕ) (hM : 1 ≤ M) (hk : 1 ≤ k) (f f' : ℕ → ℕ) (h : ∀ j < k, f j = f' j) :
    ∀ ℓ, gB M k f ℓ = gB M k f' ℓ := by
  intro ℓ
  induction ℓ with
  | zero => simp only [gB]; rw [h _ (by omega)]
  | succ ℓ ih => simp only [gB]; rw [h (k - M) (by omega), h (k - (ℓ+1)) (by omega), ih]

theorem fB_eq (M k : ℕ) (hM : 1 ≤ M) (hk : M < k) : fB M k = gB M k (fB M) k := by
  rw [fB, if_neg (by omega)]
  exact gB_congr M k hM (by omega) _ _ (fun j hj => by simp [hj]) k

theorem gB_small (M k : ℕ) (f : ℕ → ℕ) : ∀ ℓ, ℓ ≤ M → gB M k f ℓ = (M + 1) * f (k - M)
  | 0, _ => by simp [gB]
  | ℓ + 1, h => by simp [gB, h]

theorem gB_step (M k : ℕ) (f : ℕ → ℕ) (ℓ : ℕ) (h : M < ℓ + 1) :
    gB M k f (ℓ + 1) = f (k - (ℓ + 1)) * (gB M k f ℓ + 1) := by
  simp only [gB, if_neg (show ¬ (ℓ + 1 ≤ M) by omega)]

theorem fB_aux (M : ℕ) (hM : 2 ≤ M) :
    ∀ k, k ≤ M ^ 2 → fB M k + 1 ≤ (M + 1) ^ (M ^ (2 * (k / M) + 3)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  intro hk
  by_cases hkM : k ≤ M
  · rw [fB, if_pos hkM]
    have h2 : 2 ≤ M ^ (2 * (k / M) + 3) := le_trans hM (Nat.le_self_pow (by omega) M)
    calc M + 1 + 1 ≤ (M + 1) ^ 2 := by nlinarith
      _ ≤ _ := Nat.pow_le_pow_right (by omega) h2
  · push Not at hkM
    set E := M ^ (2 * ((k - M) / M) + 3) with hE
    have hE1 : 1 ≤ E := Nat.one_le_pow _ _ (by omega)
    have hfj : ∀ j, j ≤ k - M → fB M j + 1 ≤ (M + 1) ^ E := by
      intro j hj
      refine (IH j (by omega) (by omega)).trans (Nat.pow_le_pow_right (by omega) ?_)
      exact Nat.pow_le_pow_right (by omega)
        (by have := Nat.div_le_div_right (c := M) hj; omega)
    have hg : ∀ ℓ, M ≤ ℓ → ℓ ≤ k → gB M k (fB M) ℓ + 1 ≤ (M + 1) ^ (1 + (ℓ - M + 1) * E) := by
      intro ℓ hℓ
      induction ℓ, hℓ using Nat.le_induction with
      | base =>
        intro _
        rw [gB_small M k _ M le_rfl]
        have := hfj (k - M) le_rfl
        calc (M + 1) * fB M (k - M) + 1 ≤ (M + 1) * (fB M (k - M) + 1) := by nlinarith
          _ ≤ (M + 1) * (M + 1) ^ E := Nat.mul_le_mul_left _ this
          _ = (M + 1) ^ (1 + (M - M + 1) * E) := by
            rw [Nat.sub_self, zero_add, one_mul, pow_add, pow_one]
      | succ ℓ hℓ ih =>
        intro hℓk
        rw [gB_step M k _ ℓ (by omega)]
        have h1 := ih (by omega)
        have h2 := hfj (k - (ℓ + 1)) (by omega)
        have e : 1 + (ℓ + 1 - M + 1) * E = E + (1 + (ℓ - M + 1) * E) := by
          have : ℓ + 1 - M + 1 = (ℓ - M + 1) + 1 := by omega
          rw [this]; ring
        rw [e, pow_add]
        calc fB M (k - (ℓ + 1)) * (gB M k (fB M) ℓ + 1) + 1
            ≤ (fB M (k - (ℓ + 1)) + 1) * (gB M k (fB M) ℓ + 1) := by nlinarith
          _ ≤ _ := Nat.mul_le_mul h2 h1
    rw [fB_eq M k (by omega) hkM]
    refine (hg k hkM.le le_rfl).trans (Nat.pow_le_pow_right (by omega) ?_)
    have hdiv : k / M = (k - M) / M + 1 := Nat.div_eq_sub_div (by omega) hkM.le
    rw [hdiv, show 2 * ((k - M) / M + 1) + 3 = (2 * ((k - M) / M) + 3) + 2 by ring, pow_add, ← hE]
    have hM2 : k - M + 2 ≤ M ^ 2 := by
      have : 2 * M ≤ M ^ 2 := by nlinarith
      omega
    nlinarith

theorem fB_le (M : ℕ) (hM : 2 ≤ M) (k : ℕ) (hk : k ≤ M ^ 2) :
    fB M k + 1 ≤ (M + 1) ^ (M ^ (2 * M + 3)) := by
  refine (fB_aux M hM k hk).trans (Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) ?_))
  have : k / M ≤ M := Nat.div_le_of_le_mul (by nlinarith)
  omega

end OnlineColoringKYY.Supplement.Dev.T626.PartAC
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626
open Classical OnlineColoringKYY.Supplement
alias fB_le := OnlineColoringKYY.Supplement.Dev.T626.PartAC.fB_le

end OnlineColoringKYY.Supplement.Dev.T626
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartAC
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
/-! ### `cL_le` -/
theorem cC_small (M : ℕ) (W F : ℝ) (k : ℕ) (fL : ℕ → ℝ) :
    ∀ ℓ, ℓ ≤ M → cC M W F k fL ℓ = fL (k - M)
  | 0, _ => by simp [cC]
  | ℓ + 1, h => by simp [cC, h]

theorem cC_step (M : ℕ) (W F : ℝ) (k : ℕ) (fL : ℕ → ℝ) (ℓ : ℕ) (h : M < ℓ + 1) :
    cC M W F k fL (ℓ + 1) = 3 * W * fL (k - (ℓ + 1)) + 3 * W * F * cC M W F k fL ℓ := by
  simp only [cC, if_neg (show ¬ (ℓ + 1 ≤ M) by omega)]

theorem cL_le (M : ℕ) (hM : 2 ≤ M) (W F lg : ℝ) (hW : 1 ≤ W) (hF : 1 ≤ F) (hlg : 0 ≤ lg)
    (k : ℕ) (hk : k ≤ M ^ 2) :
    cL M W F lg k ≤ (2 * (3 * W * (F + 1) * (lg + 2))) ^ (M * (k + M)) := by
  set C : ℝ := 3 * W * (F + 1) with hC
  have hC1 : 1 ≤ C := by nlinarith
  have hK1 : 1 ≤ 2 * (C * (lg + 2)) := by nlinarith
  clear_value C
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  by_cases hkM : k ≤ M
  · rw [cL, if_pos hkM]
    exact one_le_pow₀ hK1
  push Not at hkM
  set B : ℝ := (2 * (C * (lg + 2))) ^ (M * k) with hB
  have hB1 : 1 ≤ B := one_le_pow₀ hK1
  clear_value B
  set fL : ℕ → ℝ := fun j => if _h : j < k then cL M W F lg j else 0 with hfL
  have hfj : ∀ j, j ≤ k - M → fL j ≤ B := by
    intro j hj
    have hjk : j < k := by omega
    simp only [hfL, dif_pos hjk]
    refine (IH j hjk (by omega)).trans (hB ▸ pow_le_pow_right₀ hK1 ?_)
    exact Nat.mul_le_mul_left _ (by omega)
  have hc : ∀ ℓ, M ≤ ℓ → ℓ ≤ k → cC M W F k fL ℓ ≤ C ^ (ℓ - M + 1) * B := by
    intro ℓ hℓ
    induction ℓ, hℓ using Nat.le_induction with
    | base =>
      intro _
      rw [cC_small M W F k fL M le_rfl, Nat.sub_self, zero_add, pow_one]
      nlinarith [hfj (k - M) le_rfl]
    | succ ℓ hℓ ih =>
      intro hℓk
      rw [cC_step M W F k fL ℓ (by omega)]
      have h1 := ih (by omega)
      have h2 := hfj (k - (ℓ + 1)) (by omega)
      have hp : 1 ≤ C ^ (ℓ - M + 1) := one_le_pow₀ hC1
      rw [show ℓ + 1 - M + 1 = (ℓ - M + 1) + 1 by omega, pow_succ]
      have hW0 : 0 ≤ 3 * W := by linarith
      have hWF : 0 ≤ 3 * W * F := by nlinarith
      calc 3 * W * fL (k - (ℓ + 1)) + 3 * W * F * cC M W F k fL ℓ
          ≤ 3 * W * (C ^ (ℓ - M + 1) * B) + 3 * W * F * (C ^ (ℓ - M + 1) * B) := by
            gcongr
            nlinarith
        _ = C ^ (ℓ - M + 1) * C * B := by rw [hC]; ring
  rw [cL, if_neg (by omega)]
  have hck := hc k hkM.le le_rfl
  set e := k - M + 1 with he
  have he1 : e ≠ 0 := by omega
  have hCe : 1 ≤ C ^ e := one_le_pow₀ hC1
  have hlg2 : lg + 2 ≤ (lg + 2) ^ e := le_self_pow₀ (by linarith) he1
  calc 1 + (lg + 1) * cC M W F k fL k ≤ 1 + (lg + 1) * (C ^ e * B) := by gcongr
    _ ≤ (lg + 2) * (C ^ e * B) := by nlinarith
    _ ≤ (lg + 2) ^ e * C ^ e * B := by
        rw [← mul_assoc]; gcongr
    _ = (C * (lg + 2)) ^ e * B := by rw [mul_pow, mul_comm ((lg + 2) ^ e)]
    _ ≤ (2 * (C * (lg + 2))) ^ e * B := by
        have h0 : 0 ≤ C * (lg + 2) := mul_nonneg (by linarith) (by linarith)
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 (by linarith) e) (by linarith)
    _ ≤ (2 * (C * (lg + 2))) ^ (M * M) * B := by
        refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK1 ?_) (by linarith)
        have : k ≤ M * M := by nlinarith
        omega
    _ = (2 * (C * (lg + 2))) ^ (M * (k + M)) := by rw [hB, ← pow_add]; ring_nf
    _ = _ := by rw [hC]

end OnlineColoringKYY.Supplement.Dev.T626.PartAC
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626
open Classical OnlineColoringKYY.Supplement
alias cL_le := OnlineColoringKYY.Supplement.Dev.T626.PartAC.cL_le

end OnlineColoringKYY.Supplement.Dev.T626
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartAC
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
/-! ### `nu_le` -/
theorem Jof_bound (P : LocParams) (k n : ℕ) (hn : 1 ≤ n) (hL : 1 ≤ P.L) :
    (n : ℝ) / (Jof P k n : ℝ) ≤ 2 * max (P.L : ℝ) ((n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ 5)) ∧
      (1 : ℝ) ≤ (Jof P k n : ℝ) := by
  have hJdef : (Jof P k n : ℝ) = ((max 1 ⌊(n : ℝ) / max (P.L : ℝ) ((n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ 5))⌋₊ : ℕ) : ℝ) := rfl
  have hm1 : (1 : ℝ) ≤ max (P.L : ℝ) ((n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ 5)) :=
    le_max_of_le_left (by exact_mod_cast hL)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  generalize max (P.L : ℝ) ((n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ 5)) = m at hJdef hm1 ⊢
  have hJ1 : (1 : ℝ) ≤ (Jof P k n : ℝ) := by rw [hJdef]; exact_mod_cast le_max_left _ _
  refine ⟨?_, hJ1⟩
  rw [div_le_iff₀ (by linarith)]
  by_cases h : 1 ≤ (n:ℝ) / m
  · have hfl : (n:ℝ)/m < ⌊(n:ℝ)/m⌋₊ + 1 := Nat.lt_floor_add_one _
    have hfl1 : (1:ℝ) ≤ ⌊(n:ℝ)/m⌋₊ := by exact_mod_cast (Nat.one_le_floor_iff _).mpr h
    have hJge : ((⌊(n:ℝ)/m⌋₊ : ℕ) : ℝ) ≤ Jof P k n := by
      rw [hJdef]; exact_mod_cast le_max_right _ _
    have : (n:ℝ) = (n/m) * m := by field_simp
    nlinarith
  · push Not at h
    rw [div_lt_one (by linarith)] at h
    nlinarith

theorem nu_le (P : LocParams) (hM : 1 ≤ P.M) (hL : 1 ≤ P.L) (N k n : ℕ) (hk : P.M < k)
    (hkM : k ≤ P.M ^ 2) (hn : 1 ≤ n) (hnN : n ≤ 2 * N) :
    nuOf P k n * 2 ^ (k - P.M) ≤
      2 ^ (P.M ^ 2) * 4 * (P.L : ℝ) ^ P.M * (2 * (N : ℝ)) ^ ((1 : ℝ) / (P.M : ℝ) ^ 5) := by
  obtain ⟨hJ, hJ1⟩ := Jof_bound P k n hn hL
  have hL1 : (1:ℝ) ≤ (P.L : ℝ) := by exact_mod_cast hL
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hnN' : (n:ℝ) ≤ 2 * N := by exact_mod_cast hnN
  have hM1 : (1:ℝ) ≤ P.M := by exact_mod_cast hM
  have hX1 : (1:ℝ) ≤ (2 * (N : ℝ)) ^ ((1 : ℝ) / (P.M : ℝ) ^ 5) :=
    Real.one_le_rpow (by linarith) (by positivity)
  have hmX : max (P.L : ℝ) ((n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ 5)) ≤
      (P.L : ℝ) * (2 * (N : ℝ)) ^ ((1 : ℝ) / (P.M : ℝ) ^ 5) := by
    apply max_le
    · nlinarith
    · calc (n:ℝ) ^ ((1:ℝ) / (k:ℝ)^5) ≤ (2 * (N:ℝ)) ^ ((1:ℝ) / (k:ℝ)^5) :=
            Real.rpow_le_rpow (by linarith) hnN' (by positivity)
        _ ≤ (2 * (N : ℝ)) ^ ((1 : ℝ) / (P.M : ℝ) ^ 5) := by
            apply Real.rpow_le_rpow_of_exponent_le (by linarith)
            apply one_div_le_one_div_of_le (by positivity)
            have : (P.M:ℝ) ≤ k := by exact_mod_cast hk.le
            gcongr
        _ ≤ _ := by nlinarith
  have hpow : (2:ℝ) ^ (k - P.M) ≤ 2 ^ (P.M ^ 2) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hLM : (P.L : ℝ) ^ (P.M - 1) * P.L = (P.L : ℝ) ^ P.M := pow_sub_one_mul (by omega) _
  have hnu : nuOf P k n ≤ 4 * (P.L : ℝ) ^ P.M * (2 * (N : ℝ)) ^ ((1 : ℝ) / (P.M : ℝ) ^ 5) := by
    unfold nuOf
    have e : 2 * (n : ℝ) * (P.L : ℝ) ^ (P.M - 1) / (Jof P k n : ℝ) =
        2 * (P.L : ℝ) ^ (P.M - 1) * ((n : ℝ) / (Jof P k n : ℝ)) := by ring
    rw [e, ← hLM]
    have h0 : (0:ℝ) ≤ (P.L : ℝ) ^ (P.M - 1) := by positivity
    calc 2 * (P.L : ℝ) ^ (P.M - 1) * ((n : ℝ) / (Jof P k n : ℝ))
        ≤ 2 * (P.L : ℝ) ^ (P.M - 1) * (2 * ((P.L : ℝ) * (2 * (N : ℝ)) ^ ((1 : ℝ) / (P.M : ℝ) ^ 5))) := by
          gcongr; exact hJ.trans (by linarith)
      _ = _ := by ring
  have hnu0 : 0 ≤ nuOf P k n := by unfold nuOf; positivity
  calc nuOf P k n * 2 ^ (k - P.M) ≤ (4 * (P.L : ℝ) ^ P.M * (2 * (N : ℝ)) ^ ((1 : ℝ) / (P.M : ℝ) ^ 5)) * 2 ^ (P.M ^ 2) :=
        mul_le_mul hnu hpow (by positivity) (by positivity)
    _ = _ := by ring

end OnlineColoringKYY.Supplement.Dev.T626.PartAC
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626
open Classical OnlineColoringKYY.Supplement
alias nu_le := OnlineColoringKYY.Supplement.Dev.T626.PartAC.nu_le

end OnlineColoringKYY.Supplement.Dev.T626
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartAC
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
/-! ### `holder` -/
theorem holder (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (xs : List ℕ) :
    (xs.map (fun x : ℕ => ((x : ℕ) : ℝ) ^ (1 - δ))).sum ≤
      (xs.length : ℝ) ^ δ * ((xs.sum : ℕ) : ℝ) ^ (1 - δ) := by
  rcases eq_or_lt_of_le hδ1 with h1 | h1
  · subst h1; simp
  rcases eq_or_lt_of_le hδ0 with h0 | h0
  · subst h0; simp
  have hsum : ∀ g : ℕ → ℝ, (xs.map g).sum = ∑ i : Fin xs.length, g (xs.get i) := by
    intro g; exact Eq.symm (Fin.sum_univ_fun_getElem xs g)
  have key := Real.inner_le_Lp_mul_Lq_of_nonneg (Finset.univ : Finset (Fin xs.length))
    (f := fun i => ((xs.get i : ℕ) : ℝ) ^ (1 - δ)) (g := fun _ => (1:ℝ))
    (p := 1 / (1 - δ)) (q := 1 / δ)
    (Real.holderConjugate_iff.mpr ⟨by rw [lt_div_iff₀ (by linarith)]; linarith, by
      simp⟩) (fun i _ => by positivity) (fun i _ => by positivity)
  rw [hsum]
  refine le_trans (by simpa using key) (le_of_eq ?_)
  have hs : ((xs.sum : ℕ) : ℝ) = ∑ i : Fin xs.length, ((xs.get i : ℕ) : ℝ) := by
    rw [← hsum (fun x => (x:ℝ))]; push_cast; simp
  rw [hs]
  simp only [List.get_eq_getElem] at *
  have e1 : ∀ i : Fin xs.length, (((xs[(i:ℕ)] : ℕ) : ℝ) ^ (1 - δ)) ^ (1 - δ)⁻¹ = ((xs[(i:ℕ)] : ℕ) : ℝ) := by
    intro i; rw [← Real.rpow_mul (by positivity), mul_inv_cancel₀ (by linarith)]; simp
  simp only [e1]; rw [mul_comm]

end OnlineColoringKYY.Supplement.Dev.T626.PartAC
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626
open Classical OnlineColoringKYY.Supplement
alias holder := OnlineColoringKYY.Supplement.Dev.T626.PartAC.holder

/-- The parameter `W` used for `N`. -/
noncomputable def Wof (ε : ℝ) (N : ℕ) : ℝ :=
  2 ^ (locM ε N ^ 2) * 4 * (locL ε N : ℝ) ^ (locM ε N) * (2 * (N : ℝ)) ^ ((1 : ℝ) / (locM ε N : ℝ) ^ 5)

end OnlineColoringKYY.Supplement.Dev.T626
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626.PartAS
open Classical OnlineColoringKYY.Supplement OnlineColoringKYY.Supplement.Dev.T626
/-! Asymptotics for Theorem 6.26: proof of `asymp` from the closed-form bounds of `ASY`. -/
/-- `x ≤ 2^{x+1}` for real `x ≥ 0`. -/
lemma le_two_rpow (x : ℝ) (hx : 0 ≤ x) : x ≤ (2 : ℝ) ^ (x + 1) := by
  set n := ⌈x⌉₊
  have h1 : x ≤ n := Nat.le_ceil x
  have h2 : (n : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
  have h3 : (n : ℝ) < (2 : ℝ) ^ (n : ℝ) := by
    rw [Real.rpow_natCast]; exact_mod_cast Nat.lt_two_pow_self
  have h4 : (2 : ℝ) ^ (n : ℝ) ≤ (2 : ℝ) ^ (x + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h2.le
  linarith

/-- Natural powers of two as real powers. -/
lemma two_pow_nat (n : ℕ) : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ (n : ℝ) := by
  rw [Real.rpow_natCast]; push_cast; rfl

/-- Pure asymptotic fact in `M`: `(M+1)^{9(M+1)} ≤ 2^{M^b}` for large `M`, when `b > 1`. -/
lemma pureM (b : ℝ) (hb : 1 < b) :
    ∃ M₁ : ℕ, ∀ M : ℕ, M₁ ≤ M → ((M : ℝ) + 1) ^ (9 * (M + 1)) ≤ (2 : ℝ) ^ ((M : ℝ) ^ b) := by
  set η : ℝ := (b - 1) / 2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  set C : ℝ := 18 * (2 : ℝ) ^ η / η with hC
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC0 : 0 ≤ C := by positivity
  refine ⟨max 1 ⌈(C / Real.log 2) ^ η⁻¹⌉₊, fun M hM => ?_⟩
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (le_max_left _ _).trans hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hMη : C / Real.log 2 ≤ (M : ℝ) ^ η := by
    have h1 : (C / Real.log 2) ^ η⁻¹ ≤ (M : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hM)
    have h2 := Real.rpow_le_rpow (by positivity) h1 hη0.le
    rwa [Real.rpow_inv_rpow (by positivity) hη0.ne'] at h2
  have hCM : C ≤ (M : ℝ) ^ η * Real.log 2 := by
    rwa [div_le_iff₀ hl2] at hMη
  have hpos1 : (0 : ℝ) < ((M : ℝ) + 1) ^ (9 * (M + 1)) := by positivity
  have hpos2 : (0 : ℝ) < (2 : ℝ) ^ ((M : ℝ) ^ b) := by positivity
  rw [← Real.log_le_log_iff hpos1 hpos2, Real.log_pow, Real.log_rpow (by norm_num)]
  -- log (M+1) ≤ 2^η M^η / η
  have hlog : Real.log ((M : ℝ) + 1) ≤ (2 : ℝ) ^ η * (M : ℝ) ^ η / η := by
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((M : ℝ) + 1) ^ η by positivity)
    rw [Real.log_rpow (by positivity)] at h1
    have h2 : ((M : ℝ) + 1) ^ η ≤ (2 * (M : ℝ)) ^ η :=
      Real.rpow_le_rpow (by positivity) (by linarith) hη0.le
    rw [Real.mul_rpow (by norm_num) hM0.le] at h2
    rw [le_div_iff₀ hη0]
    nlinarith
  have hlog0 : 0 ≤ Real.log ((M : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hb' : (M : ℝ) ^ b = (M : ℝ) * (M : ℝ) ^ η * (M : ℝ) ^ η := by
    rw [show b = 1 + η + η by rw [hη]; ring, Real.rpow_add hM0, Real.rpow_add hM0,
      Real.rpow_one]
  rw [hb']
  push_cast
  have hA : (9 * ((M : ℝ) + 1)) * Real.log ((M : ℝ) + 1) ≤
      (18 * (M : ℝ)) * ((2 : ℝ) ^ η * (M : ℝ) ^ η / η) :=
    mul_le_mul (by linarith) hlog hlog0 (by positivity)
  have hB : (18 * (M : ℝ)) * ((2 : ℝ) ^ η * (M : ℝ) ^ η / η) = C * ((M : ℝ) * (M : ℝ) ^ η) := by
    rw [hC]; ring
  have hD : C * ((M : ℝ) * (M : ℝ) ^ η) ≤ ((M : ℝ) ^ η * Real.log 2) * ((M : ℝ) * (M : ℝ) ^ η) :=
    mul_le_mul_of_nonneg_right hCM (by positivity)
  nlinarith

/-- `8(M+1) ≤ T` from `(M+1)^{8(M+1)} ≤ T`. -/
lemma eight_le_T (M : ℕ) (hM : 1 ≤ M) (T : ℝ) (hT : ((M : ℝ) + 1) ^ (8 * (M + 1)) ≤ T) :
    8 * ((M : ℝ) + 1) ≤ T := by
  have h1 : 8 * (M + 1) < 2 ^ (8 * (M + 1)) := Nat.lt_two_pow_self
  have h2 : 2 ^ (8 * (M + 1)) ≤ (M + 1) ^ (8 * (M + 1)) :=
    Nat.pow_le_pow_left (by omega) _
  have h3 : ((8 * (M + 1) : ℕ) : ℝ) ≤ (((M + 1) ^ (8 * (M + 1)) : ℕ) : ℝ) := by
    exact_mod_cast (h1.trans_le h2).le
  push_cast at h3
  linarith

/-- If `n ≤ T` then `2^n ≤ ⌊2^T⌋`. -/
lemma two_pow_le_floor (T : ℝ) (n : ℕ) (hn : (n : ℝ) ≤ T) : 2 ^ n ≤ ⌊(2 : ℝ) ^ T⌋₊ := by
  apply Nat.le_floor
  rw [two_pow_nat]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hn

/-- `W ≤ 2^{M² + 2 + TM + (ℓ+1)/M⁵}`. -/
lemma W_le (M L N : ℕ) (T ℓ : ℝ) (hN : (N : ℝ) = (2 : ℝ) ^ ℓ)
    (hL : (L : ℝ) ≤ (2 : ℝ) ^ T) :
    2 ^ (M ^ 2) * 4 * (L : ℝ) ^ M * (2 * (N : ℝ)) ^ ((1 : ℝ) / (M : ℝ) ^ 5) ≤
      (2 : ℝ) ^ ((M : ℝ) ^ 2 + 2 + T * M + (ℓ + 1) * (1 / (M : ℝ) ^ 5)) := by
  have e1 : (2 : ℝ) ^ (M ^ 2) = (2 : ℝ) ^ ((M : ℝ) ^ 2) := by
    rw [← Real.rpow_natCast]; push_cast; rfl
  have e2 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
  have e3 : (L : ℝ) ^ M ≤ (2 : ℝ) ^ (T * M) := by
    calc (L : ℝ) ^ M ≤ ((2 : ℝ) ^ T) ^ M := pow_le_pow_left₀ (by positivity) hL M
      _ = (2 : ℝ) ^ (T * M) := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have e4 : (2 * (N : ℝ)) ^ ((1 : ℝ) / (M : ℝ) ^ 5) = (2 : ℝ) ^ ((ℓ + 1) * (1 / (M : ℝ) ^ 5)) := by
    rw [hN, Real.rpow_mul (by norm_num), Real.rpow_add (by norm_num), Real.rpow_one, mul_comm]
  rw [e1, e2, e4, Real.rpow_add (by norm_num), Real.rpow_add (by norm_num),
    Real.rpow_add (by norm_num)]
  have : (0 : ℝ) ≤ (2 : ℝ) ^ ((M : ℝ) ^ 2) * (2 : ℝ) ^ (2 : ℝ) := by positivity
  have h5 : (0 : ℝ) ≤ (2 : ℝ) ^ ((ℓ + 1) * (1 / (M : ℝ) ^ 5)) := by positivity
  gcongr

/-- `(M : ℝ) ≤ 2^M` as a real power. -/
lemma nat_le_two_rpow (n : ℕ) : (n : ℝ) ≤ (2 : ℝ) ^ (n : ℝ) := by
  rw [← two_pow_nat]; exact_mod_cast Nat.lt_two_pow_self.le

/-- Polynomial inequality used for the exponent of `2K`. -/
lemma poly_le (M : ℕ) (hM : 16 ≤ M) : (M : ℝ) ^ 2 + 12 * M + 11 ≤ (M : ℝ) ^ 6 := by
  have h16 : (16 : ℝ) ≤ M := by exact_mod_cast hM
  have h4 : (16 : ℝ) ^ 4 ≤ (M : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) h16 4
  have h6 : (M : ℝ) ^ 6 = (M : ℝ) ^ 2 * (M : ℝ) ^ 4 := by ring
  have h2 : 16 * (M : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
  nlinarith

/-- The instance count: `|sizes| ≤ cL ≤ 2^{6TM⁹} = N^{6/M²}`. -/
lemma m_le (M L N : ℕ) (T ℓ : ℝ) (hM : 16 ≤ M) (hT8 : 8 * ((M : ℝ) + 1) ≤ T)
    (hℓ : ℓ = T * (M : ℝ) ^ 11) (hN : (N : ℝ) = (2 : ℝ) ^ ℓ) (hL1 : 1 ≤ L)
    (hLle : (L : ℝ) ≤ (2 : ℝ) ^ T) (W : ℝ)
    (hW : W = 2 ^ (M ^ 2) * 4 * (L : ℝ) ^ M * (2 * (N : ℝ)) ^ ((1 : ℝ) / (M : ℝ) ^ 5))
    (hW1 : 1 ≤ W) (m : ℝ) (hm : m ≤ cL M W L ℓ (M ^ 2)) :
    m ≤ (2 : ℝ) ^ (6 * T * (M : ℝ) ^ 9) := by
  have h16 : (16 : ℝ) ≤ M := by exact_mod_cast hM
  have hT1 : 1 ≤ T := by linarith
  have hM11 : (2 : ℝ) ≤ (M : ℝ) ^ 11 := by
    have : (16 : ℝ) ≤ (M : ℝ) ^ 11 := le_trans h16 (le_self_pow₀ (by linarith) (by norm_num))
    linarith
  have hℓ2 : 2 ≤ ℓ := by rw [hℓ]; nlinarith
  have hc := cL_le M (by omega) W L ℓ hW1 (by exact_mod_cast hL1) (by linarith) (M ^ 2) le_rfl
  have hWle : W ≤ (2 : ℝ) ^ ((M : ℝ) ^ 2 + 2 + T * M + (ℓ + 1) * (1 / (M : ℝ) ^ 5)) := by
    rw [hW]; exact W_le M L N T ℓ hN hLle
  have hL1' : (L : ℝ) + 1 ≤ (2 : ℝ) ^ (T + 1) := by
    have : (1 : ℝ) ≤ (2 : ℝ) ^ T := Real.one_le_rpow (by norm_num) (by linarith)
    rw [Real.rpow_add (by norm_num), Real.rpow_one]; linarith
  have hℓle : ℓ + 2 ≤ (2 : ℝ) ^ (T + 1 + (M : ℝ) * 11 + 1) := by
    have hA : T ≤ (2 : ℝ) ^ (T + 1) := le_two_rpow T (by linarith)
    have hB : (M : ℝ) ^ 11 ≤ (2 : ℝ) ^ ((M : ℝ) * 11) := by
      calc (M : ℝ) ^ 11 ≤ ((2 : ℝ) ^ (M : ℝ)) ^ 11 :=
            pow_le_pow_left₀ (by positivity) (nat_le_two_rpow M) 11
        _ = (2 : ℝ) ^ ((M : ℝ) * 11) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have hC : ℓ ≤ (2 : ℝ) ^ (T + 1) * (2 : ℝ) ^ ((M : ℝ) * 11) := by
      rw [hℓ]; exact mul_le_mul hA hB (by positivity) (by positivity)
    rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), Real.rpow_one]
    linarith
  have hK : 2 * (3 * W * ((L : ℝ) + 1) * (ℓ + 2)) ≤ (2 : ℝ) ^ (3 * T * (M : ℝ) ^ 6) := by
    calc 2 * (3 * W * ((L : ℝ) + 1) * (ℓ + 2)) = 6 * W * ((L : ℝ) + 1) * (ℓ + 2) := by ring
      _ ≤ (2 : ℝ) ^ (3 : ℝ) * (2 : ℝ) ^ ((M : ℝ) ^ 2 + 2 + T * M + (ℓ + 1) * (1 / (M : ℝ) ^ 5)) *
            (2 : ℝ) ^ (T + 1) * (2 : ℝ) ^ (T + 1 + (M : ℝ) * 11 + 1) := by
          have : (6 : ℝ) ≤ (2 : ℝ) ^ (3 : ℝ) := by norm_num
          gcongr
      _ = (2 : ℝ) ^ (3 + ((M : ℝ) ^ 2 + 2 + T * M + (ℓ + 1) * (1 / (M : ℝ) ^ 5)) + (T + 1) +
            (T + 1 + (M : ℝ) * 11 + 1)) := by
          rw [← Real.rpow_add two_pos, ← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
      _ ≤ (2 : ℝ) ^ (3 * T * (M : ℝ) ^ 6) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have hM5 : (0 : ℝ) < (M : ℝ) ^ 5 := by positivity
          have h1M5 : (1 : ℝ) ≤ (M : ℝ) ^ 5 := one_le_pow₀ (by linarith)
          have hdiv : (ℓ + 1) * (1 / (M : ℝ) ^ 5) ≤ T * (M : ℝ) ^ 6 + 1 := by
            rw [mul_one_div, div_le_iff₀ hM5, hℓ]
            have : T * (M : ℝ) ^ 11 = T * (M : ℝ) ^ 6 * (M : ℝ) ^ 5 := by ring
            nlinarith
          have hp := poly_le M hM
          have hTM2 : (M : ℝ) ^ 2 ≤ T * (M : ℝ) ^ 2 := by nlinarith
          have hTM : (M : ℝ) ≤ T * (M : ℝ) := by nlinarith
          have hTp : T * ((M : ℝ) ^ 2 + 12 * M + 11) ≤ T * (M : ℝ) ^ 6 :=
            mul_le_mul_of_nonneg_left hp (by linarith)
          nlinarith
  have hK0 : 0 ≤ 2 * (3 * W * ((L : ℝ) + 1) * (ℓ + 2)) := by
    have : (0 : ℝ) ≤ W := by linarith
    positivity
  calc m ≤ _ := hm
    _ ≤ _ := hc
    _ ≤ ((2 : ℝ) ^ (3 * T * (M : ℝ) ^ 6)) ^ (M * (M ^ 2 + M)) := pow_le_pow_left₀ hK0 hK _
    _ = (2 : ℝ) ^ (3 * T * (M : ℝ) ^ 6 * ((M : ℝ) * ((M : ℝ) ^ 2 + M))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; push_cast; ring_nf
    _ ≤ (2 : ℝ) ^ (6 * T * (M : ℝ) ^ 9) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have h89 : (M : ℝ) ^ 8 ≤ (M : ℝ) ^ 9 := pow_le_pow_right₀ (by linarith) (by norm_num)
        have hT0 : 0 ≤ T := by linarith
        have : 3 * T * (M : ℝ) ^ 6 * ((M : ℝ) * ((M : ℝ) ^ 2 + M)) =
            3 * T * ((M : ℝ) ^ 9 + (M : ℝ) ^ 8) := by ring
        rw [this]
        nlinarith

/-- The final count `(L/M)·nb + ext ≤ 3N/M`. -/
lemma final_ineq (M L N : ℕ) (T ℓ : ℝ) (hM : 16 ≤ M) (hT8 : 8 * ((M : ℝ) + 1) ≤ T)
    (hℓ : ℓ = T * (M : ℝ) ^ 11) (hN : (N : ℝ) = (2 : ℝ) ^ ℓ) (hL1 : 1 ≤ L)
    (hLle : (L : ℝ) ≤ (2 : ℝ) ^ T) (nb ext : ℕ) (sizes : List ℕ)
    (hm : (sizes.length : ℝ) ≤ (2 : ℝ) ^ (6 * T * (M : ℝ) ^ 9))
    (hnb : (nb : ℝ) ≤ (N : ℝ) / L +
      (sizes.map (fun x : ℕ => 8 * ((x : ℕ) : ℝ) ^ (1 - 1 / (M : ℝ) ^ 10))).sum)
    (hext : ext ≤ sizes.length) (hsum : sizes.sum ≤ N * (M ^ 2 / M + 1)) :
    (L : ℝ) / M * nb + ext ≤ 3 * (N : ℝ) / M := by
  have h16 : (16 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
  set δ : ℝ := 1 / (M : ℝ) ^ 10 with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_one (by positivity)]; exact one_le_pow₀ (by linarith)
  set S : ℝ := (sizes.map (fun x : ℕ => ((x : ℕ) : ℝ) ^ (1 - δ))).sum with hSdef
  have hS8 : (sizes.map (fun x : ℕ => 8 * ((x : ℕ) : ℝ) ^ (1 - δ))).sum = 8 * S := by
    rw [hSdef, List.sum_map_mul_left]
  rw [hS8] at hnb
  have hhold := holder δ hδ0 hδ1 sizes
  rw [← hSdef] at hhold
  have hmδ : (sizes.length : ℝ) ^ δ ≤ (2 : ℝ) ^ (6 * T / M) := by
    calc (sizes.length : ℝ) ^ δ ≤ ((2 : ℝ) ^ (6 * T * (M : ℝ) ^ 9)) ^ δ :=
          Real.rpow_le_rpow (by positivity) hm hδ0
      _ = (2 : ℝ) ^ (6 * T / M) := by
          rw [← Real.rpow_mul (by norm_num), hδ]; congr 1; field_simp
  have hMM : M ^ 2 / M = M := by
    rw [pow_two, Nat.mul_div_cancel _ (by omega)]
  rw [hMM] at hsum
  have hsum' : ((sizes.sum : ℕ) : ℝ) ≤ (2 : ℝ) ^ ℓ * ((M : ℝ) + 1) := by
    rw [← hN]; exact_mod_cast hsum
  have hSig : ((sizes.sum : ℕ) : ℝ) ^ (1 - δ) ≤ (2 : ℝ) ^ (ℓ - T * M) * ((M : ℝ) + 1) := by
    calc ((sizes.sum : ℕ) : ℝ) ^ (1 - δ) ≤ ((2 : ℝ) ^ ℓ * ((M : ℝ) + 1)) ^ (1 - δ) :=
          Real.rpow_le_rpow (by positivity) hsum' (by linarith)
      _ = ((2 : ℝ) ^ ℓ) ^ (1 - δ) * ((M : ℝ) + 1) ^ (1 - δ) :=
          Real.mul_rpow (by positivity) (by positivity)
      _ ≤ (2 : ℝ) ^ (ℓ - T * M) * ((M : ℝ) + 1) := by
          have e : ((2 : ℝ) ^ ℓ) ^ (1 - δ) = (2 : ℝ) ^ (ℓ - T * M) := by
            rw [← Real.rpow_mul (by norm_num)]; congr 1; rw [hδ, hℓ]; field_simp
          rw [e]
          gcongr
          calc ((M : ℝ) + 1) ^ (1 - δ) ≤ ((M : ℝ) + 1) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
            _ = (M : ℝ) + 1 := Real.rpow_one _
  have hS : S ≤ (2 : ℝ) ^ (6 * T / M) * ((2 : ℝ) ^ (ℓ - T * M) * ((M : ℝ) + 1)) :=
    hhold.trans (mul_le_mul hmδ hSig (by positivity) (by positivity))
  have h8M : 8 * ((M : ℝ) + 1) ≤ (2 : ℝ) ^ T := by
    have h := nat_le_two_rpow (8 * (M + 1))
    push_cast at h
    exact h.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast hT8))
  have hLS : (L : ℝ) * (8 * S) ≤ N := by
    have hS0 : 0 ≤ S := by
      rw [hSdef]; apply List.sum_nonneg; intro z hz
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hz; positivity
    calc (L : ℝ) * (8 * S) ≤ (2 : ℝ) ^ T *
          (8 * ((2 : ℝ) ^ (6 * T / M) * ((2 : ℝ) ^ (ℓ - T * M) * ((M : ℝ) + 1)))) := by
          gcongr
      _ = (8 * ((M : ℝ) + 1)) * (2 : ℝ) ^ (T + 6 * T / M + (ℓ - T * M)) := by
          rw [Real.rpow_add two_pos, Real.rpow_add two_pos]; ring
      _ ≤ (2 : ℝ) ^ T * (2 : ℝ) ^ (ℓ - T) := by
          gcongr
          · norm_num
          · have h6 : 6 * T / M ≤ T := by
              rw [div_le_iff₀ hMpos]; nlinarith
            have h3 : 3 * T ≤ T * M := by nlinarith
            linarith
      _ = N := by rw [← Real.rpow_add two_pos, hN]; ring_nf
  have hEM : (ext : ℝ) * M ≤ N := by
    have he : (ext : ℝ) ≤ (2 : ℝ) ^ (6 * T * (M : ℝ) ^ 9) :=
      le_trans (by exact_mod_cast hext) hm
    calc (ext : ℝ) * M ≤ (2 : ℝ) ^ (6 * T * (M : ℝ) ^ 9) * (2 : ℝ) ^ (M : ℝ) :=
          mul_le_mul he (nat_le_two_rpow M) (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (6 * T * (M : ℝ) ^ 9 + M) := by rw [Real.rpow_add two_pos]
      _ ≤ (2 : ℝ) ^ ℓ := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          rw [hℓ]
          have h19 : (M : ℝ) ≤ (M : ℝ) ^ 9 := le_self_pow₀ (by linarith) (by norm_num)
          have hM9 : (0 : ℝ) ≤ (M : ℝ) ^ 9 := by positivity
          have h11 : (M : ℝ) ^ 11 = (M : ℝ) ^ 9 * (M : ℝ) ^ 2 := by ring
          have hM2 : (256 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
          have hA : T * (M : ℝ) ^ 9 * 256 ≤ T * (M : ℝ) ^ 9 * (M : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left hM2 (mul_nonneg (by linarith : (0:ℝ) ≤ T) hM9)
          have hB : 1 * (M : ℝ) ^ 9 ≤ T * (M : ℝ) ^ 9 := mul_le_mul_of_nonneg_right hT1 hM9
          have e2 : T * ((M : ℝ) ^ 9 * (M : ℝ) ^ 2) = T * (M : ℝ) ^ 9 * (M : ℝ) ^ 2 := by ring
          rw [h11, e2]; linarith
      _ = N := hN.symm
  have hLnb : (L : ℝ) * nb ≤ N + L * (8 * S) := by
    have := mul_le_mul_of_nonneg_left hnb hLpos.le
    rw [mul_add, mul_div_cancel₀ _ hLpos.ne'] at this
    exact this
  have e : ((L : ℝ) / M * nb + ext) * M = L * nb + ext * M := by field_simp
  rw [le_div_iff₀ hMpos, e]
  linarith

/-- `f_k + 1 ≤ (M+1)^{M^{2M+3}} ≤ 2^{(M+1)^{8(M+1)}}`. -/
lemma fB_bound (M : ℕ) (hM : 2 ≤ M) (k : ℕ) (hk : k ≤ M ^ 2) :
    fB M k + 1 ≤ 2 ^ ((M + 1) ^ (8 * (M + 1))) := by
  refine (fB_le M hM k hk).trans ?_
  calc (M + 1) ^ (M ^ (2 * M + 3)) ≤ (2 ^ (M + 1)) ^ (M ^ (2 * M + 3)) :=
        Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
    _ = 2 ^ ((M + 1) * M ^ (2 * M + 3)) := by rw [← pow_mul]
    _ ≤ 2 ^ ((M + 1) ^ (8 * (M + 1))) := by
        apply Nat.pow_le_pow_right two_pos
        calc (M + 1) * M ^ (2 * M + 3) ≤ (M + 1) * (M + 1) ^ (2 * M + 3) :=
              Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
          _ = (M + 1) ^ (2 * M + 4) := by ring
          _ ≤ (M + 1) ^ (8 * (M + 1)) := Nat.pow_le_pow_right (by omega) (by omega)

/-- All asymptotics (Corollary 6.5's `n_{M+1} ≤ L`, Lemmas 6.21, 6.22, 6.24 and the final count). -/
theorem asymp (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 2) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      GoodP (locParams ε N) N (Wof ε N) (locL ε N) ∧
      ∀ (nb ext : ℕ) (sizes : List ℕ),
        (nb : ℝ) ≤ (N : ℝ) / locL ε N +
          (sizes.map (fun x : ℕ => 8 * ((x : ℕ) : ℝ) ^ (1 - 1 / (locM ε N : ℝ) ^ 10))).sum →
        ext ≤ sizes.length →
        (sizes.length : ℝ) ≤ cL (locM ε N) (Wof ε N) (locL ε N) (Real.logb 2 N) (locM ε N ^ 2) →
        sizes.sum ≤ N * (locM ε N ^ 2 / locM ε N + 1) →
        (∀ x ∈ sizes, 1 ≤ x ∧ x ≤ N) →
        (locL ε N : ℝ) / (locM ε N) * nb + ext ≤ 3 * (N : ℝ) / (locM ε N : ℝ) := by
  set a : ℝ := 1 - ε / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have ha1 : a < 1 := by rw [ha]; linarith
  set b : ℝ := a⁻¹ with hbdef
  have hb : 1 < b := (one_lt_inv₀ ha0).mpr ha1
  obtain ⟨M₁, hM₁⟩ := pureM b hb
  set M₀ : ℕ := max M₁ 16 with hM₀def
  set Y₀ : ℝ := max 1 ((M₀ : ℝ) ^ b) with hY₀def
  have hY1 : 1 ≤ Y₀ := le_max_left _ _
  refine ⟨⌈(2 : ℝ) ^ ((2 : ℝ) ^ Y₀)⌉₊, fun N hN => ?_⟩
  have hNr : (2 : ℝ) ^ ((2 : ℝ) ^ Y₀) ≤ N := Nat.ceil_le.mp hN
  have hNpos : 0 < (N : ℝ) := lt_of_lt_of_le (by positivity) hNr
  set ℓ : ℝ := Real.logb 2 N with hℓdef
  have hℓY : (2 : ℝ) ^ Y₀ ≤ ℓ := by
    have := Real.logb_le_logb_of_le (b := 2) one_lt_two (by positivity) hNr
    rwa [Real.logb_rpow two_pos (by norm_num)] at this
  have hℓpos : 0 < ℓ := lt_of_lt_of_le (by positivity) hℓY
  set y : ℝ := Real.logb 2 ℓ with hydef
  have hyY : Y₀ ≤ y := by
    have := Real.logb_le_logb_of_le (b := 2) one_lt_two (by positivity) hℓY
    rwa [Real.logb_rpow two_pos (by norm_num)] at this
  have hy0 : 0 ≤ y := by linarith
  have hMdef : locM ε N = ⌊y ^ a⌋₊ := rfl
  set M : ℕ := locM ε N with hMset
  have hMle : (M : ℝ) ≤ y ^ a := by rw [hMdef]; exact Nat.floor_le (by positivity)
  have hM₀ : M₀ ≤ M := by
    rw [hMdef]; apply Nat.le_floor
    calc (M₀ : ℝ) = ((M₀ : ℝ) ^ b) ^ a := (Real.rpow_inv_rpow (by positivity) ha0.ne').symm
      _ ≤ y ^ a := Real.rpow_le_rpow (by positivity) (le_trans (le_max_right _ _) hyY) ha0.le
  have hM16 : 16 ≤ M := le_trans (le_max_right _ _) hM₀
  have hMb : (M : ℝ) ^ b ≤ y := by
    calc (M : ℝ) ^ b ≤ (y ^ a) ^ b := Real.rpow_le_rpow (by positivity) hMle (by positivity)
      _ = y := Real.rpow_rpow_inv hy0 ha0.ne'
  have hK9 : ((M : ℝ) + 1) ^ (9 * (M + 1)) ≤ ℓ := by
    refine (hM₁ M (le_trans (le_max_left _ _) hM₀)).trans ?_
    calc (2 : ℝ) ^ ((M : ℝ) ^ b) ≤ (2 : ℝ) ^ y :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hMb
      _ = ℓ := Real.rpow_logb two_pos (by norm_num) hℓpos
  have h16 : (16 : ℝ) ≤ M := by exact_mod_cast hM16
  have hM11pos : (0 : ℝ) < (M : ℝ) ^ 11 := by positivity
  set T : ℝ := ℓ / (M : ℝ) ^ 11 with hTdef
  have hℓT : ℓ = T * (M : ℝ) ^ 11 := by rw [hTdef]; field_simp
  have hT : ((M : ℝ) + 1) ^ (8 * (M + 1)) ≤ T := by
    rw [hTdef, le_div_iff₀ hM11pos]
    refine le_trans ?_ hK9
    have e : ((M : ℝ) + 1) ^ (9 * (M + 1)) =
        ((M : ℝ) + 1) ^ (8 * (M + 1)) * ((M : ℝ) + 1) ^ (M + 1) := by
      rw [← pow_add]; congr 1; ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc (M : ℝ) ^ 11 ≤ ((M : ℝ) + 1) ^ 11 := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ ≤ ((M : ℝ) + 1) ^ (M + 1) := pow_le_pow_right₀ (by linarith) (by omega)
  have hN2 : (N : ℝ) = (2 : ℝ) ^ ℓ := (Real.rpow_logb two_pos (by norm_num) hNpos).symm
  have hLdef : locL ε N = ⌊(2 : ℝ) ^ T⌋₊ := by
    show ⌊(N : ℝ) ^ ((1 : ℝ) / ((locM ε N : ℕ) : ℝ) ^ 11)⌋₊ = _
    rw [← hMset, hN2, ← Real.rpow_mul (by norm_num), mul_one_div]
  set L : ℕ := locL ε N with hLset
  have hLle : (L : ℝ) ≤ (2 : ℝ) ^ T := by rw [hLdef]; exact Nat.floor_le (by positivity)
  have hL1 : 1 ≤ L := by
    rw [hLdef]; apply Nat.le_floor
    have hT0 : 0 ≤ T := le_trans (by positivity) hT
    simpa using Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) hT0
  have hT8 := eight_le_T M (by omega) T hT
  have hW : Wof ε N = 2 ^ (M ^ 2) * 4 * (L : ℝ) ^ M *
      (2 * (N : ℝ)) ^ ((1 : ℝ) / (M : ℝ) ^ 5) := rfl
  have hW1 : 1 ≤ Wof ε N := by
    rw [hW]
    have h1 : (1 : ℝ) ≤ 2 ^ (M ^ 2) := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ (L : ℝ) ^ M := one_le_pow₀ (by exact_mod_cast hL1)
    have h3 : (1 : ℝ) ≤ (2 * (N : ℝ)) ^ ((1 : ℝ) / (M : ℝ) ^ 5) := by
      have hN0 : 0 < N := by exact_mod_cast hNpos
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN0
      exact Real.one_le_rpow (by linarith) (by positivity)
    have h4 : (1 : ℝ) ≤ 2 ^ (M ^ 2) * 4 := by nlinarith
    have h5 : (1 : ℝ) ≤ 2 ^ (M ^ 2) * 4 * (L : ℝ) ^ M := by nlinarith
    nlinarith
  refine ⟨⟨by show 2 ≤ M; omega, hL1, ?_, hW1, by exact_mod_cast hL1, ?_, ?_⟩, ?_⟩
  · show nSeq M (M + 1) ≤ L
    refine (nSeq_le M (by omega)).trans ?_
    rw [hLdef]
    apply two_pow_le_floor
    push_cast; exact hT
  · intro k hk
    show (fB M k : ℝ) ≤ (L : ℝ)
    have h := fB_bound M (by omega) k hk
    have h2 : 2 ^ ((M + 1) ^ (8 * (M + 1))) ≤ L := by
      rw [hLdef]; apply two_pow_le_floor; push_cast; exact hT
    exact_mod_cast (by omega : fB M k ≤ L)
  · intro k n hk hkM hn hnN
    exact nu_le (locParams ε N) (by show 1 ≤ M; omega) (by show 1 ≤ L; exact hL1) N k n hk hkM
      hn hnN
  · intro nb ext sizes hnb hext hm hsum _
    have hm' := m_le M L N T ℓ hM16 hT8 hℓT hN2 hL1 hLle (Wof ε N) hW hW1 _ hm
    exact final_ineq M L N T ℓ hM16 hT8 hℓT hN2 hL1 hLle nb ext sizes hm' hnb hext hsum

end OnlineColoringKYY.Supplement.Dev.T626.PartAS
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement.Dev.T626
open Classical OnlineColoringKYY.Supplement
alias asymp := OnlineColoringKYY.Supplement.Dev.T626.PartAS.asymp

end OnlineColoringKYY.Supplement.Dev.T626
end

section
set_option autoImplicit false
namespace OnlineColoringKYY.Supplement
open OnlineColoringKYY.Supplement.Dev.T626 in
theorem chk_theorem_6_26 (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 2) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : ℕ, n ≤ N → ∀ (G : SimpleGraph (Fin n)),
      ∀ R : Resolver, R.Valid →
        ((locNumColors ε N R G : ℕ) : ℝ) ≤ 3 * (N : ℝ) / ((locM ε N : ℕ) : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := asymp ε hε hε2
  refine ⟨N₀, fun N hN n hn G R hR => ?_⟩
  obtain ⟨hgood, hfin⟩ := hN₀ N hN
  set Adj : ℕ → ℕ → Prop := fun a b => ∃ (ha : a < n) (hb : b < n), G.Adj ⟨a, ha⟩ ⟨b, hb⟩
  have hsymm : ∀ a b, Adj a b → Adj b a := by
    rintro a b ⟨ha, hb, h⟩; exact ⟨hb, ha, h.symm⟩
  obtain ⟨ins, hsort, hlen, hlive, hrun⟩ := locRun_eq ε N R G
  have hS : Std (locParams ε N) R Adj N (Wof ε N) (locL ε N) := ⟨hgood, hR, hsymm⟩
  have hin : InOK (locParams ε N) N (Wof ε N) ins (.loc (locM ε N ^ 2)) :=
    ⟨hsort, hlen.trans hn, le_rfl⟩
  obtain ⟨nb, ext, sizes, h1, h2, h3, -, h4, h5, h6, -⟩ :=
    holds_all (locParams ε N) R Adj N (Wof ε N) (locL ε N) hS (.loc (locM ε N ^ 2)) [] ins hin hlive
  have hL : ((ins.length : ℕ) : ℝ) / (locL ε N : ℝ) ≤ (N : ℝ) / locL ε N :=
    div_le_div_of_nonneg_right (by exact_mod_cast hlen.trans hn) (by positivity)
  have h2' : (nb : ℝ) ≤ (N : ℝ) / locL ε N +
      (sizes.map (fun x : ℕ => 8 * ((x : ℕ) : ℝ) ^ (1 - 1 / (locM ε N : ℝ) ^ 10))).sum := by
    have := h2; simp only [ownBins, add_zero, locParams] at this
    linarith
  have h3' : ext ≤ sizes.length := by simpa [ownExt] using h3
  have h5' : sizes.sum ≤ N * (locM ε N ^ 2 / locM ε N + 1) :=
    h5.trans (Nat.mul_le_mul_right _ (hlen.trans hn))
  have hfinal := hfin nb ext sizes h2' h3' (by simpa [cntOf, locParams] using h4) h5' h6
  unfold locNumColors
  rw [hrun]
  refine le_trans ?_ hfinal
  simpa [locParams] using h1

end OnlineColoringKYY.Supplement
end

theorem solution : type_of% @OnlineColoringKYY.Supplement.chk_theorem_6_26 := @OnlineColoringKYY.Supplement.chk_theorem_6_26
