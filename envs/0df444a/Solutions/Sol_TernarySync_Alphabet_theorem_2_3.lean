-- Prove2me | solution 1 for TernarySync.Alphabet.theorem_2_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:25:13.233874+00:00
-- url     : https://prove2.me/submissions/5cd4c78e-27ee-4136-92ab-0c8521f92f5c

import Mathlib

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace TernarySync.Dev.LLL

variable {Ω : Type*} [MeasurableSpace Ω] {V : Type*} [Fintype V] [DecidableEq V]
  {β : V → Type*} [∀ v, MeasurableSpace (β v)] {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false in
lemma indep_inter (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ∀ v, Ω → β v) (hXm : ∀ v, Measurable (X v)) (hind : iIndepFun X μ)
    (E : ι → Set Ω) (vbl : ι → Finset V)
    (hdet : ∀ i, MeasurableSet[⨆ v ∈ vbl i, MeasurableSpace.comap (X v) inferInstance] (E i))
    (i : ι) (S : Finset ι) (hS : ∀ j ∈ S, Disjoint (vbl j) (vbl i)) :
    μ.real (E i ∩ ⋂ j ∈ S, (E j)ᶜ) = μ.real (E i) * μ.real (⋂ j ∈ S, (E j)ᶜ) := by
  have hI : iIndep (fun v => MeasurableSpace.comap (X v) inferInstance) μ := hind.iIndep
  have hle : ∀ v, MeasurableSpace.comap (X v) (inferInstance : MeasurableSpace (β v)) ≤
      (inferInstance : MeasurableSpace Ω) := fun v => (hXm v).comap_le
  have hdis : Disjoint ((vbl i : Finset V) : Set V) ((S.biUnion vbl : Finset V) : Set V) := by
    rw [Finset.disjoint_coe, Finset.disjoint_left]
    intro v hv hv'
    obtain ⟨j, hj, hvj⟩ := Finset.mem_biUnion.1 hv'
    exact Finset.disjoint_left.1 (hS j hj) hvj hv
  have h := indep_iSup_of_disjoint hle hI hdis
  rw [Indep_iff] at h
  have hA : MeasurableSet[⨆ v ∈ (S.biUnion vbl : Finset V),
      MeasurableSpace.comap (X v) inferInstance] (⋂ j ∈ S, (E j)ᶜ) := by
    refine @Finset.measurableSet_biInter Ω ι
      (⨆ v ∈ (S.biUnion vbl : Finset V), MeasurableSpace.comap (X v) inferInstance)
      (fun j => (E j)ᶜ) S (fun j hj => ?_)
    refine MeasurableSet.compl ?_
    have hle2 : (⨆ v ∈ vbl j, MeasurableSpace.comap (X v) (inferInstance : MeasurableSpace (β v)))
        ≤ ⨆ v ∈ (S.biUnion vbl : Finset V), MeasurableSpace.comap (X v) inferInstance := by
      refine iSup₂_le (fun v hv => ?_)
      exact le_iSup₂_of_le v (Finset.mem_biUnion.2 ⟨j, hj, hv⟩) le_rfl
    exact hle2 _ (hdet j)
  have := h (E i) _ (by simpa using hdet i) hA
  simp only [Measure.real]
  rw [this, ENNReal.toReal_mul]


section Abstract

set_option linter.unusedSectionVars false

variable {ι' : Type*} [DecidableEq ι'] {Ω' : Type*} [MeasurableSpace Ω']

/-- the intersection of complements -/
def A (E : ι' → Set Ω') (S : Finset ι') : Set Ω' := ⋂ j ∈ S, (E j)ᶜ

lemma A_insert (E : ι' → Set Ω') (S : Finset ι') (a : ι') :
    A E (insert a S) = A E S ∩ (E a)ᶜ := by
  ext ω; simp [A, and_comm]

lemma A_union (E : ι' → Set Ω') (S T : Finset ι') :
    A E (S ∪ T) = A E S ∩ A E T := by
  ext ω; simp only [A, Set.mem_iInter, Set.mem_inter_iff, Finset.mem_union]
  constructor
  · intro h; exact ⟨fun j hj => h j (Or.inl hj), fun j hj => h j (Or.inr hj)⟩
  · rintro ⟨h1, h2⟩ j (hj | hj)
    · exact h1 j hj
    · exact h2 j hj

lemma A_anti (E : ι' → Set Ω') {S T : Finset ι'} (h : S ⊆ T) : A E T ⊆ A E S := by
  intro ω hω
  simp only [A, Set.mem_iInter] at hω ⊢
  exact fun j hj => hω j (h hj)

lemma step (μ : Measure Ω') [IsProbabilityMeasure μ] (E : ι' → Set Ω')
    (hE : ∀ i, MeasurableSet (E i)) (x : ι' → ℝ) (hx : ∀ i, 0 < x i ∧ x i < 1)
    (S : Finset ι') (a : ι') (hcl : μ.real (E a ∩ A E S) ≤ x a * μ.real (A E S)) :
    (1 - x a) * μ.real (A E S) ≤ μ.real (A E (insert a S)) := by
  rw [A_insert]
  have h := measureReal_inter_add_sdiff (μ := μ) (s := A E S) (hE a)
  have h2 : A E S ∩ (E a)ᶜ = A E S \ E a := by rw [Set.sdiff_eq]
  rw [h2]
  rw [Set.inter_comm] at hcl
  nlinarith

lemma main (μ : Measure Ω') [IsProbabilityMeasure μ] (E : ι' → Set Ω')
    (hE : ∀ i, MeasurableSet (E i)) (x : ι' → ℝ) (hx : ∀ i, 0 < x i ∧ x i < 1)
    (G : ι' → Finset ι')
    (hindep : ∀ i (S : Finset ι'), (∀ j ∈ S, j ∉ G i ∧ j ≠ i) →
      μ.real (E i ∩ A E S) = μ.real (E i) * μ.real (A E S))
    (h5 : ∀ i, μ.real (E i) ≤ x i * ∏ j ∈ G i, (1 - x j)) (S : Finset ι') :
    ∏ j ∈ S, (1 - x j) ≤ μ.real (A E S) := by
  have claim : ∀ n : ℕ, ∀ S : Finset ι', S.card = n → ∀ i ∉ S,
      μ.real (E i ∩ A E S) ≤ x i * μ.real (A E S) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro S hn i hi
    set S1 := S.filter (fun j => j ∈ G i) with hS1
    set S2 := S.filter (fun j => j ∉ G i) with hS2
    have hSeq : S = S2 ∪ S1 := by
      ext y; simp only [hS1, hS2, Finset.mem_union, Finset.mem_filter]; tauto
    have chain : ∀ T : Finset ι', T ⊆ S1 →
        (∏ j ∈ T, (1 - x j)) * μ.real (A E S2) ≤ μ.real (A E (S2 ∪ T)) := by
      intro T
      induction T using Finset.induction_on with
      | empty => intro _; simp
      | insert a T ha ihT =>
        intro hT
        have hTS : T ⊆ S1 := fun y hy => hT (Finset.mem_insert_of_mem hy)
        have haS1 : a ∈ S1 := hT (Finset.mem_insert_self a T)
        have haS : a ∈ S := (Finset.mem_filter.1 haS1).1
        have haG : a ∈ G i := (Finset.mem_filter.1 haS1).2
        have haS2 : a ∉ S2 := fun h => (Finset.mem_filter.1 h).2 haG
        have hsub : S2 ∪ T ⊆ S := by
          intro y hy
          rcases Finset.mem_union.1 hy with h | h
          · exact (Finset.mem_filter.1 h).1
          · exact (Finset.mem_filter.1 (hTS h)).1
        have hnot : a ∉ S2 ∪ T := by
          intro h; rcases Finset.mem_union.1 h with h | h
          · exact haS2 h
          · exact ha h
        have hlt : (S2 ∪ T).card < n := by
          rw [← hn]
          exact Finset.card_lt_card ⟨hsub, fun h => hnot (h haS)⟩
        have hcl := ih _ hlt (S2 ∪ T) rfl a hnot
        have hst := step μ E hE x hx (S2 ∪ T) a hcl
        have hnn : 0 ≤ ∏ j ∈ T, (1 - x j) :=
          Finset.prod_nonneg (fun j _ => by linarith [(hx j).2])
        rw [Finset.prod_insert ha, Finset.union_insert]
        have h1 := (hx a).2
        nlinarith [ihT hTS, mul_le_mul_of_nonneg_left (ihT hTS) (by linarith : 0 ≤ 1 - x a)]
    have hA : A E S = A E S2 ∩ A E S1 := by rw [hSeq, A_union]
    have hsub1 : μ.real (E i ∩ A E S) ≤ μ.real (E i ∩ A E S2) := by
      apply measureReal_mono
      · exact Set.inter_subset_inter_right _ (A_anti E (by rw [hSeq]; exact Finset.subset_union_left))
      · exact measure_ne_top _ _
    have hind := hindep i S2 (fun j hj => by
      have := Finset.mem_filter.1 hj
      exact ⟨this.2, fun h => hi (h ▸ this.1)⟩)
    have hG : ∏ j ∈ G i, (1 - x j) ≤ ∏ j ∈ S1, (1 - x j) := by
      have hsb : S1 ⊆ G i := fun y hy => (Finset.mem_filter.1 hy).2
      rw [← Finset.prod_sdiff hsb]
      have h1 : ∏ j ∈ G i \ S1, (1 - x j) ≤ 1 :=
        Finset.prod_le_one (fun j _ => by linarith [(hx j).2]) (fun j _ => by linarith [(hx j).1])
      have h2 : 0 ≤ ∏ j ∈ S1, (1 - x j) :=
        Finset.prod_nonneg (fun j _ => by linarith [(hx j).2])
      nlinarith
    have hch := chain S1 le_rfl
    have hS2nn : 0 ≤ μ.real (A E S2) := measureReal_nonneg
    have hxi := (hx i).1
    have hAS : A E (S2 ∪ S1) = A E S := by rw [← hSeq]
    rw [hAS] at hch
    calc μ.real (E i ∩ A E S) ≤ μ.real (E i ∩ A E S2) := hsub1
      _ = μ.real (E i) * μ.real (A E S2) := hind
      _ ≤ (x i * ∏ j ∈ G i, (1 - x j)) * μ.real (A E S2) :=
          mul_le_mul_of_nonneg_right (h5 i) hS2nn
      _ ≤ (x i * ∏ j ∈ S1, (1 - x j)) * μ.real (A E S2) := by
          apply mul_le_mul_of_nonneg_right _ hS2nn
          exact mul_le_mul_of_nonneg_left hG hxi.le
      _ = x i * ((∏ j ∈ S1, (1 - x j)) * μ.real (A E S2)) := by ring
      _ ≤ x i * μ.real (A E S) := mul_le_mul_of_nonneg_left hch hxi.le
  induction S using Finset.induction_on with
  | empty => simp [A]
  | insert a S ha ih =>
    have := step μ E hE x hx S a (claim _ S rfl a ha)
    rw [Finset.prod_insert ha]
    have h1 := (hx a).2
    nlinarith [mul_le_mul_of_nonneg_left ih (by linarith : 0 ≤ 1 - x a)]

end Abstract

end TernarySync.Dev.LLL

namespace TernarySync.Alphabet
open MeasureTheory ProbabilityTheory
open TernarySync.Dev.LLL in
theorem chk_theorem_2_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {V : Type*} [Fintype V] [DecidableEq V] {β : V → Type*} [∀ v, MeasurableSpace (β v)]
    (X : ∀ v, Ω → β v) (hXm : ∀ v, Measurable (X v)) (hind : iIndepFun X μ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → Set Ω) (vbl : ι → Finset V)
    (hdet : ∀ i, MeasurableSet[⨆ v ∈ vbl i, MeasurableSpace.comap (X v) inferInstance] (E i))
    (x : ι → ℝ) (hx : ∀ i, 0 < x i ∧ x i < 1)
    (h5 : ∀ i, μ.real (E i) ≤
      x i * ∏ j ∈ Finset.univ.filter (fun j => j ≠ i ∧ (vbl j ∩ vbl i).Nonempty), (1 - x j)) :
    ∏ i, (1 - x i) ≤ μ.real (⋂ i, (E i)ᶜ) ∧ 0 < ∏ i, (1 - x i) := by
  have hEm : ∀ i, MeasurableSet (E i) := by
    intro i
    have hle : (⨆ v ∈ vbl i, MeasurableSpace.comap (X v) (inferInstance : MeasurableSpace (β v)))
        ≤ (inferInstance : MeasurableSpace Ω) :=
      iSup₂_le (fun v _ => (hXm v).comap_le)
    exact hle _ (hdet i)
  refine ⟨?_, Finset.prod_pos (fun i _ => by linarith [(hx i).2])⟩
  have hm := main μ E hEm x hx
    (fun i => Finset.univ.filter (fun j => j ≠ i ∧ (vbl j ∩ vbl i).Nonempty))
    (fun i S hS => by
      refine indep_inter μ X hXm hind E vbl hdet i S (fun j hj => ?_)
      obtain ⟨h1, h2⟩ := hS j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and] at h1
      exact Finset.disjoint_iff_inter_eq_empty.2 (Finset.not_nonempty_iff_eq_empty.1 (h1 h2)))
    h5 Finset.univ
  have : A E Finset.univ = ⋂ i, (E i)ᶜ := by simp [A]
  rw [this] at hm
  exact hm

end TernarySync.Alphabet
end

theorem solution : type_of% @TernarySync.Alphabet.chk_theorem_2_3 := @TernarySync.Alphabet.chk_theorem_2_3
