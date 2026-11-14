-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.iid_continuous_rank_uniform
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:20:10.129711+00:00
-- url     : https://prove2.me/submissions/f0fc52a7-f352-47bb-84bf-3bd8f2a8e6dc

import Mathlib
noncomputable section
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function

private def rankBelow {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j => x j < x i)).card

private theorem rankBelow_lt {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : rankBelow x i < n := by
  unfold rankBelow
  have h : Finset.univ.filter (fun j => x j < x i) ⊂ (Finset.univ : Finset (Fin n)) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro he
    have hi : i ∈ Finset.univ.filter (fun j => x j < x i) := by rw [he]; simp
    simp at hi
  simpa using Finset.card_lt_card h

private theorem rankBelow_strict {n : ℕ} (x : Fin n → ℝ) (i j : Fin n) (h : x i < x j) :
    rankBelow x i < rankBelow x j := by
  unfold rankBelow
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro k hk
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hk ⊢
    exact lt_trans hk h
  · intro he
    have hi : i ∈ Finset.univ.filter (fun k => x k < x j) := by simp [h]
    rw [← he] at hi
    simp at hi

private theorem rankBelow_bijection {n : ℕ} (x : Fin n → ℝ)
    (hinj : Function.Injective x) : Function.Bijective (fun i : Fin n => (⟨rankBelow x i, rankBelow_lt x i⟩ : Fin n)) := by
  have h : Function.Injective (fun i : Fin n => (⟨rankBelow x i, rankBelow_lt x i⟩ : Fin n)) := by
   intro i j hij
   have he : rankBelow x i = rankBelow x j := congrArg Fin.val hij
   by_contra hn
   have hne : x i ≠ x j := fun h => hn (hinj h)
   rcases lt_or_gt_of_ne hne with h | h
   · exact (ne_of_lt (rankBelow_strict x i j h)) he
   · exact (ne_of_gt (rankBelow_strict x j i h)) he
  exact ⟨h,(Finite.injective_iff_surjective).mp h⟩

private theorem rankBelow_perm {n : ℕ} (x : Fin n → ℝ) (e : Fin n ≃ Fin n) (i : Fin n) :
    rankBelow (fun j => x (e.symm j)) i = rankBelow x (e.symm i) := by
  unfold rankBelow
  apply Finset.card_bij (fun j _ => e.symm j)
  · intro j hj
    simpa using hj
  · intro a ha b hb hab
    exact e.symm.injective hab
  · intro b hb
    refine ⟨e b, ?_, by simp⟩
    simpa using hb

private theorem rankBelow_measurable {n : ℕ} (i : Fin n) : Measurable (fun x : Fin n → ℝ => rankBelow x i) := by
  have he : (fun x : Fin n → ℝ => rankBelow x i) =
      fun x => ∑ j : Fin n, if x j < x i then (1 : ℕ) else 0 := by
    funext x
    exact Finset.card_filter _ _
  rw [he]
  apply Finset.measurable_sum
  intro j hj
  exact Measurable.ite (measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i)) measurable_const measurable_const

/-- Every specified coordinate has a uniform rank in a finite iid continuous sample. -/
theorem solution (n : ℕ) (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀]
    (htie : ∀ a b : Fin n, a ≠ b →
      Measure.pi (fun _ : Fin n => μ₀) {x | x a = x b} = 0)
    (i k : Fin n) :
    (Measure.pi (fun _ : Fin n => μ₀) {x | (Finset.univ.filter (fun j : Fin n => x j < x i)).card = k.val}).toReal = 1 / n := by
  classical
  change (Measure.pi (fun _ : Fin n => μ₀) {x | rankBelow x i = k.val}).toReal = 1 / n
  let μ : Measure (Fin n → ℝ) := Measure.pi (fun _ => μ₀)
  haveI : IsProbabilityMeasure μ := by unfold μ; infer_instance
  have hinjset : MeasurableSet {x : Fin n → ℝ | Function.Injective x} := by
    simp only [Function.Injective, setOf_forall]
    apply MeasurableSet.iInter; intro a
    apply MeasurableSet.iInter; intro b
    by_cases hab : a = b
    · simp [hab]
    · have he : {x : Fin n → ℝ | x a = x b → a = b} = {x | x a ≠ x b} := by ext x; simp [hab]
      rw [he]
      exact (measurableSet_eq_fun (measurable_pi_apply a) (measurable_pi_apply b)).compl
  let event : Fin n → Set (Fin n → ℝ) := fun j => {x | rankBelow x j = k.val ∧ Function.Injective x}
  have hm (j : Fin n) : MeasurableSet (event j) := (measurableSet_eq.preimage (rankBelow_measurable j)).inter hinjset
  have hae : ∀ᵐ x ∂μ, Function.Injective x := by
    apply ae_all_iff.mpr; intro a
    apply ae_all_iff.mpr; intro b
    by_cases hab : a = b
    · simp [hab]
    · have hh : ∀ᵐ x ∂μ, x a ≠ x b := by
        rw [ae_iff]
        have he : {x : Fin n → ℝ | ¬(x a ≠ x b)} = {x | x a = x b} := by ext x; simp
        rw [he]
        exact htie a b hab
      filter_upwards [hh] with x hx h
      exact (hx h).elim
  have hfull : (⋃ j : Fin n, event j) =ᵐ[μ] Set.univ := by
    filter_upwards [hae] with x hx
    apply propext
    change x ∈ (⋃ j : Fin n, event j) ↔ x ∈ Set.univ
    simp only [Set.mem_univ, iff_true, Set.mem_iUnion]
    obtain ⟨j,hj⟩ := (rankBelow_bijection x hx).2 k
    exact ⟨j, congrArg Fin.val hj, hx⟩
  have hdis : Pairwise (Disjoint on event) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    intro x ha hb
    have hab' : rankBelow x a = rankBelow x b := ha.1.trans hb.1.symm
    have hne : x a ≠ x b := fun h => hab (ha.2 h)
    rcases lt_or_gt_of_ne hne with h | h
    · exact (ne_of_lt (rankBelow_strict x a b h)) hab'
    · exact (ne_of_gt (rankBelow_strict x b a h)) hab'
  have hsum : (∑ j : Fin n, μ.real (event j)) = 1 := by
    have h := measureReal_iUnion_fintype (μ := μ) hdis hm
    have hall : μ.real (⋃ j : Fin n, event j) = 1 := by
      unfold Measure.real
      rw [measure_congr hfull, measure_univ, ENNReal.toReal_one]
    linarith
  have hequal (a b : Fin n) : μ.real (event a) = μ.real (event b) := by
    let e : Fin n ≃ Fin n := Equiv.swap a b
    have hmp := measurePreserving_piCongrLeft (fun _ : Fin n => μ₀) e
    have hp := hmp.measure_preimage (hm b).nullMeasurableSet
    have he : (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) e) ⁻¹' event b = event a := by
      ext x
      simp only [mem_preimage, event, mem_setOf_eq, MeasurableEquiv.coe_piCongrLeft,
        Equiv.piCongrLeft_apply,eq_rec_constant]
      have hefun : (Equiv.piCongrLeft (fun _ : Fin n => ℝ) e) x = (fun j => x (e.symm j)) := by
        funext j
        simp [Equiv.piCongrLeft_apply]
      rw [hefun]
      have hs : e.symm b = a := by simp [e]
      rw [rankBelow_perm, hs]
      constructor
      · rintro ⟨hr,hi⟩
        refine ⟨hr, ?_⟩
        intro u v huv
        apply e.injective
        apply hi
        simpa using huv
      · rintro ⟨hr,hi⟩
        refine ⟨hr, ?_⟩
        intro u v huv
        exact e.symm.injective (hi huv)
    rw [he] at hp
    exact congrArg ENNReal.toReal hp
  have heqsum : (∑ j : Fin n, μ.real (event j)) = n * μ.real (event i) := by
    calc
      _ = ∑ _j : Fin n, μ.real (event i) := by
        apply Finset.sum_congr rfl
        intro j _
        exact hequal j i
      _ = n * μ.real (event i) := by simp
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  have hevent : μ.real (event i) = μ.real {x | rankBelow x i = k.val} := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hae] with x hx
    change (rankBelow x i = k.val ∧ Function.Injective x) = (rankBelow x i = k.val)
    simp [hx]
  rw [heqsum, hevent] at hsum
  change μ.real {x | rankBelow x i = k.val} = 1 / n
  field_simp
  linarith

