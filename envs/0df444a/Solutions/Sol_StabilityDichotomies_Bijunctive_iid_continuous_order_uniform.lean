-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.iid_continuous_order_uniform
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:21:14.237259+00:00
-- url     : https://prove2.me/submissions/1d8a0d39-b6f7-49f1-be56-0fa2d0c6b9fc

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

/-- Every strict ordering of a finite iid continuous sample is equally likely. -/
theorem solution (n : ℕ) (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀]
    (htie : ∀ a b : Fin n, a ≠ b →
      Measure.pi (fun _ : Fin n => μ₀) {x | x a = x b} = 0)
    (e : Equiv.Perm (Fin n)) :
    (Measure.pi (fun _ : Fin n => μ₀)
      {x | ∀ i, (Finset.univ.filter (fun j : Fin n => x j < x i)).card = (e i).val}).toReal = 1 / n.factorial := by
  classical
  change (Measure.pi (fun _ : Fin n => μ₀) {x | ∀ i, rankBelow x i = (e i).val}).toReal = 1 / n.factorial
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
  let event : Equiv.Perm (Fin n) → Set (Fin n → ℝ) := fun p => {x | (∀ i, rankBelow x i = (p i).val) ∧ Function.Injective x}
  have hm (p : Equiv.Perm (Fin n)) : MeasurableSet (event p) := by
    apply MeasurableSet.inter _ hinjset
    have he : {x : Fin n → ℝ | ∀ i, rankBelow x i = (p i).val} = ⋂ i : Fin n, {x | rankBelow x i = (p i).val} := by ext x; simp
    have hh : MeasurableSet {x : Fin n → ℝ | ∀ i, rankBelow x i = (p i).val} := by
      rw [he]
      exact MeasurableSet.iInter fun i => measurableSet_eq.preimage (rankBelow_measurable i)
    exact hh
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
  have hfull : (⋃ p : Equiv.Perm (Fin n), event p) =ᵐ[μ] Set.univ := by
    filter_upwards [hae] with x hx
    apply propext
    change x ∈ (⋃ p : Equiv.Perm (Fin n), event p) ↔ x ∈ Set.univ
    simp only [Set.mem_univ, iff_true, Set.mem_iUnion]
    let f : Fin n → Fin n := fun i => ⟨rankBelow x i, rankBelow_lt x i⟩
    let p := Equiv.ofBijective f (rankBelow_bijection x hx)
    exact ⟨p,fun _ => rfl,hx⟩
  have hdis : Pairwise (Disjoint on event) := by
    intro p q hpq
    apply Set.disjoint_left.mpr
    intro x hp hq
    apply hpq
    ext i
    exact (hp.1 i).symm.trans (hq.1 i)
  have hsum : (∑ p : Equiv.Perm (Fin n), μ.real (event p)) = 1 := by
    have h := measureReal_iUnion_fintype (μ := μ) hdis hm
    have hall : μ.real (⋃ p : Equiv.Perm (Fin n), event p) = 1 := by
      unfold Measure.real
      rw [measure_congr hfull, measure_univ, ENNReal.toReal_one]
    linarith
  have hequal (p q : Equiv.Perm (Fin n)) : μ.real (event p) = μ.real (event q) := by
    let t : Equiv.Perm (Fin n) := p.trans q.symm
    have hmp := measurePreserving_piCongrLeft (fun _ : Fin n => μ₀) t
    have hp := hmp.measure_preimage (hm q).nullMeasurableSet
    have he : (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) t) ⁻¹' event q = event p := by
      ext x
      simp only [mem_preimage, event, mem_setOf_eq, MeasurableEquiv.coe_piCongrLeft]
      have hefun : (Equiv.piCongrLeft (fun _ : Fin n => ℝ) t) x = (fun j => x (t.symm j)) := by
        funext j
        simp [Equiv.piCongrLeft_apply]
      rw [hefun]
      simp only [rankBelow_perm]
      constructor
      · rintro ⟨hr,hi⟩
        constructor
        · intro j
          have hj := hr (t j)
          simpa [t] using hj
        · intro u v huv
          apply t.injective
          apply hi
          simpa using huv
      · rintro ⟨hr,hi⟩
        constructor
        · intro j
          have hj := hr (t.symm j)
          simpa [t] using hj
        · intro u v huv
          exact t.symm.injective (hi huv)
    rw [he] at hp
    exact congrArg ENNReal.toReal hp
  have heqsum : (∑ p : Equiv.Perm (Fin n), μ.real (event p)) = n.factorial * μ.real (event e) := by
    calc
      _ = ∑ _p : Equiv.Perm (Fin n), μ.real (event e) := by
        apply Finset.sum_congr rfl
        intro p _
        exact hequal p e
      _ = n.factorial * μ.real (event e) := by simp [Fintype.card_perm]
  have hn : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hevent : μ.real (event e) = μ.real {x | ∀ i, rankBelow x i = (e i).val} := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hae] with x hx
    change ((∀ i, rankBelow x i = (e i).val) ∧ Function.Injective x) = (∀ i, rankBelow x i = (e i).val)
    simp [hx]
  rw [heqsum, hevent] at hsum
  change μ.real {x | ∀ i, rankBelow x i = (e i).val} = 1 / n.factorial
  field_simp
  linarith
