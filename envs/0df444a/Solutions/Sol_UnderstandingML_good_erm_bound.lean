-- Prove2me | solution 1 for UnderstandingML.good_erm_bound
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T20:24:31.958094+00:00
-- url     : https://prove2.me/submissions/a1b03e3d-dacc-42bb-898b-569ad2c4e1b5

import Definitions.Def_UnderstandingML_MulticlassLearnability

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

section GoodERMAux

variable {X : Type*}

lemma hSet_eq_some_iff (A : {A : Set X // A.Finite ∨ Aᶜ.Finite}) (x : X) (B) :
    hSet A x = some B ↔ x ∈ A.1 ∧ A = B := by
  unfold hSet
  split_ifs with h <;> simp [h]

lemma hSet_eq_none_iff (A : {A : Set X // A.Finite ∨ Aᶜ.Finite}) (x : X) :
    hSet A x = none ↔ x ∉ A.1 := by
  unfold hSet
  split_ifs with h <;> simp [h]

/-- On a consistent sample hitting `A`, any ERM returns `h_A`. -/
lemma erm_eq_of_hit (A : Learner (X × CofinLabel X) (X → CofinLabel X))
    (hA : IsERMLearner lossMulti (cofinClass X) A) (Aset : {A : Set X // A.Finite ∨ Aᶜ.Finite})
    (m : ℕ) (S : Fin m → X × CofinLabel X) (hS : ∀ i, (S i).2 = hSet Aset (S i).1)
    (i₀ : Fin m) (hi₀ : (S i₀).1 ∈ Aset.1) : A m S = hSet Aset := by
  obtain ⟨⟨A', hA'⟩, hle⟩ := hA m S
  have h0 : empRisk lossMulti S (hSet Aset) = 0 := by
    unfold empRisk lossMulti
    simp [hS]
  have hle' := hle _ ⟨Aset, rfl⟩
  rw [h0, ← hA'] at hle'
  have hpos : (0 : ℝ) < m := by
    have := i₀.pos; exact_mod_cast this
  have hsum : ∑ i, lossMulti (hSet A') (S i) ≤ 0 := by
    unfold empRisk at hle'
    rwa [div_le_iff₀ hpos, zero_mul] at hle'
  have hnn : ∀ i, 0 ≤ lossMulti (hSet A') (S i) := by
    intro i; unfold lossMulti; split_ifs <;> norm_num
  have hzero : ∀ i, lossMulti (hSet A') (S i) = 0 := by
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ hnn i)).1
      (le_antisymm hsum (Finset.sum_nonneg fun i _ ↦ hnn i)) i (Finset.mem_univ _)
    exact this
  have hi := hzero i₀
  unfold lossMulti at hi
  split_ifs at hi with hh
  · rw [hS i₀] at hh
    have hsome : hSet Aset (S i₀).1 = some Aset := by
      rw [hSet_eq_some_iff]; exact ⟨hi₀, rfl⟩
    rw [hsome, hSet_eq_some_iff] at hh
    rw [← hA', hh.2]
  · norm_num at hi

end GoodERMAux

end UnderstandingML

open UnderstandingML in
theorem solution {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X]
    (A : Learner (X × CofinLabel X) (X → CofinLabel X)) (hA : IsGoodERM A) (D : Measure X)
    [IsProbabilityMeasure D] (Aset : {A : Set X // A.Finite ∨ Aᶜ.Finite}) (ε δ : ℝ) (hε : 0 < ε)
    (hδ : 0 < δ) (m : ℕ) (hm : 1 / ε * Real.log (1 / δ) ≤ m) :
    iidLaw (D.map (fun x ↦ (x, hSet Aset x))) m
      {S | ENNReal.ofReal ε < D {x | A m S x ≠ hSet Aset x}} ≤ ENNReal.ofReal δ := by
  set f : X → X × CofinLabel X := fun x ↦ (x, hSet Aset x) with hf_def
  have hf : Measurable f := measurable_of_countable f
  set ν := D.map f with hν
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hf.aemeasurable
  -- the inconsistent samples
  set G : Set (X × CofinLabel X) := {p | p.2 ≠ hSet Aset p.1} with hG
  have hGm : MeasurableSet G := by
    have : G = (⋃ x : X, ({x} : Set X) ×ˢ ({hSet Aset x} : Set (CofinLabel X)))ᶜ := by
      ext ⟨x, y⟩; simp [hG, eq_comm]
    rw [this]
    exact (MeasurableSet.iUnion fun x ↦
      (measurableSet_singleton x).prod (MeasurableSpace.measurableSet_top)).compl
  have hνG : ν G = 0 := by
    rw [hν, Measure.map_apply hf hGm]
    have : f ⁻¹' G = ∅ := by ext x; simp [hG, hf_def]
    rw [this, measure_empty]
  set Bad : Set (Fin m → X × CofinLabel X) := ⋃ i, Function.eval i ⁻¹' G with hBad
  have hBad0 : iidLaw ν m Bad = 0 := by
    rw [hBad]
    exact measure_iUnion_null fun i ↦ Measure.pi_eval_preimage_null _ hνG
  -- the samples avoiding `A`
  set E : Set (X × CofinLabel X) := Prod.fst ⁻¹' Aset.1ᶜ with hE
  set Out : Set (Fin m → X × CofinLabel X) := Set.univ.pi (fun _ ↦ E) with hOut
  have key : {S : Fin m → X × CofinLabel X | ENNReal.ofReal ε < D {x | A m S x ≠ hSet Aset x}} ⊆
      Bad ∪ (Out ∩ {_S | ENNReal.ofReal ε < D Aset.1}) := by
    intro S hS
    simp only [Set.mem_setOf_eq] at hS
    by_cases hcons : ∀ i, (S i).2 = hSet Aset (S i).1
    · right
      by_cases hhit : ∃ i, (S i).1 ∈ Aset.1
      · obtain ⟨i₀, hi₀⟩ := hhit
        rw [erm_eq_of_hit A hA.1 Aset m S hcons i₀ hi₀] at hS
        simp at hS
      · push_neg at hhit
        have hnone : ∀ i, (S i).2 = none := fun i ↦ by
          rw [hcons i, hSet_eq_none_iff]; exact hhit i
        rw [hA.2 m S hnone] at hS
        have hset : {x | hSet ⟨∅, Or.inl Set.finite_empty⟩ x ≠ hSet Aset x} = Aset.1 := by
          ext x
          have h1 : hSet (⟨∅, Or.inl Set.finite_empty⟩ : {A : Set X // A.Finite ∨ Aᶜ.Finite}) x
              = none := by rw [hSet_eq_none_iff]; simp
          rw [Set.mem_setOf_eq, h1, ne_comm, Ne, hSet_eq_none_iff, not_not]
        rw [hset] at hS
        refine ⟨?_, hS⟩
        simp only [hOut, Set.mem_pi, Set.mem_univ, true_implies, hE, Set.mem_preimage,
          Set.mem_compl_iff]
        exact hhit
    · left
      push_neg at hcons
      obtain ⟨i, hi⟩ := hcons
      simp only [hBad, Set.mem_iUnion, Set.mem_preimage, Function.eval]
      exact ⟨i, hi⟩
  refine (measure_mono key).trans ((measure_union_le _ _).trans ?_)
  rw [hBad0, zero_add]
  by_cases hbig : ENNReal.ofReal ε < D Aset.1
  · have hset : Out ∩ {_S | ENNReal.ofReal ε < D Aset.1} = Out := by
      ext S; simp [hbig]
    rw [hset]
    have hAm : MeasurableSet Aset.1 := (Set.to_countable _).measurableSet
    have hνE : ν E = 1 - D Aset.1 := by
      rw [hν, Measure.map_apply hf (measurable_fst hAm.compl)]
      have : f ⁻¹' E = Aset.1ᶜ := by ext x; simp [hE, hf_def]
      rw [this, measure_compl hAm (measure_ne_top _ _), measure_univ]
    have hpi : iidLaw ν m Out = (1 - D Aset.1) ^ m := by
      rw [iidLaw, hOut, Measure.pi_pi]
      simp [hνE]
    rw [hpi]
    have hε1 : ε < 1 := by
      have : D Aset.1 ≤ 1 := prob_le_one
      have := hbig.trans_le this
      rwa [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff one_pos] at this
    have h1 : 1 - D Aset.1 ≤ ENNReal.ofReal (1 - ε) := by
      rw [ENNReal.ofReal_sub _ hε.le, ENNReal.ofReal_one]
      exact tsub_le_tsub_left hbig.le _
    calc (1 - D Aset.1) ^ m ≤ ENNReal.ofReal (1 - ε) ^ m := pow_le_pow_left' h1 m
      _ = ENNReal.ofReal ((1 - ε) ^ m) := (ENNReal.ofReal_pow (by linarith) m).symm
      _ ≤ ENNReal.ofReal δ := by
        apply ENNReal.ofReal_le_ofReal
        have hexp : (1 - ε) ^ m ≤ Real.exp (-ε) ^ m :=
          pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg ε) m
        rw [← Real.exp_nat_mul] at hexp
        refine hexp.trans ?_
        have hlog : Real.log (1 / δ) ≤ ε * m := by
          rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hε] at hm
          linarith
        calc Real.exp (m * -ε) ≤ Real.exp (- Real.log (1 / δ)) := by
              apply Real.exp_le_exp.2; linarith
          _ = δ := by
              rw [one_div, Real.log_inv, neg_neg, Real.exp_log hδ]
  · have hset : Out ∩ {_S | ENNReal.ofReal ε < D Aset.1} = ∅ := by
      ext S; simp [hbig]
    rw [hset, measure_empty]
    simp
