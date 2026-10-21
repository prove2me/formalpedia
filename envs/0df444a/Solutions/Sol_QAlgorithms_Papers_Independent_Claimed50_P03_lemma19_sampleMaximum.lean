-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P03.lemma19_sampleMaximum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T10:30:16.120635+00:00
-- url     : https://prove2.me/submissions/3855e8ac-d3a8-4a63-a900-d3818e2cb970

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace


lemma g58a_lowerset_measure (mu : Measure ℝ) [IsProbabilityMeasure mu] (p : ENNReal) :
    mu {y | mu (Set.Iic y) < p} ≤ p := by
  set B := {y | mu (Set.Iic y) < p} with hB
  have hmono : Monotone (fun y : ℝ => mu (Set.Iic y)) :=
    fun a b hab => measure_mono (Set.Iic_subset_Iic.mpr hab)
  have hBm : MeasurableSet B := measurableSet_lt hmono.measurable measurable_const
  by_contra hcon
  push Not at hcon
  have hne : mu B - p ≠ 0 := (tsub_pos_of_lt hcon).ne'
  obtain ⟨K, hKB, hK, hlt⟩ := hBm.exists_isCompact_lt_add (measure_ne_top mu B) hne
  have hpK : p < mu K := by
    by_contra h
    push Not at h
    have : mu K + (mu B - p) ≤ p + (mu B - p) := add_le_add h le_rfl
    rw [add_tsub_cancel_of_le hcon.le] at this
    exact absurd (lt_of_lt_of_le hlt this) (lt_irrefl _)
  rcases K.eq_empty_or_nonempty with h | h
  · rw [h, measure_empty] at hpK; exact absurd hpK (not_lt_zero)
  · have hm := hK.sSup_mem h
    have hsub : K ⊆ Set.Iic (sSup K) := fun x hx => le_csSup hK.bddAbove hx
    have := hKB hm
    simp only [hB, Set.mem_ofPred_eq] at this
    exact absurd (lt_of_lt_of_le hpK ((measure_mono hsub).trans this.le)) (lt_irrefl _)

theorem solution (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (eps delta : ℝ) (he0 : 0 < eps) (he1 : eps < 1)
    (hd0 : 0 < delta) (hd1 : delta < 1) :
    let N := ⌈Real.log (1 / delta) / eps⌉₊
    ENNReal.ofReal (1 - delta) ≤
      (Measure.pi (fun _ : Fin N => mu))
        {x | ENNReal.ofReal (1 - eps) ≤ mu (Set.Iic (sampleMaximum x))} := by
  intro N
  set p := ENNReal.ofReal (1 - eps) with hp
  set E := {x : Fin N → ℝ | p ≤ mu (Set.Iic (sampleMaximum x))} with hE
  set B := {y | mu (Set.Iic y) < p} with hB
  have hlog : 0 < Real.log (1 / delta) := Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨hd0, hd1⟩)
  have hN : Real.log (1 / delta) / eps ≤ N := Nat.le_ceil _
  have hNpos : 0 < N := Nat.ceil_pos.mpr (div_pos hlog he0)
  have hcomp : Eᶜ ⊆ Set.univ.pi (fun _ : Fin N => B) := by
    intro x hx
    simp only [hE, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hx
    simp only [Set.mem_pi, Set.mem_univ, true_implies, hB, Set.mem_ofPred_eq]
    intro l
    have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hNpos⟩, Finset.mem_univ _⟩
    have hle : x l ≤ sampleMaximum x := by
      simp only [sampleMaximum, dif_pos hne]
      exact Finset.le_sup' x (Finset.mem_univ l)
    exact lt_of_le_of_lt (measure_mono (Set.Iic_subset_Iic.mpr hle)) hx
  have hEc : (Measure.pi (fun _ : Fin N => mu)) Eᶜ ≤ ENNReal.ofReal delta := by
    refine (measure_mono hcomp).trans ?_
    rw [Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine (pow_le_pow_left' (g58a_lowerset_measure mu p) N).trans ?_
    rw [hp, ← ENNReal.ofReal_pow (by linarith)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : (1 - eps) ^ N ≤ Real.exp (-eps) ^ N :=
      pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-eps)]) N
    rw [← Real.exp_nat_mul] at h1
    refine h1.trans ?_
    have h2 : Real.log (1 / delta) ≤ eps * N := by
      rw [div_le_iff₀ he0] at hN; linarith
    calc Real.exp (N * -eps) ≤ Real.exp (-Real.log (1 / delta)) :=
          Real.exp_le_exp.mpr (by nlinarith)
      _ = delta := by
          rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  have htot : (1 : ENNReal) ≤ (Measure.pi (fun _ : Fin N => mu)) E + ENNReal.ofReal delta := by
    calc (1 : ENNReal) = (Measure.pi (fun _ : Fin N => mu)) (E ∪ Eᶜ) := by
          rw [Set.union_compl_self, measure_univ]
      _ ≤ _ := measure_union_le _ _
      _ ≤ _ := add_le_add le_rfl hEc
  rw [ENNReal.ofReal_sub _ hd0.le, ENNReal.ofReal_one]
  exact tsub_le_iff_right.mpr htot

end
