-- Prove2me | solution 1 for UnderstandingML.pac_bayes_finite_class
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T05:20:47.580574+00:00
-- url     : https://prove2.me/submissions/86739418-c357-494f-8592-930e340ad4b0

import Mathlib
import Definitions.Def_UnderstandingML_PACBayes

open MeasureTheory
open MeasureTheory ProbabilityTheory

namespace UnderstandingML

lemma pb_hoeff {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (g : Z → ℝ) (hg : Measurable g) (hg01 : ∀ z, g z ∈ Set.Icc (0:ℝ) 1) (m : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    (iidLaw D m).real {S | t ≤ ∑ i : Fin m, (g (S i) - ∫ z, g z ∂D)} ≤
      Real.exp (-t ^ 2 / (2 * ∑ i : Fin m, ((‖(1:ℝ) - 0‖₊ / 2) ^ 2 : NNReal))) := by
  set μg := ∫ z, g z ∂D with hμg
  have hind : iIndepFun (fun (i : Fin m) (S : Fin m → Z) => g (S i) - μg) (iidLaw D m) := by
    unfold iidLaw
    exact iIndepFun_pi (X := fun _ z => g z - μg) (fun _ => (hg.sub_const μg).aemeasurable)
  have : IsProbabilityMeasure (iidLaw D m) := by unfold iidLaw; infer_instance
  have hsub : ∀ i ∈ (Finset.univ : Finset (Fin m)), HasSubgaussianMGF
      (fun S : Fin m → Z => g (S i) - μg) ((‖(1:ℝ) - 0‖₊ / 2) ^ 2) (iidLaw D m) := by
    intro i _
    have hm : AEMeasurable (fun S : Fin m → Z => g (S i)) (iidLaw D m) :=
      (hg.comp (measurable_pi_apply i)).aemeasurable
    have h := hasSubgaussianMGF_of_mem_Icc (a := 0) (b := 1) hm
      (Filter.Eventually.of_forall fun S => hg01 (S i))
    have hint : ∫ S, g (S i) ∂(iidLaw D m) = μg := by
      unfold iidLaw
      exact integral_comp_eval hg.aestronglyMeasurable
    rw [hint] at h
    exact h
  exact HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind hsub ht

lemma pb_hoeff' {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (g : Z → ℝ) (hg : Measurable g) (hg01 : ∀ z, g z ∈ Set.Icc (0:ℝ) 1) (m : ℕ)
    (hm : 0 < m) (t : ℝ) (ht : 0 ≤ t) :
    iidLaw D m {S | t ≤ ∑ i : Fin m, (g (S i) - ∫ z, g z ∂D)} ≤
      ENNReal.ofReal (Real.exp (-(2 * t ^ 2 / m))) := by
  have : IsProbabilityMeasure (iidLaw D m) := by unfold iidLaw; infer_instance
  have h := pb_hoeff D g hg hg01 m t ht
  rw [← ENNReal.ofReal_toReal (measure_ne_top (iidLaw D m) _)]
  apply ENNReal.ofReal_le_ofReal
  refine h.trans (le_of_eq ?_)
  congr 1
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hs : ((∑ i : Fin m, ((‖(1:ℝ) - 0‖₊ / 2) ^ 2 : NNReal) : NNReal) : ℝ) = m / 4 := by
    push_cast
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
    ring
  rw [hs]
  field_simp
  ring

theorem pb_main {Z Hyp : Type*} [MeasurableSpace Z] (loss : Hyp → Z → ℝ)
    (H : Finset Hyp) (hH : H.Nonempty) (hmeas : ∀ h ∈ H, Measurable (loss h))
    (hloss : ∀ h z, loss h z ∈ Set.Icc (0 : ℝ) 1) (D : Measure Z) [IsProbabilityMeasure D]
    (m : ℕ) (hm : 2 ≤ m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    iidLaw D m {S | ∃ h ∈ H,
      empRisk loss S h + Real.sqrt ((Real.log H.card + Real.log (m / δ)) / (2 * (m - 1))) <
        risk loss D h} ≤ ENNReal.ofReal δ := by
  set ε := Real.sqrt ((Real.log H.card + Real.log (m / δ)) / (2 * (m - 1))) with hε
  have hm0 : 0 < m := by omega
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hcard : (1:ℝ) ≤ H.card := by exact_mod_cast hH.card_pos
  set L := Real.log H.card + Real.log (m / δ) with hL
  have hlogH : 0 ≤ Real.log H.card := Real.log_nonneg hcard
  have hlogm : 0 < Real.log (m / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have hL0 : 0 ≤ L := by linarith
  have hε2 : ε ^ 2 = L / (2 * (m - 1)) := Real.sq_sqrt (div_nonneg hL0 (by linarith))
  have hε0 : 0 ≤ ε := Real.sqrt_nonneg _
  have hper : ∀ h ∈ H, iidLaw D m {S | empRisk loss S h + ε < risk loss D h}
      ≤ ENNReal.ofReal (δ / (H.card * m)) := by
    intro h hh
    set g : Z → ℝ := fun z => 1 - loss h z with hg
    have hgm : Measurable g := measurable_const.sub (hmeas h hh)
    have hg01 : ∀ z, g z ∈ Set.Icc (0:ℝ) 1 := fun z => by
      have := hloss h z
      simp only [hg, Set.mem_Icc] at this ⊢
      constructor <;> linarith [this.1, this.2]
    have hint : Integrable (loss h) D :=
      Integrable.of_mem_Icc 0 1 (hmeas h hh).aemeasurable
        (Filter.Eventually.of_forall fun z => hloss h z)
    have hEg : ∫ z, g z ∂D = 1 - risk loss D h := by
      simp only [hg]
      rw [integral_sub (integrable_const 1) hint]
      simp [risk]
    have hsub : {S : Fin m → Z | empRisk loss S h + ε < risk loss D h} ⊆
        {S | m * ε ≤ ∑ i : Fin m, (g (S i) - ∫ z, g z ∂D)} := by
      intro S hS
      simp only [Set.mem_setOf_eq] at hS ⊢
      rw [hEg]
      have hsum : ∑ i : Fin m, (g (S i) - (1 - risk loss D h))
          = m * risk loss D h - ∑ i, loss h (S i) := by
        simp only [hg]
        rw [show (fun i : Fin m => 1 - loss h (S i) - (1 - risk loss D h))
            = fun i => risk loss D h - loss h (S i) by funext i; ring]
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
      have hmpos : (0:ℝ) < m := by linarith
      have hemp : empRisk loss S h * m = ∑ i, loss h (S i) := by
        unfold empRisk
        field_simp
      rw [hsum]
      nlinarith
    calc iidLaw D m {S | empRisk loss S h + ε < risk loss D h}
        ≤ iidLaw D m {S | m * ε ≤ ∑ i : Fin m, (g (S i) - ∫ z, g z ∂D)} := measure_mono hsub
      _ ≤ ENNReal.ofReal (Real.exp (-(2 * (m * ε) ^ 2 / m))) :=
          pb_hoeff' D g hgm hg01 m hm0 (m * ε) (by positivity)
      _ ≤ ENNReal.ofReal (δ / (H.card * m)) := by
          apply ENNReal.ofReal_le_ofReal
          have hm1 : (0:ℝ) < m - 1 := by linarith
          have e1 : 2 * ((m:ℝ) * ε) ^ 2 / m = m / (m - 1) * L := by
            rw [show 2 * ((m:ℝ) * ε) ^ 2 / m = 2 * m * ε ^ 2 by field_simp, hε2]
            field_simp
          rw [e1]
          have hmm : 1 ≤ (m:ℝ) / (m - 1) := by rw [le_div_iff₀ hm1]; linarith
          have hle : L ≤ m / (m - 1) * L := le_mul_of_one_le_left hL0 hmm
          calc Real.exp (-(m / (m - 1) * L)) ≤ Real.exp (-L) := Real.exp_le_exp.mpr (by linarith)
            _ = δ / (H.card * m) := by
                rw [hL, neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg,
                  Real.exp_log (by linarith), Real.exp_log (by positivity)]
                field_simp
  have hU : {S : Fin m → Z | ∃ h ∈ H, empRisk loss S h + ε < risk loss D h} =
      ⋃ h ∈ H, {S | empRisk loss S h + ε < risk loss D h} := by
    ext S
    simp
  rw [hU]
  calc iidLaw D m (⋃ h ∈ H, {S | empRisk loss S h + ε < risk loss D h})
      ≤ ∑ h ∈ H, iidLaw D m {S | empRisk loss S h + ε < risk loss D h} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ h ∈ H, ENNReal.ofReal (δ / (H.card * m)) := Finset.sum_le_sum hper
    _ = ENNReal.ofReal (H.card * (δ / (H.card * m))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal δ := by
        apply ENNReal.ofReal_le_ofReal
        have hc0 : (H.card : ℝ) ≠ 0 := by linarith
        rw [show (H.card : ℝ) * (δ / (H.card * m)) = δ / m by field_simp]
        exact div_le_self hδ.le (by linarith)

end UnderstandingML

open UnderstandingML

theorem solution {Z Hyp : Type*} [MeasurableSpace Z] (loss : Hyp → Z → ℝ)
    (H : Finset Hyp) (hH : H.Nonempty) (hmeas : ∀ h ∈ H, Measurable (loss h))
    (hloss : ∀ h z, loss h z ∈ Set.Icc (0 : ℝ) 1) (D : Measure Z) [IsProbabilityMeasure D]
    (m : ℕ) (hm : 2 ≤ m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    iidLaw D m {S | ∃ h ∈ H,
      empRisk loss S h + Real.sqrt ((Real.log H.card + Real.log (m / δ)) / (2 * (m - 1))) <
        risk loss D h} ≤ ENNReal.ofReal δ := by
  exact pb_main loss H hH hmeas hloss D m hm δ hδ hδ1
