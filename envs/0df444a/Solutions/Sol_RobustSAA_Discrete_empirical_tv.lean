-- Prove2me | solution 1 for RobustSAA.Discrete.empirical_tv
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T20:25:34.67348+00:00
-- url     : https://prove2.me/submissions/237bb008-df44-41ab-b8ff-e84a7e368f0a

import Mathlib
import Definitions.Def_RobustSAA_Discrete_Setting

namespace RobustSAA.Discrete

open Filter MeasureTheory ProbabilityTheory Topology

lemma phat_tendsto_aux (n : ℕ) (F : ProbabilityMeasure (Fin n)) (j : Fin n) :
    ∀ᵐ ω ∂dataLaw F, Tendsto (fun N => phat (sample ω N) j) atTop (𝓝 (pvec F j)) := by
  set f : Fin n → ℝ := fun x => if x = j then 1 else 0 with hf
  have hfm : Measurable f := measurable_of_finite f
  set X : ℕ → (ℕ → Fin n) → ℝ := fun i ω => f (ω i) with hX
  have hind : iIndepFun X (dataLaw F) := by
    unfold dataLaw
    exact iIndepFun_infinitePi (P := fun _ : ℕ => (F : Measure (Fin n)))
      (X := fun _ => f) (fun _ => hfm)
  have hmapi : ∀ i, (dataLaw F).map (fun ω : ℕ → Fin n => ω i) = (F : Measure (Fin n)) := by
    intro i
    unfold dataLaw
    exact Measure.infinitePi_map_eval _ i
  have hXm : ∀ i, Measurable (X i) := fun i => hfm.comp (measurable_pi_apply i)
  have hident : ∀ i, IdentDistrib (X i) (X 0) (dataLaw F) (dataLaw F) := by
    intro i
    refine ⟨(hXm i).aemeasurable, (hXm 0).aemeasurable, ?_⟩
    have h1 : X i = f ∘ (fun ω : ℕ → Fin n => ω i) := rfl
    have h0 : X 0 = f ∘ (fun ω : ℕ → Fin n => ω 0) := rfl
    rw [h1, h0, ← Measure.map_map hfm (measurable_pi_apply i),
      ← Measure.map_map hfm (measurable_pi_apply 0), hmapi, hmapi]
  have hprob : IsProbabilityMeasure (dataLaw F) := by
    unfold dataLaw; infer_instance
  have hint : Integrable (X 0) (dataLaw F) := by
    refine Integrable.of_bound (C := 1) (hXm 0).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    simp only [hX, hf]
    split_ifs <;> simp
  have hE : (dataLaw F)[X 0] = pvec F j := by
    show ∫ ω, f (ω 0) ∂dataLaw F = pvec F j
    rw [← integral_map (φ := fun ω : ℕ → Fin n => ω 0) (measurable_pi_apply 0).aemeasurable
      hfm.aestronglyMeasurable, hmapi, integral_fintype]
    · simp [hf, pvec]
    · exact .of_finite
  have hslln := strong_law_ae X hint (fun i k hik => hind.indepFun hik) hident
  filter_upwards [hslln] with ω hω
  rw [hE] at hω
  refine hω.congr' (Filter.Eventually.of_forall (fun N => ?_))
  simp only [smul_eq_mul, phat, sample, hX, hf]
  rw [← Fin.sum_univ_eq_sum_range (fun x => if ω x = j then (1:ℝ) else 0) N,
    Finset.sum_boole, div_eq_inv_mul]
  simp only [mul_eq_mul_left_iff, Nat.cast_inj, inv_eq_zero, Nat.cast_eq_zero]
  left
  congr 1

lemma empirical_tv_proof (n : ℕ) (F : ProbabilityMeasure (Fin n)) :
    ∀ᵐ ω ∂dataLaw F,
      Tendsto (fun N => dTV (phat (sample ω N)) (pvec F)) atTop (nhds 0) := by
  have h := ae_all_iff.2 (phat_tendsto_aux n F)
  filter_upwards [h] with ω hω
  have : Tendsto (fun N => dTV (phat (sample ω N)) (pvec F)) atTop
      (nhds ((1/2 : ℝ) * ∑ j : Fin n, |pvec F j - pvec F j|)) := by
    unfold dTV
    refine Tendsto.const_mul _ (tendsto_finsetSum _ (fun j _ => ?_))
    exact ((hω j).sub tendsto_const_nhds).abs
  simpa using this


end RobustSAA.Discrete

open RobustSAA.Discrete Filter MeasureTheory in
theorem solution (n : ℕ) (F : ProbabilityMeasure (Fin n)) :
    ∀ᵐ ω ∂dataLaw F,
      Tendsto (fun N => dTV (phat (sample ω N)) (pvec F)) atTop (nhds 0) :=
  empirical_tv_proof n F
