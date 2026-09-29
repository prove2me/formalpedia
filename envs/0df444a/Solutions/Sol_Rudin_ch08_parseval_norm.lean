-- Prove2me | solution 1 for Rudin.ch08_parseval_norm
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-18T13:58:22.670919+00:00
-- url     : https://prove2.me/submissions/a4c08de0-1610-4ace-853f-3fca61afcfe4

import Mathlib
import Definitions.Def_Rudin_ch08_fourier
open Filter Topology MeasureTheory

private lemma rudin_fourierCoeff_eq (f : ℝ → ℂ) (n : ℤ) (hab : -Real.pi < Real.pi) :
    fourierCoeffOn hab f n = Rudin.fourierCoeff f n := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [fourierCoeffOn_eq_integral, Rudin.fourierCoeff, Complex.real_smul]
  congr 1
  · push_cast; field_simp; norm_num
  · refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [fourier_coe_apply, smul_eq_mul, mul_comm]
    congr 2
    push_cast
    field_simp
    ring

private lemma tendsto_Icc_atTop :
    Tendsto (fun N : ℤ => Finset.Icc (-N) N) atTop atTop := by
  refine tendsto_atTop_finset_of_monotone (fun m n hmn => ?_) (fun x => ⟨(x.natAbs : ℤ), ?_⟩)
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  · simp only [Finset.mem_Icc]
    omega

theorem solution (f : ℝ → ℂ) (hfper : Rudin.HasPeriodTwoPi f)
    (hf : IntervalIntegrable f MeasureTheory.volume (-Real.pi) Real.pi)
    (hf2 : IntervalIntegrable (fun x => ‖f x‖ ^ 2) MeasureTheory.volume (-Real.pi) Real.pi) :
    Tendsto (fun N => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖Rudin.fourierCoeff f n‖ ^ 2) atTop
      (𝓝 ((1 / (2 * Real.pi)) * ∫ x in (-Real.pi)..Real.pi, ‖f x‖ ^ 2)) := by
  have hab : -Real.pi < Real.pi := by have := Real.pi_pos; linarith
  have hmeas : AEStronglyMeasurable f (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).1 hf).aestronglyMeasurable
  have hL2 : MemLp f 2 (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) :=
    (memLp_two_iff_integrable_sq_norm hmeas).2
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).1 hf2)
  have hs := hasSum_sq_fourierCoeffOn hab hL2
  simp_rw [rudin_fourierCoeff_eq f _ hab] at hs
  have hval : (Real.pi - -Real.pi)⁻¹ • (∫ x in (-Real.pi)..Real.pi, ‖f x‖ ^ 2)
      = (1 / (2 * Real.pi)) * ∫ x in (-Real.pi)..Real.pi, ‖f x‖ ^ 2 := by
    rw [smul_eq_mul, one_div]
    congr 2
    ring
  rw [hval] at hs
  have htend : Tendsto (fun s : Finset ℤ => ∑ n ∈ s, ‖Rudin.fourierCoeff f n‖ ^ 2) atTop
      (𝓝 ((1 / (2 * Real.pi)) * ∫ x in (-Real.pi)..Real.pi, ‖f x‖ ^ 2)) := hs
  exact htend.comp tendsto_Icc_atTop
