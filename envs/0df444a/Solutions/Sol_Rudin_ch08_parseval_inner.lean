-- Prove2me | solution 1 for Rudin.ch08_parseval_inner
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-18T14:03:15.534983+00:00
-- url     : https://prove2.me/submissions/da8f5052-d550-4cc6-a38f-5f2248182ba3

import Mathlib
import Definitions.Def_Rudin_ch08_fourier

open Filter Topology MeasureTheory

noncomputable section

private instance factTwoPi : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

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

private lemma rudin_fourierCoeff_eq' (f : ℝ → ℂ) (n : ℤ) (a b : ℝ) (hab : a < b)
    (ha : a = -Real.pi) (hb : b = Real.pi) :
    fourierCoeffOn hab f n = Rudin.fourierCoeff f n := by
  subst ha; subst hb; exact rudin_fourierCoeff_eq f n hab

private lemma tendsto_Icc_atTop :
    Tendsto (fun N : ℤ => Finset.Icc (-N) N) atTop atTop := by
  refine tendsto_atTop_finset_of_monotone (fun m n hmn => ?_) (fun x => ⟨(x.natAbs : ℤ), ?_⟩)
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  · simp only [Finset.mem_Icc]
    omega

/-- The `L²` element of the circle of circumference `2π` attached to a function that is
square-integrable on one period, together with its two defining properties. -/
private lemma exists_lp (f : ℝ → ℂ)
    (hf : IntervalIntegrable f MeasureTheory.volume (-Real.pi) Real.pi)
    (hf2 : IntervalIntegrable (fun x => ‖f x‖ ^ 2) MeasureTheory.volume (-Real.pi) Real.pi) :
    ∃ F : Lp ℂ 2 (AddCircle.haarAddCircle (T := 2 * Real.pi)),
      (∀ n : ℤ, fourierCoeff (⇑F) n = Rudin.fourierCoeff f n) ∧
      ⇑F =ᵐ[AddCircle.haarAddCircle] AddCircle.liftIoc (2 * Real.pi) (-Real.pi) f := by
  have hab : -Real.pi < Real.pi := by have := Real.pi_pos; linarith
  have hpi2 : -Real.pi + 2 * Real.pi = Real.pi := by ring
  have hmeas : AEStronglyMeasurable f (volume.restrict (Set.Ioc (-Real.pi) Real.pi)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).1 hf).aestronglyMeasurable
  have hL2 : MemLp f 2 (volume.restrict (Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi))) := by
    rw [hpi2]
    exact (memLp_two_iff_integrable_sq_norm hmeas).2
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).1 hf2)
  have hF : MemLp (AddCircle.liftIoc (2 * Real.pi) (-Real.pi) f) 2 AddCircle.haarAddCircle :=
    hL2.memLp_liftIoc.haarAddCircle
  refine ⟨hF.toLp, fun n => ?_, hF.coeFn_toLp⟩
  rw [fourierCoeff_congr_ae hF.coeFn_toLp, fourierCoeff_liftIoc_eq]
  exact rudin_fourierCoeff_eq' f n _ _ _ rfl hpi2

theorem solution (f g : ℝ → ℂ) (hfper : Rudin.HasPeriodTwoPi f) (hgper : Rudin.HasPeriodTwoPi g)
    (hf : IntervalIntegrable f MeasureTheory.volume (-Real.pi) Real.pi)
    (hg : IntervalIntegrable g MeasureTheory.volume (-Real.pi) Real.pi)
    (hf2 : IntervalIntegrable (fun x => ‖f x‖ ^ 2) MeasureTheory.volume (-Real.pi) Real.pi)
    (hg2 : IntervalIntegrable (fun x => ‖g x‖ ^ 2) MeasureTheory.volume (-Real.pi) Real.pi) :
    Tendsto (fun N => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        Rudin.fourierCoeff f n * (starRingEnd ℂ) (Rudin.fourierCoeff g n)) atTop
      (𝓝 ((1 / (2 * Real.pi) : ℂ) *
        ∫ x in (-Real.pi)..Real.pi, f x * (starRingEnd ℂ) (g x))) := by
  obtain ⟨F, hFc, hFae⟩ := exists_lp f hf hf2
  obtain ⟨G, hGc, hGae⟩ := exists_lp g hg hg2
  have hpi2 : -Real.pi + 2 * Real.pi = Real.pi := by ring
  -- the inner product of `G` and `F` computed as an integral
  have hInner : (inner ℂ G F : ℂ)
      = (1 / (2 * Real.pi) : ℂ) * ∫ x in (-Real.pi)..Real.pi, f x * (starRingEnd ℂ) (g x) := by
    rw [MeasureTheory.L2.inner_def]
    have h1 : ∫ a : AddCircle (2 * Real.pi), (inner ℂ (G a) (F a) : ℂ) ∂AddCircle.haarAddCircle
        = ∫ a : AddCircle (2 * Real.pi),
            AddCircle.liftIoc (2 * Real.pi) (-Real.pi)
              (fun x => (starRingEnd ℂ) (g x) * f x) a ∂AddCircle.haarAddCircle := by
      refine integral_congr_ae ?_
      filter_upwards [hFae, hGae] with a ha hb
      rw [RCLike.inner_apply', ha, hb]
      rfl
    rw [h1, AddCircle.integral_haarAddCircle,
      AddCircle.integral_liftIoc_eq_intervalIntegral, hpi2, Complex.real_smul]
    have h2 : ∫ x in (-Real.pi)..Real.pi, (starRingEnd ℂ) (g x) * f x
        = ∫ x in (-Real.pi)..Real.pi, f x * (starRingEnd ℂ) (g x) := by
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      ring
    rw [h2]
    congr 1
    push_cast
    ring
  -- Parseval for the Hilbert basis of exponentials
  have hs := (fourierBasis (T := 2 * Real.pi)).hasSum_inner_mul_inner G F
  have hterm : ∀ i : ℤ,
      (inner ℂ G (fourierBasis (T := 2 * Real.pi) i) : ℂ) *
          (inner ℂ (fourierBasis (T := 2 * Real.pi) i) F : ℂ)
        = Rudin.fourierCoeff f i * (starRingEnd ℂ) (Rudin.fourierCoeff g i) := by
    intro i
    have hFi : (inner ℂ (fourierBasis (T := 2 * Real.pi) i) F : ℂ) = Rudin.fourierCoeff f i := by
      rw [← HilbertBasis.repr_apply_apply, fourierBasis_repr, hFc]
    have hGi : (inner ℂ G (fourierBasis (T := 2 * Real.pi) i) : ℂ)
        = (starRingEnd ℂ) (Rudin.fourierCoeff g i) := by
      rw [← inner_conj_symm, ← HilbertBasis.repr_apply_apply, fourierBasis_repr, hGc]
    rw [hFi, hGi, mul_comm]
  simp_rw [hterm, hInner] at hs
  have htend : Tendsto (fun s : Finset ℤ => ∑ n ∈ s,
      Rudin.fourierCoeff f n * (starRingEnd ℂ) (Rudin.fourierCoeff g n)) atTop
      (𝓝 ((1 / (2 * Real.pi) : ℂ) *
        ∫ x in (-Real.pi)..Real.pi, f x * (starRingEnd ℂ) (g x))) := hs
  exact htend.comp tendsto_Icc_atTop
