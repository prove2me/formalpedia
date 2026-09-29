-- Prove2me | solution 1 for Rudin.ch08_parseval_L2_conv
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-18T14:08:17.734992+00:00
-- url     : https://prove2.me/submissions/2665b82a-2d48-48b7-b317-3d20be54cc2c

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

private lemma lp_norm_eq_L2Norm (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := 2 * Real.pi)))
    (h : ℝ → ℂ) (hae : ⇑u =ᵐ[AddCircle.haarAddCircle]
      AddCircle.liftIoc (2 * Real.pi) (-Real.pi) h) :
    ‖u‖ = Rudin.L2Norm h := by
  have hpi2 : -Real.pi + 2 * Real.pi = Real.pi := by ring
  have hsq : ‖u‖ ^ 2 = ∫ t : AddCircle (2 * Real.pi), ‖u t‖ ^ 2 ∂AddCircle.haarAddCircle := by
    have H := congr_arg RCLike.re (@MeasureTheory.L2.inner_def (AddCircle (2 * Real.pi)) ℂ ℂ _ _ _ _ _ u u)
    rw [← integral_re (MeasureTheory.L2.integrable_inner u u)] at H
    simp only [← norm_sq_eq_re_inner] at H
    exact H
  have hint : ∫ t : AddCircle (2 * Real.pi), ‖u t‖ ^ 2 ∂AddCircle.haarAddCircle
      = (1 / (2 * Real.pi)) * ∫ x in (-Real.pi)..Real.pi, ‖h x‖ ^ 2 := by
    have h1 : ∫ t : AddCircle (2 * Real.pi), ‖u t‖ ^ 2 ∂AddCircle.haarAddCircle
        = ∫ t : AddCircle (2 * Real.pi),
            AddCircle.liftIoc (2 * Real.pi) (-Real.pi) (fun x => ‖h x‖ ^ 2) t
            ∂AddCircle.haarAddCircle := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with t ht
      rw [ht]
      rfl
    rw [h1, AddCircle.integral_haarAddCircle, AddCircle.integral_liftIoc_eq_intervalIntegral,
      hpi2, smul_eq_mul, one_div]
  rw [Rudin.L2Norm, ← hint, ← hsq, Real.sqrt_sq (norm_nonneg u)]

private lemma lp_coeFn_sum {α : Type} {m : MeasurableSpace α} {μ : Measure α} {ι : Type}
    (s : Finset ι) (F : ι → Lp ℂ 2 μ) :
    ⇑(∑ i ∈ s, F i) =ᵐ[μ] fun a => ∑ i ∈ s, (F i) a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
      simpa using hx
  | insert a s ha ih =>
      filter_upwards [Lp.coeFn_add (F a) (∑ i ∈ s, F i), ih] with x h1 h2
      rw [Finset.sum_insert ha, h1, Pi.add_apply, h2, Finset.sum_insert ha]

private lemma fourier_eq_exp (n : ℤ) (x : ℝ) :
    (fourier n : AddCircle (2 * Real.pi) → ℂ) x = Complex.exp ((n : ℂ) * Complex.I * (x : ℂ)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp

private lemma lift_sub_partial (f : ℝ → ℂ) (N : ℕ) (c : ℤ → ℂ) (t : AddCircle (2 * Real.pi)) :
    AddCircle.liftIoc (2 * Real.pi) (-Real.pi)
        (fun x => f x - ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          c n * Complex.exp ((n : ℂ) * Complex.I * (x : ℂ))) t
      = AddCircle.liftIoc (2 * Real.pi) (-Real.pi) f t
        - ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            c n * (fourier n : AddCircle (2 * Real.pi) → ℂ) t := by
  set y := AddCircle.equivIoc (2 * Real.pi) (-Real.pi) t with hy
  have ht : ((y : ℝ) : AddCircle (2 * Real.pi)) = t := AddCircle.coe_equivIoc
  rw [← ht, AddCircle.liftIoc_coe_apply y.2, AddCircle.liftIoc_coe_apply y.2]
  simp_rw [fourier_eq_exp]


private lemma tendsto_Icc_atTop_nat :
    Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) atTop atTop := by
  refine tendsto_atTop_finset_of_monotone (fun m n hmn => ?_) (fun x => ⟨x.natAbs, ?_⟩)
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    have : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hmn
    omega
  · simp only [Finset.mem_Icc]
    omega

theorem solution (f : ℝ → ℂ) (hfper : Rudin.HasPeriodTwoPi f)
    (hf : IntervalIntegrable f MeasureTheory.volume (-Real.pi) Real.pi)
    (hf2 : IntervalIntegrable (fun x => ‖f x‖ ^ 2) MeasureTheory.volume (-Real.pi) Real.pi) :
    Tendsto (fun N => Rudin.L2Norm (fun x => f x - Rudin.fourierPartialSum f N x)) atTop (𝓝 0) := by
  obtain ⟨F, hFc, hFae⟩ := exists_lp f hf hf2
  set S : ℕ → Lp ℂ 2 (AddCircle.haarAddCircle (T := 2 * Real.pi)) := fun N =>
    ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeff (⇑F) n • fourierLp 2 n with hSdef
  have hconv : Tendsto S atTop (𝓝 F) :=
    (hasSum_fourier_series_L2 F).comp tendsto_Icc_atTop_nat
  have hsmul : ∀ n : ℤ,
      ⇑(fourierCoeff (⇑F) n • fourierLp (T := 2 * Real.pi) 2 n) =ᵐ[AddCircle.haarAddCircle]
        fun t => fourierCoeff (⇑F) n * (fourier n : AddCircle (2 * Real.pi) → ℂ) t := by
    intro n
    filter_upwards [Lp.coeFn_smul (fourierCoeff (⇑F) n) (fourierLp (T := 2 * Real.pi) 2 n),
      coeFn_fourierLp (T := 2 * Real.pi) 2 n] with t h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul]
  have hSae : ∀ N : ℕ, ⇑(S N) =ᵐ[AddCircle.haarAddCircle]
      fun t => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        fourierCoeff (⇑F) n * (fourier n : AddCircle (2 * Real.pi) → ℂ) t := by
    intro N
    have hall : ∀ᵐ t ∂(AddCircle.haarAddCircle (T := 2 * Real.pi)),
        ∀ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          (fourierCoeff (⇑F) n • fourierLp (T := 2 * Real.pi) 2 n) t
            = fourierCoeff (⇑F) n * (fourier n : AddCircle (2 * Real.pi) → ℂ) t := by
      rw [Filter.eventually_all_finset]
      intro n _
      exact hsmul n
    filter_upwards [lp_coeFn_sum (Finset.Icc (-(N : ℤ)) (N : ℤ))
      (fun n => fourierCoeff (⇑F) n • fourierLp (T := 2 * Real.pi) 2 n), hall] with t h1 h2
    rw [h1]
    exact Finset.sum_congr rfl h2
  have hkey : ∀ N : ℕ,
      Rudin.L2Norm (fun x => f x - Rudin.fourierPartialSum f N x) = ‖F - S N‖ := by
    intro N
    refine (lp_norm_eq_L2Norm (F - S N) _ ?_).symm
    filter_upwards [Lp.coeFn_sub F (S N), hFae, hSae N] with t h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
    simp only [Rudin.fourierPartialSum]
    rw [lift_sub_partial f N (fun n => Rudin.fourierCoeff f n) t]
    simp only [hFc]
  have hzero : Tendsto (fun N : ℕ => ‖F - S N‖) atTop (𝓝 0) := by
    have h0 : Tendsto (fun N : ℕ => F - S N) atTop (𝓝 (F - F)) :=
      tendsto_const_nhds.sub hconv
    simpa using h0.norm
  simpa [hkey] using hzero

end
