-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P43.classicalFiniteLogSpan
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T15:59:58.068491+00:00
-- url     : https://prove2.me/submissions/3cb2a1d8-daed-403c-884d-0afd86d845d8

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P43
noncomputable section

open MeasureTheory Filter

open scoped ENNReal BigOperators

open QAlgorithms.Papers.Independent.Next46.P43

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsTraceClass IsDensity State tensorApply productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (homogeneousEntropy generalizedRelativeEntropy traceFirst traceSecond)

theorem g62c_coeFn_sum {X ι : Type*} [MeasurableSpace X] {mu : Measure X}
    (s : Finset ι) (F : ι → X →ₘ[mu] ℝ) :
    ⇑(∑ i ∈ s, F i) =ᵐ[mu] fun x => ∑ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact AEEqFun.coeFn_zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [AEEqFun.coeFn_add (F a) (∑ i ∈ s, F i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2]

theorem g62c_integrable {X : Type*} [MeasurableSpace X] (P mu : Measure X)
    [IsProbabilityMeasure P] (r : X → ℝ) (hr : Measurable r)
    (hpos : ∀ᵐ x ∂mu, 0 < r x)
    (hD : P = mu.withDensity (fun x => ENNReal.ofReal (r x))) :
    Integrable r mu ∧ ∫ x, r x ∂mu = 1 := by
  have hl : ∫⁻ x, ENNReal.ofReal (r x) ∂mu = 1 := by
    have := measure_univ (μ := P)
    rw [hD, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
    exact this
  have hnn : 0 ≤ᵐ[mu] r := by
    filter_upwards [hpos] with x hx using hx.le
  refine ⟨⟨hr.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal hnn, hl]; exact ENNReal.one_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hnn hr.aestronglyMeasurable, hl]; simp

theorem solution
    {X Theta : Type*} [MeasurableSpace X] [Nonempty Theta]
    (P : Theta → Measure X) (hProb : ∀ theta, IsProbabilityMeasure (P theta))
    (mu : Measure X) [SigmaFinite mu] (r : Theta → X → ℝ)
    (hr : ∀ theta, Measurable (r theta))
    (hPositive : ∀ theta, ∀ᵐ x ∂mu, 0 < r theta x)
    (hDensity : ∀ theta, P theta =
      mu.withDensity (fun x => ENNReal.ofReal (r theta x))) :
    HasExponentialRepresentation mu r ↔
      FiniteDimensional ℝ (Submodule.span ℝ
        (Set.range (fun theta => LogDensityClass mu (r theta) (hr theta)))) := by
  constructor
  · rintro ⟨n, T, xi, h, Z, hT, hh, hhpos, hZ, hrep⟩
    let g : Option (Option (Fin n)) → (X →ₘ[mu] ℝ) := fun o =>
      match o with
      | none => 1
      | some none => AEEqFun.mk (fun x => Real.log (h x)) hh.log.aestronglyMeasurable
      | some (some i) => AEEqFun.mk (T i) (hT i).aestronglyMeasurable
    have hfin : FiniteDimensional ℝ (Submodule.span ℝ (Set.range g)) :=
      FiniteDimensional.span_of_finite ℝ (Set.finite_range g)
    suffices hle : Submodule.span ℝ
        (Set.range (fun theta => LogDensityClass mu (r theta) (hr theta))) ≤
        Submodule.span ℝ (Set.range g) from Submodule.finiteDimensional_of_le hle
    refine Submodule.span_le.2 ?_
    rintro _ ⟨theta, rfl⟩
    have key : LogDensityClass mu (r theta) (hr theta) =
        (∑ i : Fin n, xi theta i • g (some (some i))) + g (some none)
          + (-Real.log (Z theta)) • g none := by
      apply AEEqFun.ext
      have e1 := AEEqFun.coeFn_mk (fun x => Real.log (r theta x))
        ((hr theta).log.aestronglyMeasurable (μ := mu))
      have e2 := AEEqFun.coeFn_add ((∑ i : Fin n, xi theta i • g (some (some i))) + g (some none))
        ((-Real.log (Z theta)) • g none)
      have e3 := AEEqFun.coeFn_add (∑ i : Fin n, xi theta i • g (some (some i))) (g (some none))
      have e4 := g62c_coeFn_sum Finset.univ (fun i : Fin n => xi theta i • g (some (some i)))
      have e5 : ∀ i : Fin n, ⇑(xi theta i • g (some (some i))) =ᵐ[mu]
          fun x => xi theta i * T i x := by
        intro i
        filter_upwards [AEEqFun.coeFn_smul (xi theta i) (g (some (some i))),
          AEEqFun.coeFn_mk (T i) (hT i).aestronglyMeasurable] with x h1 h2
        rw [h1, Pi.smul_apply, smul_eq_mul]
        simp only [g]
        rw [h2]
      have e5' : ∀ᵐ x ∂mu, ∀ i : Fin n, (xi theta i • g (some (some i))) x = xi theta i * T i x :=
        ae_all_iff.2 e5
      have e6 : ⇑(g (some none)) =ᵐ[mu] fun x => Real.log (h x) :=
        AEEqFun.coeFn_mk _ _
      have e7 : ⇑((-Real.log (Z theta)) • g none) =ᵐ[mu] fun _ => -Real.log (Z theta) := by
        filter_upwards [AEEqFun.coeFn_smul (-Real.log (Z theta)) (g none),
          (AEEqFun.coeFn_one : ⇑(1 : X →ₘ[mu] ℝ) =ᵐ[mu] 1)] with x h1 h2
        rw [h1, Pi.smul_apply, smul_eq_mul]
        simp only [g]
        rw [h2]; simp
      unfold LogDensityClass
      filter_upwards [e1, e2, e3, e4, e5', e6, e7, hrep theta, hhpos] with x h1 h2 h3 h4 h5 h6 h7 h8 h9
      rw [h1, h2, Pi.add_apply, h3, Pi.add_apply, h4, h6, h7, h8]
      simp only [h5]
      unfold ExponentialDensity
      have hZ' := (hZ theta).2.2
      rw [Real.log_div (by positivity) hZ'.ne', Real.log_mul (Real.exp_pos _).ne' h9.ne',
        Real.log_exp]
      ring
    show LogDensityClass mu (r theta) (hr theta) ∈ Submodule.span ℝ (Set.range g)
    rw [key]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨some (some i), rfl⟩))
    · exact Submodule.subset_span ⟨some none, rfl⟩
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨none, rfl⟩)
  · intro hfin
    set S := Submodule.span ℝ
        (Set.range (fun theta => LogDensityClass mu (r theta) (hr theta))) with hS
    let b := Module.finBasis ℝ S
    let d := Module.finrank ℝ S
    let T : Fin d → X → ℝ := fun j => ⇑((b j : S) : X →ₘ[mu] ℝ)
    have hmem : ∀ theta, LogDensityClass mu (r theta) (hr theta) ∈ S :=
      fun theta => Submodule.subset_span ⟨theta, rfl⟩
    let xi : Theta → Fin d → ℝ := fun theta j => b.repr ⟨_, hmem theta⟩ j
    have hlog : ∀ theta, ∀ᵐ x ∂mu, Real.log (r theta x) = ∑ j, xi theta j * T j x := by
      intro theta
      have hsum := b.sum_repr ⟨_, hmem theta⟩
      have hsum' : LogDensityClass mu (r theta) (hr theta) =
          ∑ j, xi theta j • ((b j : S) : X →ₘ[mu] ℝ) := by
        have := congrArg (fun v : S => (v : X →ₘ[mu] ℝ)) hsum
        simp only [Submodule.coe_sum, Submodule.coe_smul] at this
        exact this.symm
      have e1 := AEEqFun.coeFn_mk (fun x => Real.log (r theta x))
        ((hr theta).log.aestronglyMeasurable (μ := mu))
      have e4 := g62c_coeFn_sum Finset.univ (fun j : Fin d => xi theta j • ((b j : S) : X →ₘ[mu] ℝ))
      have e5 : ∀ᵐ x ∂mu, ∀ j : Fin d, (xi theta j • ((b j : S) : X →ₘ[mu] ℝ)) x
          = xi theta j * T j x :=
        ae_all_iff.2 (fun j => by
          filter_upwards [AEEqFun.coeFn_smul (xi theta j) ((b j : S) : X →ₘ[mu] ℝ)] with x h1
          rw [h1]; rfl)
      have e0 : ⇑(LogDensityClass mu (r theta) (hr theta)) =ᵐ[mu]
          ⇑(∑ j, xi theta j • ((b j : S) : X →ₘ[mu] ℝ)) := by rw [hsum']
      unfold LogDensityClass at e0
      filter_upwards [e0, e1, e4, e5] with x h0 h1 h4 h5
      rw [← h1, h0, h4]
      simp only [h5]
    have hexp : ∀ theta, (fun x => Real.exp (∑ j, xi theta j * T j x) * 1) =ᵐ[mu] r theta := by
      intro theta
      filter_upwards [hlog theta, hPositive theta] with x h1 h2
      rw [← h1, mul_one, Real.exp_log h2]
    refine ⟨d, T, xi, fun _ => 1, fun _ => 1, fun j => ?_, measurable_const,
      Filter.Eventually.of_forall (fun _ => zero_lt_one), fun theta => ?_, fun theta => ?_⟩
    · exact ((b j : S) : X →ₘ[mu] ℝ).stronglyMeasurable.measurable
    · haveI := hProb theta
      obtain ⟨hi, hint⟩ := g62c_integrable (P theta) mu (r theta) (hr theta) (hPositive theta)
        (hDensity theta)
      refine ⟨(integrable_congr (hexp theta)).2 hi, ?_, zero_lt_one⟩
      rw [integral_congr_ae (hexp theta), hint]
    · filter_upwards [hexp theta] with x hx
      unfold ExponentialDensity
      rw [div_one, hx]
