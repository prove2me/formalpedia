-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P08.cardinalityAttainment
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T08:24:28.917765+00:00
-- url     : https://prove2.me/submissions/7ee277d3-6480-49a7-a242-0373dfe4705b

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

open scoped Matrix ComplexOrder ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P08

set_option linter.unusedSectionVars false

namespace P08Aux

theorem dens_spec {I : Type} [Fintype I] [DecidableEq I] {ρ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef ∧ ρ.trace = 1) :
    IsSelfAdjoint ρ ∧ spectrum ℝ ρ ⊆ Set.Icc 0 1 := by
  have hA := hρ.1.isHermitian
  refine ⟨hA, ?_⟩
  rw [hA.spectrum_real_eq_range_eigenvalues]
  rintro _ ⟨i, rfl⟩
  have hnn : ∀ j, 0 ≤ hA.eigenvalues j := fun j => hρ.1.eigenvalues_nonneg j
  have htr : ∑ j, hA.eigenvalues j = 1 := by
    have h := hA.trace_eq_sum_eigenvalues
    rw [hρ.2] at h
    have h2 := congrArg Complex.re h
    simp only [Complex.one_re, Complex.re_sum] at h2
    exact h2.symm
  refine ⟨hnn i, ?_⟩
  rw [← htr]
  exact Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)

theorem cfc_contOn_dens {I : Type} [Fintype I] [DecidableEq I] (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1)) :
    ContinuousOn (fun ρ : Matrix I I ℂ => cfc f ρ) {ρ | ρ.PosSemidef ∧ ρ.trace = 1} := by
  have h : ContinuousOn (fun ρ : Matrix I I ℂ => cfc f ρ)
      {ρ | IsSelfAdjoint ρ ∧ spectrum ℝ ρ ⊆ Set.Icc 0 1} := by
    open scoped Matrix.Norms.L2Operator in
    exact continuousOn_cfc (Matrix I I ℂ) isCompact_Icc f hf
  exact h.mono fun ρ hρ => dens_spec hρ

theorem trace_cfc_contOn_dens {I : Type} [Fintype I] [DecidableEq I] (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1)) :
    ContinuousOn (fun ρ : Matrix I I ℂ => (cfc f ρ).trace.re)
      {ρ | ρ.PosSemidef ∧ ρ.trace = 1} :=
  Complex.continuous_re.comp_continuousOn
    ((continuous_id.matrix_trace).comp_continuousOn (cfc_contOn_dens f hf))

theorem sqrt_mul_sqrt {I : Type} [Fintype I] [DecidableEq I] {ρ : Matrix I I ℂ}
    (hρ : ρ.PosSemidef) : cfc Real.sqrt ρ * cfc Real.sqrt ρ = ρ := by
  have hA : IsSelfAdjoint ρ := hρ.isHermitian
  have hfin : (spectrum ℝ ρ).Finite := Matrix.finite_real_spectrum
  rw [← cfc_mul (hf := hfin.continuousOn _) (hg := hfin.continuousOn _)]
  have hnn : ∀ x ∈ spectrum ℝ ρ, 0 ≤ x := by
    intro x hx
    rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hρ.eigenvalues_nonneg i
  conv_rhs => rw [← cfc_id' ℝ ρ]
  exact cfc_congr fun x hx => Real.mul_self_sqrt (hnn x hx)

theorem sqrt_herm {I : Type} [Fintype I] [DecidableEq I] (ρ : Matrix I I ℂ) :
    (cfc Real.sqrt ρ)ᴴ = cfc Real.sqrt ρ :=
  (cfc_predicate Real.sqrt ρ : IsSelfAdjoint (cfc Real.sqrt ρ))

/-- a matrix `R * Rᴴ` is the sum of the rank-one projectors of the columns of `R` -/
theorem mul_conjTranspose_eq_sum {I : Type} [Fintype I] (R : Matrix I I ℂ) :
    R * Rᴴ = ∑ k, Matrix.vecMulVec (fun i => R i k) (star fun i => R i k) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.sum_apply]

variable {I : Type} [Fintype I] [DecidableEq I]

/-- normalisation of a vector, with a fixed unit vector `u0` at zero -/
noncomputable def nz (u0 : EuclideanSpace ℂ I) (y : I → ℂ) : EuclideanSpace ℂ I :=
  if y = 0 then u0 else ((‖WithLp.toLp 2 y‖ : ℂ)⁻¹) • WithLp.toLp 2 y

/-- homogeneous extension of a score -/
noncomputable def sc (E : EuclideanSpace ℂ I → ℝ) (u0 : EuclideanSpace ℂ I) (y : I → ℂ) : ℝ :=
  ‖WithLp.toLp 2 y‖ ^ 2 * E (nz u0 y)

theorem norm_toLp_sq (y : I → ℂ) : ‖WithLp.toLp 2 y‖ ^ 2 = ∑ i, ‖y i‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]

theorem nz_mem (u0 : EuclideanSpace ℂ I) (hu0 : ‖u0‖ = 1) (y : I → ℂ) :
    ‖nz u0 y‖ = 1 := by
  unfold nz
  split_ifs with h
  · exact hu0
  · have hne : ‖WithLp.toLp 2 y‖ ≠ 0 := by
      rw [norm_ne_zero_iff]
      intro h'
      exact h (by simpa using congrArg WithLp.ofLp h')
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ hne]

theorem pureDensity_eq_vecMulVec (v : EuclideanSpace ℂ I) :
    pureDensity v = Matrix.vecMulVec (fun i => v i) (star fun i => v i) := by
  ext a b
  simp [pureDensity, Matrix.vecMulVec_apply]

theorem sq_smul_pureDensity_nz (u0 : EuclideanSpace ℂ I) (y : I → ℂ) :
    (‖WithLp.toLp 2 y‖ ^ 2) • pureDensity (nz u0 y) = Matrix.vecMulVec y (star y) := by
  unfold nz
  split_ifs with h
  · subst h
    ext a b
    simp [Matrix.vecMulVec_apply]
  · have hne : ‖WithLp.toLp 2 y‖ ≠ 0 := by
      rw [norm_ne_zero_iff]
      intro h'
      exact h (by simpa using congrArg WithLp.ofLp h')
    ext a b
    simp only [pureDensity, Matrix.smul_apply, Matrix.of_apply, Matrix.vecMulVec_apply,
      PiLp.smul_apply, PiLp.toLp_apply, smul_eq_mul, map_mul, map_inv₀, Complex.conj_ofReal,
      Pi.star_apply, RCLike.star_def]
    rw [Complex.real_smul]
    have hc : (‖WithLp.toLp 2 y‖ : ℂ) ≠ 0 := by exact_mod_cast hne
    field_simp
    push_cast
    ring

theorem trace_vecMulVec_self (y : I → ℂ) :
    (Matrix.vecMulVec y (star y)).trace = ((∑ i, ‖y i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- from a vector decomposition of a trace-one matrix to a pure ensemble -/
theorem ens_of_vecs (E : EuclideanSpace ℂ I → ℝ) (u0 : EuclideanSpace ℂ I) (hu0 : ‖u0‖ = 1)
    {ι : Type} [Fintype ι] (y : ι → I → ℂ) (ρ : Matrix I I ℂ)
    (hρ : ρ = ∑ x, Matrix.vecMulVec (y x) (star (y x))) (htr : ρ.trace = 1) :
    ∃ e : PureEnsemble I, pureAverage e = ρ ∧
      ∑ x, e.prob x * E (e.vector x) = ∑ x, sc E u0 (y x) := by
  let σ := Fintype.equivFin ι
  let y' : Fin (Fintype.card ι) → I → ℂ := fun x => y (σ.symm x)
  have hsum : ∀ g : ι → ℝ, ∑ x, g (σ.symm x) = ∑ x, g x := fun g =>
    Equiv.sum_comp σ.symm g
  refine ⟨{ size := Fintype.card ι
            prob := fun x => ‖WithLp.toLp 2 (y' x)‖ ^ 2
            vector := fun x => nz u0 (y' x)
            nonneg := fun x => by positivity
            total := ?_
            normalized := fun x => nz_mem u0 hu0 _ }, ?_, ?_⟩
  · have h1 : ∀ x, ‖WithLp.toLp 2 (y x)‖ ^ 2 = ((Matrix.vecMulVec (y x) (star (y x))).trace).re := by
      intro x
      rw [trace_vecMulVec_self, Complex.ofReal_re, norm_toLp_sq]
    have h2 := congrArg Complex.re htr
    rw [hρ, Matrix.trace_sum, Complex.re_sum, Complex.one_re] at h2
    simp only [y']
    rw [hsum (fun x => ‖WithLp.toLp 2 (y x)‖ ^ 2)]
    simp_rw [h1]
    exact h2
  · simp only [pureAverage, y']
    simp_rw [sq_smul_pureDensity_nz]
    exact (Equiv.sum_comp σ.symm (fun x => Matrix.vecMulVec (y x) (star (y x)))).trans hρ.symm
  · exact hsum (fun x => sc E u0 (y x))

theorem sc_cont (E : EuclideanSpace ℂ I → ℝ) (u0 : EuclideanSpace ℂ I) (hu0 : ‖u0‖ = 1)
    (hE : ContinuousOn E (Metric.sphere 0 1)) : Continuous (sc E u0) := by
  obtain ⟨C, hC⟩ :=
    (isCompact_sphere (0 : EuclideanSpace ℂ I) 1).exists_bound_of_continuousOn hE
  have hmem : ∀ y, nz u0 y ∈ Metric.sphere (0 : EuclideanSpace ℂ I) 1 := fun y => by
    rw [mem_sphere_zero_iff_norm]; exact nz_mem u0 hu0 y
  rw [continuous_iff_continuousAt]
  intro y0
  by_cases h0 : y0 = 0
  · subst h0
    have hs0 : sc E u0 0 = 0 := by simp [sc]
    rw [ContinuousAt, hs0]
    have hT : Filter.Tendsto (fun y : I → ℂ => C * ‖WithLp.toLp 2 y‖ ^ 2) (nhds 0) (nhds 0) := by
      have : Continuous (fun y : I → ℂ => C * ‖WithLp.toLp 2 y‖ ^ 2) := by fun_prop
      simpa using this.tendsto 0
    refine squeeze_zero_norm (fun y => ?_) hT
    calc ‖sc E u0 y‖ = ‖WithLp.toLp 2 y‖ ^ 2 * ‖E (nz u0 y)‖ := by
          rw [sc, norm_mul, norm_pow, norm_norm]
      _ ≤ ‖WithLp.toLp 2 y‖ ^ 2 * C := mul_le_mul_of_nonneg_left (hC _ (hmem y)) (by positivity)
      _ = C * ‖WithLp.toLp 2 y‖ ^ 2 := mul_comm _ _
  · have hnzeq : (fun y : I → ℂ => ((‖WithLp.toLp 2 y‖ : ℂ)⁻¹) • WithLp.toLp 2 y)
        =ᶠ[nhds y0] nz u0 := by
      filter_upwards [(isClosed_singleton (x := (0 : I → ℂ))).isOpen_compl.mem_nhds
        (by simpa using h0)] with y hy
      have hy' : y ≠ 0 := by simpa using hy
      simp [nz, hy']
    have hne : (‖WithLp.toLp 2 y0‖ : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero, norm_ne_zero_iff]
      intro h'
      exact h0 (by simpa using congrArg WithLp.ofLp h')
    have hc1 : Continuous (fun y : I → ℂ => (‖WithLp.toLp 2 y‖ : ℂ)) := by fun_prop
    have hg : ContinuousAt (fun y : I → ℂ => ((‖WithLp.toLp 2 y‖ : ℂ)⁻¹) • WithLp.toLp 2 y) y0 :=
      (hc1.continuousAt.inv₀ hne).smul (PiLp.continuous_toLp 2 _).continuousAt
    have hnz : ContinuousAt (nz u0) y0 := hg.congr hnzeq
    have hEc : ContinuousAt (fun y => E (nz u0 y)) y0 :=
      (hE.continuousWithinAt (hmem y0)).tendsto.comp
        (tendsto_nhdsWithin_iff.mpr ⟨hnz.tendsto, Filter.Eventually.of_forall hmem⟩)
    have hn2 : Continuous (fun y : I → ℂ => ‖WithLp.toLp 2 y‖ ^ 2) := by fun_prop
    exact hn2.continuousAt.mul hEc

theorem roof_bdd (E : EuclideanSpace ℂ I → ℝ) (C : ℝ)
    (hC : ∀ v ∈ Metric.sphere (0 : EuclideanSpace ℂ I) 1, ‖E v‖ ≤ C) (ρ : Matrix I I ℂ) :
    ∀ r ∈ {r | ∃ e : PureEnsemble I, pureAverage e = ρ ∧ r = ∑ x, e.prob x * E (e.vector x)},
      -C ≤ r ∧ r ≤ C := by
  rintro r ⟨e, -, rfl⟩
  have hb : ∀ x, -C ≤ E (e.vector x) ∧ E (e.vector x) ≤ C := fun x => by
    have := hC (e.vector x) (by rw [mem_sphere_zero_iff_norm]; exact e.normalized x)
    rw [Real.norm_eq_abs, abs_le] at this
    exact this
  have h1 : ∑ x, e.prob x * (-C) = -C := by rw [← Finset.sum_mul, e.total, one_mul]
  have h2 : ∑ x, e.prob x * C = C := by rw [← Finset.sum_mul, e.total, one_mul]
  constructor
  · rw [← h1]
    exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hb x).1 (e.nonneg x)
  · rw [← h2]
    exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hb x).2 (e.nonneg x)

theorem vecMulVec_mulVec_self (M : Matrix I I ℂ) (w : I → ℂ) :
    Matrix.vecMulVec (M *ᵥ w) (star (M *ᵥ w)) = M * Matrix.vecMulVec w (star w) * Mᴴ := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

theorem vecs_zero {ι : Type} [Fintype ι] (w : ι → I → ℂ)
    (h : ∑ x, Matrix.vecMulVec (w x) (star (w x)) = 0) : ∀ x, w x = 0 := by
  have ht := congrArg (fun M => (Matrix.trace M).re) h
  simp only [Matrix.trace_sum, Complex.re_sum, trace_vecMulVec_self, Complex.ofReal_re,
    Matrix.trace_zero, Complex.zero_re] at ht
  intro x
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => by positivity)).mp ht x
    (Finset.mem_univ x)
  funext i
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).mp h1 i
    (Finset.mem_univ i)
  simpa using h2

theorem psd_decomp {ρ : Matrix I I ℂ} (hρ : ρ.PosSemidef) :
    ρ = ∑ k, Matrix.vecMulVec (fun i => cfc Real.sqrt ρ i k)
      (star fun i => cfc Real.sqrt ρ i k) := by
  rw [← mul_conjTranspose_eq_sum, sqrt_herm, sqrt_mul_sqrt hρ]

theorem roof_usc [Nonempty I] (E : EuclideanSpace ℂ I → ℝ)
    (hE : ContinuousOn E (Metric.sphere 0 1)) :
    UpperSemicontinuousOn (pureRoof E) {ρ : Matrix I I ℂ | IsDensityMatrix ρ} := by
  obtain ⟨C, hC⟩ :=
    (isCompact_sphere (0 : EuclideanSpace ℂ I) 1).exists_bound_of_continuousOn hE
  let u0 : EuclideanSpace ℂ I := EuclideanSpace.single (Classical.arbitrary I) 1
  have hu0 : ‖u0‖ = 1 := by simp [u0]
  have hsc := sc_cont E u0 hu0 hE
  have hbdd : ∀ ρ : Matrix I I ℂ, BddBelow {r | ∃ e : PureEnsemble I, pureAverage e = ρ ∧
      r = ∑ x, e.prob x * E (e.vector x)} :=
    fun ρ => ⟨-C, fun r hr => (roof_bdd E C hC ρ r hr).1⟩
  intro ρ0 hρ0 y hy
  have hA : IsSelfAdjoint ρ0 := hρ0.1.isHermitian
  have hfin : (spectrum ℝ ρ0).Finite := Matrix.finite_real_spectrum
  have hnn : ∀ t ∈ spectrum ℝ ρ0, 0 ≤ t := fun t ht => ((dens_spec hρ0).2 ht).1
  have hne : {r | ∃ e : PureEnsemble I, pureAverage e = ρ0 ∧
      r = ∑ x, e.prob x * E (e.vector x)}.Nonempty := by
    obtain ⟨e, he, -⟩ := ens_of_vecs E u0 hu0 _ ρ0 (psd_decomp hρ0.1) hρ0.2
    exact ⟨_, e, he, rfl⟩
  obtain ⟨r, ⟨e0, he0, rfl⟩, hr⟩ := exists_lt_of_csInf_lt hne hy
  -- vectors of the near-optimal decomposition
  let yv : Fin e0.size → I → ℂ := fun x i => (Real.sqrt (e0.prob x) : ℂ) * e0.vector x i
  have hyv_toLp : ∀ x, WithLp.toLp 2 (yv x) = (Real.sqrt (e0.prob x) : ℂ) • e0.vector x := by
    intro x; ext i; simp [yv]
  have hy_sc : ∀ x, sc E u0 (yv x) = e0.prob x * E (e0.vector x) := by
    intro x
    have hn : ‖WithLp.toLp 2 (yv x)‖ = Real.sqrt (e0.prob x) := by
      rw [hyv_toLp, norm_smul, e0.normalized x, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    by_cases hp : e0.prob x = 0
    · have : yv x = 0 := by funext i; simp [yv, hp]
      rw [this, hp]; simp [sc]
    · have hpos : 0 < Real.sqrt (e0.prob x) := Real.sqrt_pos.mpr (lt_of_le_of_ne (e0.nonneg x) (Ne.symm hp))
      have hyne : yv x ≠ 0 := by
        intro h0
        have : ‖WithLp.toLp 2 (yv x)‖ = 0 := by rw [h0]; simp
        rw [hn] at this; linarith
      rw [sc, hn, Real.sq_sqrt (e0.nonneg x)]
      congr 2
      rw [nz, if_neg hyne, hn, hyv_toLp, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hpos.ne'),
        one_smul]
  have hy_dec : ρ0 = ∑ x, Matrix.vecMulVec (yv x) (star (yv x)) := by
    rw [← he0, pureAverage]
    refine Finset.sum_congr rfl fun x _ => ?_
    ext a b
    simp only [pureDensity, Matrix.smul_apply, Matrix.of_apply, Matrix.vecMulVec_apply, yv,
      Pi.star_apply, RCLike.star_def, map_mul, Complex.conj_ofReal, Complex.real_smul]
    have : ((Real.sqrt (e0.prob x) : ℝ) : ℂ) * (Real.sqrt (e0.prob x) : ℂ) = (e0.prob x : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (e0.nonneg x)]
    rw [← this]; ring
  -- spectral matrices of ρ0
  have cm : ∀ f g : ℝ → ℝ, cfc f ρ0 * cfc g ρ0 = cfc (fun t => f t * g t) ρ0 :=
    fun f g => (cfc_mul f g ρ0 (hfin.continuousOn _) (hfin.continuousOn _)).symm
  have ca : ∀ f g : ℝ → ℝ, cfc f ρ0 + cfc g ρ0 = cfc (fun t => f t + g t) ρ0 :=
    fun f g => (cfc_add ρ0 f g (hfin.continuousOn _) (hfin.continuousOn _)).symm
  have hid : cfc (fun t : ℝ => t) ρ0 = ρ0 := cfc_id' ℝ ρ0
  set Pp := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) ρ0 with hPp
  set Q := cfc (fun t : ℝ => if t = 0 then (1 : ℝ) else 0) ρ0 with hQ
  set R0 := cfc Real.sqrt ρ0 with hR0
  have hPpH : Ppᴴ = Pp := (cfc_predicate _ ρ0 : IsSelfAdjoint Pp)
  have hQH : Qᴴ = Q := (cfc_predicate _ ρ0 : IsSelfAdjoint Q)
  have F1 : Pp * ρ0 * Pp + Q = 1 := by
    rw [← hid, hPp, hQ, cm, cm, ca, ← cfc_const_one ℝ ρ0]
    refine cfc_congr fun t ht => ?_
    rcases (hnn t ht).eq_or_lt with h | h
    · subst h; simp
    · have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr h).ne'
      have h3 : (Real.sqrt t)⁻¹ * t * (Real.sqrt t)⁻¹ = (Real.sqrt t * Real.sqrt t)⁻¹ * t := by ring
      rw [if_neg h.ne', add_zero, h3, Real.mul_self_sqrt h.le, inv_mul_cancel₀ h.ne']
  have F2 : Q * ρ0 * Q = 0 := by
    rw [← hid, hQ, cm, cm, ← cfc_zero ℝ ρ0]
    refine cfc_congr fun t ht => ?_
    by_cases h : t = 0 <;> simp [h]
  have F3 : R0 * Q * R0 = 0 := by
    rw [hQ, hR0, cm, cm, ← cfc_zero ℝ ρ0]
    refine cfc_congr fun t ht => ?_
    by_cases h : t = 0 <;> simp [h]
  have F4 : R0 * Pp = 1 - Q := by
    rw [hR0, hPp, hQ, cm, ← cfc_const_one ℝ ρ0, ← cfc_sub (fun _ => (1 : ℝ)) _ ρ0 (hfin.continuousOn _)
      (hfin.continuousOn _)]
    refine cfc_congr fun t ht => ?_
    rcases (hnn t ht).eq_or_lt with h | h
    · subst h; simp
    · have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr h).ne'
      rw [if_neg h.ne', mul_inv_cancel₀ hs]; simp
  have F5 : Q * Q = Q := by
    rw [hQ, cm]
    refine cfc_congr fun t ht => ?_
    by_cases h : t = 0 <;> simp [h]
  -- the kernel part kills the decomposition vectors
  have hQy : ∀ x, Q *ᵥ yv x = 0 := by
    apply vecs_zero
    simp_rw [vecMulVec_mulVec_self]
    rw [← Finset.sum_mul, ← Finset.mul_sum, ← hy_dec, hQH, F2]
  let q : I → I → ℂ := fun j i => Q i j
  have hq_dec : ∑ j, Matrix.vecMulVec (q j) (star (q j)) = Q := by
    rw [← mul_conjTranspose_eq_sum, hQH, F5]
  have hR0q : ∀ j, R0 *ᵥ q j = 0 := by
    apply vecs_zero
    simp_rw [vecMulVec_mulVec_self]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hq_dec, hR0, sqrt_herm, ← hR0, F3]
  -- the perturbed decomposition
  let z : Matrix I I ℂ → Fin e0.size ⊕ I → I → ℂ := fun ρ s =>
    match s with
    | Sum.inl x => cfc Real.sqrt ρ *ᵥ (Pp *ᵥ yv x)
    | Sum.inr j => cfc Real.sqrt ρ *ᵥ q j
  have hz_dec : ∀ ρ : Matrix I I ℂ, ρ.PosSemidef →
      ρ = ∑ s, Matrix.vecMulVec (z ρ s) (star (z ρ s)) := by
    intro ρ hρ
    rw [Fintype.sum_sum_type]
    simp only [z]
    simp_rw [vecMulVec_mulVec_self]
    rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum,
      ← Finset.sum_mul, ← Finset.mul_sum, ← hy_dec, hq_dec, ← add_mul, ← mul_add, hPpH, F1,
      mul_one, sqrt_herm, sqrt_mul_sqrt hρ]
  let V : Matrix I I ℂ → ℝ := fun ρ => ∑ s, sc E u0 (z ρ s)
  have hV0 : V ρ0 = ∑ x, e0.prob x * E (e0.vector x) := by
    simp only [V, z, Fintype.sum_sum_type]
    rw [← hR0]
    have h1 : ∀ x, R0 *ᵥ (Pp *ᵥ yv x) = yv x := by
      intro x
      rw [Matrix.mulVec_mulVec, F4, Matrix.sub_mulVec, hQy, Matrix.one_mulVec, sub_zero]
    simp_rw [h1, hR0q, hy_sc]
    simp [sc]
  have hVc : ContinuousWithinAt V {ρ : Matrix I I ℂ | IsDensityMatrix ρ} ρ0 := by
    have hR : ContinuousWithinAt (fun ρ : Matrix I I ℂ => cfc Real.sqrt ρ)
        {ρ : Matrix I I ℂ | IsDensityMatrix ρ} ρ0 :=
      cfc_contOn_dens Real.sqrt Real.continuous_sqrt.continuousOn ρ0 hρ0
    have hW : Continuous (fun R : Matrix I I ℂ => ∑ s : Fin e0.size ⊕ I, sc E u0
        (match s with
          | Sum.inl x => R *ᵥ (Pp *ᵥ yv x)
          | Sum.inr j => R *ᵥ q j)) := by
      refine continuous_finset_sum _ (fun s _ => hsc.comp ?_)
      rcases s with x | j
      · exact Continuous.matrix_mulVec continuous_id continuous_const
      · exact Continuous.matrix_mulVec continuous_id continuous_const
    exact hW.continuousAt.comp_continuousWithinAt hR
  have hev : ∀ᶠ ρ in nhdsWithin ρ0 {ρ : Matrix I I ℂ | IsDensityMatrix ρ}, V ρ < y :=
    Filter.Tendsto.eventually_lt_const (by rw [hV0]; exact hr) hVc.tendsto
  filter_upwards [hev, self_mem_nhdsWithin] with ρ hV hρ
  obtain ⟨e, he, hval⟩ := ens_of_vecs E u0 hu0 (z ρ) ρ (hz_dec ρ hρ.1) hρ.2
  exact lt_of_le_of_lt (csInf_le (hbdd ρ) ⟨e, he, hval.symm ▸ rfl⟩) hV

end P08Aux

namespace P08B
open P08Aux

theorem kraus_psd {J ι κ : Type} [Fintype J] [Fintype ι] [Fintype κ] (K : J → Matrix κ ι ℂ)
    {X : Matrix ι ι ℂ} (hX : X.PosSemidef) : (krausApply K X).PosSemidef := by
  unfold krausApply
  exact Matrix.posSemidef_sum _ fun j _ => hX.mul_mul_conjTranspose_same (K j)

theorem kraus_trace {J ι κ : Type} [Fintype J] [Fintype ι] [Fintype κ] [DecidableEq ι]
    (K : J → Matrix κ ι ℂ) (hK : ∑ j, (K j)ᴴ * K j = 1) (X : Matrix ι ι ℂ) :
    (krausApply K X).trace = X.trace := by
  unfold krausApply
  have h : ∀ j, (K j * X * (K j)ᴴ).trace = (X * ((K j)ᴴ * K j)).trace := fun j => by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  rw [Matrix.trace_sum]
  simp_rw [h]
  rw [← Matrix.trace_sum, ← Finset.mul_sum, hK, Matrix.mul_one]

theorem kraus_dens {J ι κ : Type} [Fintype J] [Fintype ι] [Fintype κ] [DecidableEq ι]
    (K : J → Matrix κ ι ℂ) (hK : ∑ j, (K j)ᴴ * K j = 1) {X : Matrix ι ι ℂ}
    (hX : IsDensityMatrix X) : IsDensityMatrix (krausApply K X) :=
  ⟨kraus_psd K hX.1, (kraus_trace K hK X).trans hX.2⟩

theorem kraus_cont {J ι κ : Type} [Fintype J] [Fintype ι] [Fintype κ]
    (K : J → Matrix κ ι ℂ) : Continuous (krausApply K) := by
  unfold krausApply
  exact continuous_finsetSum _ fun j _ =>
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)

theorem idTensor_kraus {R J ι κ : Type} [Fintype R] [DecidableEq R] [Fintype J] [Fintype ι]
    [Fintype κ] (K : J → Matrix κ ι ℂ) (X : Matrix (R × ι) (R × ι) ℂ) :
    idTensorSuperop (R := R) (krausApply K) X =
      krausApply (fun j => Matrix.kroneckerMap (· * ·) (1 : Matrix R R ℂ) (K j)) X := by
  ext ⟨r, k⟩ ⟨r', k'⟩
  simp only [idTensorSuperop, krausApply, Matrix.of_apply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.kronecker_apply, Fintype.sum_prod_type, Matrix.one_apply]
  simp
  simp only [apply_ite (starRingEnd ℂ), map_zero, mul_ite, mul_zero, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem kron_kraus {R J ι κ : Type} [Fintype R] [DecidableEq R] [Fintype J] [Fintype ι]
    [Fintype κ] [DecidableEq ι] (K : J → Matrix κ ι ℂ) (hK : ∑ j, (K j)ᴴ * K j = 1) :
    ∑ j, (Matrix.kroneckerMap (· * ·) (1 : Matrix R R ℂ) (K j))ᴴ * Matrix.kroneckerMap (· * ·) (1 : Matrix R R ℂ) (K j)
      = 1 := by
  simp_rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul]
  ext ⟨r, k⟩ ⟨r', k'⟩
  have h2 := congrArg (fun M => M k k') hK
  simp only [Matrix.sum_apply] at h2
  rw [Matrix.sum_apply]
  simp only [Matrix.kronecker_apply]
  rw [← Finset.mul_sum, h2]
  by_cases h1 : r = r' <;> by_cases h3 : k = k' <;> simp [Matrix.one_apply, h1, h3]

theorem pure_dens {ι : Type} [Fintype ι] [DecidableEq ι] (v : EuclideanSpace ℂ ι)
    (hv : ‖v‖ = 1) : IsDensityMatrix (pureDensity v) := by
  rw [pureDensity_eq_vecMulVec]
  refine ⟨Matrix.posSemidef_vecMulVec_self_star _, ?_⟩
  rw [trace_vecMulVec_self, ← EuclideanSpace.norm_sq_eq, hv]
  simp

theorem traceRight_pure {A B : Type} [Fintype A] [Fintype B] (v : EuclideanSpace ℂ (A × B)) :
    traceRight (pureDensity v) =
      (Matrix.of fun j h => v (j, h)) * (Matrix.of fun j h => v (j, h))ᴴ := by
  ext j k
  simp [traceRight, pureDensity, Matrix.mul_apply]

theorem traceRight_pure_dens {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (v : EuclideanSpace ℂ (A × B)) (hv : ‖v‖ = 1) : IsDensityMatrix (traceRight (pureDensity v)) := by
  have h1 := pure_dens v hv
  refine ⟨?_, ?_⟩
  · rw [traceRight_pure]; exact Matrix.posSemidef_self_mul_conjTranspose _
  · rw [← h1.2]; simp [Matrix.trace, traceRight, Fintype.sum_prod_type]

theorem traceRight_pure_cont {A B : Type} [Fintype A] [Fintype B] :
    Continuous (fun v : EuclideanSpace ℂ (A × B) => traceRight (pureDensity v)) := by
  have hM : Continuous (fun v : EuclideanSpace ℂ (A × B) => (Matrix.of fun j h => v (j, h))) :=
    continuous_matrix fun j h => (EuclideanSpace.proj (𝕜 := ℂ) (j, h)).continuous
  have : (fun v : EuclideanSpace ℂ (A × B) => traceRight (pureDensity v)) =
      fun v => (Matrix.of fun j h => v (j, h)) * (Matrix.of fun j h => v (j, h))ᴴ := by
    funext v; exact traceRight_pure v
  rw [this]
  exact hM.matrix_mul hM.matrix_conjTranspose

theorem vn_contOn {ι : Type} [Fintype ι] [DecidableEq ι] :
    ContinuousOn (fun ρ : Matrix ι ι ℂ => vnEntropy ρ) {ρ | IsDensityMatrix ρ} := by
  have hf : ContinuousOn (fun x : ℝ => x * Real.logb 2 x) (Set.Icc 0 1) := by
    have : (fun x : ℝ => x * Real.logb 2 x) = fun x => x * Real.log x / Real.log 2 := by
      funext x; rw [Real.logb, mul_div_assoc]
    rw [this]
    exact (Real.continuous_mul_log.div_const _).continuousOn
  exact (trace_cfc_contOn_dens _ hf).neg

theorem EF_cont {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] :
    ContinuousOn (fun v : EuclideanSpace ℂ (A × B) => vnEntropy (traceRight (pureDensity v)))
      (Metric.sphere 0 1) :=
  vn_contOn.comp traceRight_pure_cont.continuousOn fun v hv =>
    traceRight_pure_dens v (by simpa using hv)

theorem canon_dens {A : Type} [Fintype A] [DecidableEq A] {τ : Matrix A A ℂ}
    (hτ : IsDensityMatrix τ) : IsDensityMatrix (pureDensity (canonicalPurification τ)) := by
  refine ⟨by rw [pureDensity_eq_vecMulVec]; exact Matrix.posSemidef_vecMulVec_self_star _, ?_⟩
  have h : (cfc Real.sqrt τ * (cfc Real.sqrt τ)ᴴ).trace = 1 := by
    rw [sqrt_herm, sqrt_mul_sqrt hτ.1, hτ.2]
  rw [← h]
  simp only [Matrix.trace, Matrix.diag, pureDensity, canonicalPurification, Matrix.of_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type, PiLp.toLp_apply,
    RCLike.star_def]
  exact Finset.sum_comm

theorem canon_cont {A : Type} [Fintype A] [DecidableEq A] :
    ContinuousOn (fun τ : Matrix A A ℂ => pureDensity (canonicalPurification τ))
      {τ | IsDensityMatrix τ} := by
  let g : Matrix A A ℂ → Matrix (A × A) (A × A) ℂ :=
    fun S => Matrix.of fun p q => S p.2 p.1 * (starRingEnd ℂ) (S q.2 q.1)
  have hg : Continuous g := continuous_matrix fun p q =>
    (continuous_id.matrix_elem p.2 p.1).mul
      (Complex.continuous_conj.comp (continuous_id.matrix_elem q.2 q.1))
  have : (fun τ : Matrix A A ℂ => pureDensity (canonicalPurification τ)) =
      g ∘ fun τ => cfc Real.sqrt τ := by
    funext τ; ext p q; simp [pureDensity, canonicalPurification, g]
  rw [this]
  exact hg.comp_continuousOn (cfc_contOn_dens _ Real.continuous_sqrt.continuousOn)

theorem usc_comp {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {f : Y → ℝ} {g : X → Y}
    {s : Set X} {t : Set Y} (hf : UpperSemicontinuousOn f t) (hg : ContinuousOn g s)
    (hst : Set.MapsTo g s t) : UpperSemicontinuousOn (f ∘ g) s := by
  intro x hx y hy
  exact ((hg x hx).tendsto_nhdsWithin hst).eventually (hf (g x) (hst hx) y hy)

theorem roof_abs {ι : Type} [Fintype ι] [DecidableEq ι] (E : EuclideanSpace ℂ ι → ℝ)
    (hE : ContinuousOn E (Metric.sphere 0 1)) : ∃ C, ∀ ρ, |pureRoof E ρ| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : EuclideanSpace ℂ ι) 1).exists_bound_of_continuousOn hE
  refine ⟨max C 0, fun ρ => ?_⟩
  have hb := roof_bdd E C hC ρ
  unfold pureRoof
  rcases Set.eq_empty_or_nonempty {r | ∃ e : PureEnsemble ι, pureAverage e = ρ ∧
      r = ∑ x, e.prob x * E (e.vector x)} with h | h
  · rw [h, Real.sInf_empty]; simp
  · rw [abs_le]; constructor
    · have := le_csInf h fun r hr => (hb r hr).1
      linarith [le_max_left C 0]
    · obtain ⟨r, hr⟩ := h
      have := csInf_le ⟨-C, fun r hr => (hb r hr).1⟩ hr
      linarith [(hb r hr).2, le_max_left C 0]

theorem form_usc {A B J : Type} [Fintype A] [Fintype B] [Fintype J] [DecidableEq A]
    [DecidableEq B] [Nonempty A] [Nonempty B] (K : J → Matrix B A ℂ)
    (hK : ∑ j, (K j)ᴴ * K j = 1) :
    UpperSemicontinuousOn (channelFormation (krausApply K)) {τ : Matrix A A ℂ | IsDensityMatrix τ}
      ∧ ∃ C, ∀ τ, |channelFormation (krausApply K) τ| ≤ C := by
  let E : EuclideanSpace ℂ (A × B) → ℝ := fun v => vnEntropy (traceRight (pureDensity v))
  let σ : Matrix A A ℂ → Matrix (A × B) (A × B) ℂ := fun τ =>
    krausApply (fun j => Matrix.kroneckerMap (· * ·) (1 : Matrix A A ℂ) (K j))
      (pureDensity (canonicalPurification τ))
  have hf : channelFormation (krausApply K) = pureRoof E ∘ σ := by
    funext τ
    simp only [Function.comp, σ, channelFormation, formation, E]
    rw [idTensor_kraus]
  have hσc : ContinuousOn σ {τ : Matrix A A ℂ | IsDensityMatrix τ} :=
    (kraus_cont _).comp_continuousOn canon_cont
  have hσm : Set.MapsTo σ {τ : Matrix A A ℂ | IsDensityMatrix τ}
      {ρ : Matrix (A × B) (A × B) ℂ | IsDensityMatrix ρ} := fun τ hτ =>
    kraus_dens _ (kron_kraus K hK) (canon_dens hτ)
  refine ⟨?_, ?_⟩
  · rw [hf]; exact usc_comp (roof_usc E EF_cont) hσc hσm
  · obtain ⟨C, hC⟩ := roof_abs E EF_cont
    exact ⟨C, fun τ => by rw [hf]; exact hC _⟩

theorem trace_mul_ct {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ) :
    (M * Mᴴ).trace = ((∑ i, ∑ j, ‖M i j‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem dens_compact {ι : Type} [Fintype ι] [DecidableEq ι] :
    IsCompact {ρ : Matrix ι ι ℂ | IsDensityMatrix ρ} := by
  let T : Set (Matrix ι ι ℂ) := {M | ∑ i, ∑ j, ‖M i j‖ ^ 2 = 1}
  have hT : IsCompact T := by
    have hK : IsCompact (Set.univ.pi fun _ : ι => Set.univ.pi fun _ : ι =>
        Metric.closedBall (0 : ℂ) 1) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
    refine hK.of_isClosed_subset (isClosed_eq ?_ continuous_const) ?_
    · exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        ((continuous_id.matrix_elem i j).norm.pow 2)
    · intro M hM i _ j _
      simp only [Metric.mem_closedBall, dist_zero_right]
      have hM' : ∑ i, ∑ j, ‖M i j‖ ^ 2 = 1 := hM
      have h1 : ‖M i j‖ ^ 2 ≤ 1 := by
        rw [← hM']
        exact (Finset.single_le_sum (f := fun j => ‖M i j‖ ^ 2) (fun j _ => by positivity)
          (Finset.mem_univ j)).trans (Finset.single_le_sum
            (f := fun i => ∑ j, ‖M i j‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ i))
      nlinarith [norm_nonneg (M i j)]
  have hD : {ρ : Matrix ι ι ℂ | IsDensityMatrix ρ} = (fun M => M * Mᴴ) '' T := by
    ext ρ; constructor
    · intro hρ
      refine ⟨cfc Real.sqrt ρ, ?_, by simp only; rw [sqrt_herm, sqrt_mul_sqrt hρ.1]⟩
      have h := trace_mul_ct (cfc Real.sqrt ρ)
      rw [sqrt_herm, sqrt_mul_sqrt hρ.1, hρ.2] at h
      show ∑ i, ∑ j, ‖cfc Real.sqrt ρ i j‖ ^ 2 = 1
      exact_mod_cast h.symm
    · rintro ⟨M, hM, rfl⟩
      refine ⟨Matrix.posSemidef_self_mul_conjTranspose M, ?_⟩
      have hM' : ∑ i, ∑ j, ‖M i j‖ ^ 2 = 1 := hM
      rw [trace_mul_ct, hM']; simp
  rw [hD]
  exact hT.image (continuous_id.matrix_mul continuous_id.matrix_conjTranspose)

end P08B

namespace P08C
open P08Aux P08B

theorem dep_vec {a n : ℕ} (hn : a ^ 2 < n) (τ : Fin n → Matrix (Fin a) (Fin a) ℂ)
    (hτ : ∀ x, IsDensityMatrix (τ x)) (g : Matrix (Fin a) (Fin a) ℂ → ℝ) :
    ∃ c : Fin n → ℝ, c ≠ 0 ∧ ∑ x, c x = 0 ∧ ∑ x, c x • τ x = 0 ∧
      0 ≤ ∑ x, c x * g (τ x) := by
  let ψ : Matrix (Fin a) (Fin a) ℂ → (Fin a × Fin a → ℝ) := fun M ij =>
    if ij.1 ≤ ij.2 then (M ij.1 ij.2).re else (M ij.2 ij.1).im
  let Φ : (Fin n → ℝ) →ₗ[ℝ] (Fin a × Fin a → ℝ) :=
    { toFun := fun c => ∑ x, c x • ψ (τ x)
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r c => by simp [Finset.smul_sum, smul_smul] }
  have hrank : Module.finrank ℝ (Fin a × Fin a → ℝ) < Module.finrank ℝ (Fin n → ℝ) := by
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin]
    rw [← sq]; exact hn
  obtain ⟨c, hcK, hc0⟩ := (Submodule.ne_bot_iff _).mp (LinearMap.ker_ne_bot_of_finrank_lt (f := Φ) hrank)
  have hΦ : ∀ ij : Fin a × Fin a, ∑ x, c x * ψ (τ x) ij = 0 := by
    intro ij
    have h0 : (∑ x, c x • ψ (τ x)) = 0 := LinearMap.mem_ker.mp hcK
    have := congrFun h0 ij
    simpa [Finset.sum_apply] using this
  have hre : ∀ x i j, (τ x i j).re = (τ x j i).re := fun x i j => by
    rw [← (hτ x).1.isHermitian.apply i j]; simp
  have him : ∀ x i j, (τ x i j).im = -(τ x j i).im := fun x i j => by
    rw [← (hτ x).1.isHermitian.apply i j]; simp
  have hR : ∀ i j, ∑ x, c x * (τ x i j).re = 0 := by
    intro i j
    rcases le_total i j with h | h
    · simpa [ψ, h] using hΦ (i, j)
    · calc ∑ x, c x * (τ x i j).re = ∑ x, c x * (τ x j i).re :=
            Finset.sum_congr rfl fun x _ => by rw [hre x i j]
        _ = 0 := by simpa [ψ, h] using hΦ (j, i)
  have hI : ∀ i j, ∑ x, c x * (τ x i j).im = 0 := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · simpa [ψ, not_le.mpr h] using hΦ (j, i)
    · have : ∀ x, (τ x i i).im = 0 := fun x => by linarith [him x i i]
      simp [this]
    · have h2 : ∑ x, c x * (τ x j i).im = 0 := by simpa [ψ, not_le.mpr h] using hΦ (i, j)
      calc ∑ x, c x * (τ x i j).im = -∑ x, c x * (τ x j i).im := by
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun x _ => by rw [him x i j]; ring
        _ = 0 := by rw [h2, neg_zero]
  have hM : ∑ x, c x • τ x = 0 := by
    ext i j
    rw [Matrix.sum_apply, Matrix.zero_apply]
    apply Complex.ext
    · rw [Complex.re_sum]; simpa [Matrix.smul_apply] using hR i j
    · rw [Complex.im_sum]; simpa [Matrix.smul_apply] using hI i j
  have htr : ∀ x, ∑ i, (τ x i i).re = 1 := fun x => by
    have := congrArg Complex.re (hτ x).2
    simpa [Matrix.trace, Complex.re_sum] using this
  have hcs : ∑ x, c x = 0 := by
    have h0 : ∑ i, ∑ x, c x * (τ x i i).re = 0 := Finset.sum_eq_zero fun i _ => hR i i
    rw [Finset.sum_comm] at h0
    simpa [← Finset.mul_sum, htr] using h0
  by_cases hg : 0 ≤ ∑ x, c x * g (τ x)
  · exact ⟨c, hc0, hcs, hM, hg⟩
  · refine ⟨-c, neg_ne_zero.mpr hc0, ?_, ?_, ?_⟩
    · simp [Finset.sum_neg_distrib, hcs]
    · simp [neg_smul, Finset.sum_neg_distrib, hM]
    · simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]; linarith

theorem red_raw {a n : ℕ} (hn : a ^ 2 < n + 1) (p : Fin (n + 1) → ℝ)
    (τ : Fin (n + 1) → Matrix (Fin a) (Fin a) ℂ) (hp : ∀ x, 0 ≤ p x)
    (hτ : ∀ x, IsDensityMatrix (τ x)) (g : Matrix (Fin a) (Fin a) ℂ → ℝ) :
    ∃ q : Fin n → ℝ, ∃ σ : Fin n → Matrix (Fin a) (Fin a) ℂ, (∀ x, 0 ≤ q x) ∧
      (∀ x, IsDensityMatrix (σ x)) ∧ ∑ x, q x = ∑ x, p x ∧
      ∑ x, q x • σ x = ∑ x, p x • τ x ∧ ∑ x, p x * g (τ x) ≤ ∑ x, q x * g (σ x) := by
  obtain ⟨c, hc0, hcs, hcτ, hcg⟩ := dep_vec hn τ hτ g
  have hneg : ∃ x, c x < 0 := by
    by_contra h
    push Not at h
    apply hc0
    funext x
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => h x)).mp hcs x (Finset.mem_univ x)
  obtain ⟨x1, hx1⟩ := hneg
  obtain ⟨x0, hx0S, hx0min⟩ := Finset.exists_min_image (Finset.univ.filter fun x => c x < 0)
    (fun x => p x / (-c x)) ⟨x1, by simp [hx1]⟩
  have hcx0 : c x0 < 0 := by simpa using hx0S
  set t := p x0 / (-c x0) with ht
  have ht0 : 0 ≤ t := div_nonneg (hp x0) (by linarith)
  let p' : Fin (n + 1) → ℝ := fun x => p x + t * c x
  have hp'0 : ∀ x, 0 ≤ p' x := by
    intro x
    by_cases hx : c x < 0
    · have h1 := hx0min x (by simp [hx])
      have h2 : t * (-c x) ≤ p x := (le_div_iff₀ (by linarith)).mp h1
      simp only [p']; linarith
    · push Not at hx
      simp only [p']; nlinarith [hp x, mul_nonneg ht0 hx]
  have hp'x0 : p' x0 = 0 := by
    have hne : c x0 ≠ 0 := hcx0.ne
    have : t * c x0 = -p x0 := by
      rw [ht, div_mul_eq_mul_div, div_eq_iff (neg_ne_zero.mpr hne)]; ring
    simp only [p']; rw [this]; ring
  refine ⟨fun i => p' (x0.succAbove i), fun i => τ (x0.succAbove i), fun i => hp'0 _,
    fun i => hτ _, ?_, ?_, ?_⟩
  · have h := Fin.sum_univ_succAbove p' x0
    rw [hp'x0, zero_add] at h
    rw [← h]
    simp only [p', Finset.sum_add_distrib, ← Finset.mul_sum, hcs, mul_zero, add_zero]
  · have h := Fin.sum_univ_succAbove (fun x => p' x • τ x) x0
    simp only [hp'x0, zero_smul, zero_add] at h
    rw [← h]
    simp only [p', add_smul, Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum, hcτ, smul_zero,
      add_zero]
  · have h := Fin.sum_univ_succAbove (fun x => p' x * g (τ x)) x0
    simp only [hp'x0, zero_mul, zero_add] at h
    rw [← h]
    simp only [p', add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    nlinarith

theorem red_step {a : ℕ} (g : Matrix (Fin a) (Fin a) ℂ → ℝ) (e : Ensemble (Fin a))
    (hn : a ^ 2 < e.size) : ∃ e' : Ensemble (Fin a), e'.size + 1 = e.size ∧
      ensembleAverage e' = ensembleAverage e ∧
      ∑ x, e.prob x * g (e.state x) ≤ ∑ x, e'.prob x * g (e'.state x) := by
  rcases e with ⟨size, prob, state, nonneg, total, density⟩
  cases size with
  | zero => exact absurd hn (Nat.not_lt_zero _)
  | succ n =>
    obtain ⟨q, σ, hq, hσ, hqs, hqa, hqg⟩ := red_raw hn prob state nonneg density g
    exact ⟨⟨n, q, σ, hq, hqs.trans total, hσ⟩, rfl, hqa, hqg⟩

theorem red_all {a : ℕ} (g : Matrix (Fin a) (Fin a) ℂ → ℝ) : ∀ n, ∀ e : Ensemble (Fin a),
    e.size ≤ n → ∃ e' : Ensemble (Fin a), e'.size ≤ a ^ 2 ∧
      ensembleAverage e' = ensembleAverage e ∧
      ∑ x, e.prob x * g (e.state x) ≤ ∑ x, e'.prob x * g (e'.state x) := by
  intro n
  induction n with
  | zero => intro e he; exact ⟨e, by omega, rfl, le_rfl⟩
  | succ n ih =>
    intro e he
    by_cases h : e.size ≤ a ^ 2
    · exact ⟨e, h, rfl, le_rfl⟩
    · obtain ⟨e1, h1, h1a, h1g⟩ := red_step g e (by omega)
      obtain ⟨e', h', h'a, h'g⟩ := ih e1 (by omega)
      exact ⟨e', h', h'a.trans h1a, h1g.trans h'g⟩

theorem obj_eq {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (N : Superop A B) (e : Ensemble A) :
    channelObjective N e = vnEntropy (N (ensembleAverage e)) +
      ∑ x, e.prob x * (channelFormation N (e.state x) - vnEntropy (N (e.state x))) := by
  unfold channelObjective outputHolevo
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

theorem reduce {a b : ℕ} [DecidableEq (Fin a)] [DecidableEq (Fin b)]
    (N : Superop (Fin a) (Fin b)) (e : Ensemble (Fin a)) :
    ∃ e' : Ensemble (Fin a), e'.size ≤ a ^ 2 ∧ channelObjective N e ≤ channelObjective N e' := by
  obtain ⟨e', h1, h2, h3⟩ :=
    red_all (fun τ => channelFormation N τ - vnEntropy (N τ)) e.size e le_rfl
  refine ⟨e', h1, ?_⟩
  rw [obj_eq, obj_eq, h2]
  linarith

end P08C

namespace P08D
open P08Aux P08B P08C

theorem usc_mul {Z : Type} [TopologicalSpace Z] {s : Set Z} {p h : Z → ℝ} {C : ℝ}
    (hp : ContinuousOn p s) (hp0 : ∀ z ∈ s, 0 ≤ p z) (hh : UpperSemicontinuousOn h s)
    (hC : ∀ z, |h z| ≤ C) : UpperSemicontinuousOn (fun z => p z * h z) s := by
  intro z0 hz0 y hy
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC z0)
  have hp0' := hp0 z0 hz0
  set δ := y - p z0 * h z0 with hδ
  have hδ0 : 0 < δ := by simp only [hδ]; linarith
  have hε : 0 < δ / (2 * (p z0 + 1)) := div_pos hδ0 (by linarith)
  have e1 := hh z0 hz0 (h z0 + δ / (2 * (p z0 + 1))) (by linarith)
  have e2 : ∀ᶠ z in nhdsWithin z0 s, |p z - p z0| < δ / (2 * (C + 1)) := by
    have := (hp z0 hz0).tendsto
    exact ((Metric.tendsto_nhds.mp this) (δ / (2 * (C + 1))) (div_pos hδ0 (by linarith))).mono fun z hz => by
      rwa [Real.dist_eq] at hz
  filter_upwards [e1, e2] with z h1 h2
  have k1 : p z0 * h z ≤ p z0 * (h z0 + δ / (2 * (p z0 + 1))) :=
    mul_le_mul_of_nonneg_left h1.le hp0'
  have k2 : p z0 * (δ / (2 * (p z0 + 1))) ≤ δ / 2 := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
  have k3 : (p z - p z0) * h z ≤ |p z - p z0| * C := by
    calc (p z - p z0) * h z ≤ |(p z - p z0) * h z| := le_abs_self _
      _ = |p z - p z0| * |h z| := abs_mul _ _
      _ ≤ |p z - p z0| * C := mul_le_mul_of_nonneg_left (hC z) (abs_nonneg _)
  have k4 : |p z - p z0| * C < δ / 2 := by
    rw [lt_div_iff₀ (by linarith)] at h2
    nlinarith [abs_nonneg (p z - p z0)]
  have : p z * h z = p z0 * h z + (p z - p z0) * h z := by ring
  rw [this]
  nlinarith

theorem avg_dens {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq n] {p : ι → ℝ}
    {τ : ι → Matrix n n ℂ} (hp : ∀ x, 0 ≤ p x) (h1 : ∑ x, p x = 1)
    (hτ : ∀ x, IsDensityMatrix (τ x)) : IsDensityMatrix (∑ x, p x • τ x) := by
  refine ⟨Matrix.posSemidef_sum _ fun x _ => ?_, ?_⟩
  · rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact (hτ x).1.smul (Complex.zero_le_real.mpr (hp x))
  · rw [Matrix.trace_sum, Finset.sum_congr rfl (g := fun x => p x • (1 : ℂ))
      fun x _ => by rw [Matrix.trace_smul, (hτ x).2]]
    simp only [Complex.real_smul, mul_one]
    rw [← Complex.ofReal_sum, h1, Complex.ofReal_one]

theorem pad_sum {M : Type} [AddCommMonoid M] {k m : ℕ} (hkm : k ≤ m) (F : Fin k → M) :
    ∑ x : Fin m, (if h : (x : ℕ) < k then F ⟨x, h⟩ else 0) = ∑ y, F y := by
  let G : ℕ → M := fun n => if h : n < k then F ⟨n, h⟩ else 0
  have h1 : ∑ x : Fin m, (if h : (x : ℕ) < k then F ⟨x, h⟩ else 0) =
      ∑ n ∈ Finset.range m, G n := Fin.sum_univ_eq_sum_range G m
  have h2 : ∑ y : Fin k, F y = ∑ n ∈ Finset.range k, G n := by
    rw [← Fin.sum_univ_eq_sum_range G k]
    exact Finset.sum_congr rfl fun y _ => by simp [G, y.isLt]
  rw [h1, h2]
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr hkm)
  intro n _ hn
  simp only [Finset.mem_range] at hn
  simp [G, hn]

theorem pad_gen {M β : Type} [AddCommMonoid M] {k m : ℕ} (hkm : k ≤ m) (P : Fin k → ℝ)
    (T : Fin k → β) (b0 : β) (Φ : ℝ → β → M) (hΦ : ∀ b, Φ 0 b = 0) :
    ∑ x : Fin m, Φ (if h : (x : ℕ) < k then P ⟨x, h⟩ else 0)
      (if h : (x : ℕ) < k then T ⟨x, h⟩ else b0) = ∑ y, Φ (P y) (T y) := by
  have : ∀ x : Fin m, Φ (if h : (x : ℕ) < k then P ⟨x, h⟩ else 0)
      (if h : (x : ℕ) < k then T ⟨x, h⟩ else b0) =
      if h : (x : ℕ) < k then Φ (P ⟨x, h⟩) (T ⟨x, h⟩) else 0 := fun x => by
    split_ifs <;> simp [hΦ]
  simp_rw [this]
  exact pad_sum (M := M) hkm (fun y => Φ (P y) (T y))

theorem sum_usc {m : ℕ} {Y : Type} [TopologicalSpace Y] {D : Set Y} (f : Y → ℝ)
    (hfu : UpperSemicontinuousOn f D) (C : ℝ) (hC : ∀ y, |f y| ≤ C) :
    UpperSemicontinuousOn (fun z : (Fin m → ℝ) × (Fin m → Y) => ∑ x, z.1 x * f (z.2 x))
      (stdSimplex ℝ (Fin m) ×ˢ Set.univ.pi fun _ => D) :=
  upperSemicontinuousOn_sum fun x _ =>
    usc_mul ((continuous_apply x).comp continuous_fst).continuousOn (fun z hz => hz.1.1 x)
      (usc_comp (f := f) (g := fun z : (Fin m → ℝ) × (Fin m → Y) => z.2 x) hfu
        ((continuous_apply x).comp continuous_snd).continuousOn
        fun z hz => hz.2 x (Set.mem_univ x)) (fun z => hC (z.2 x))

theorem sum_cont {m : ℕ} {Y : Type} [TopologicalSpace Y] {D : Set Y} (F : Y → ℝ)
    (hF : ContinuousOn F D) :
    ContinuousOn (fun z : (Fin m → ℝ) × (Fin m → Y) => ∑ x, z.1 x * F (z.2 x))
      (stdSimplex ℝ (Fin m) ×ˢ Set.univ.pi fun _ => D) :=
  continuousOn_finsetSum _ fun x _ =>
    ((continuous_apply x).comp continuous_fst).continuousOn.mul
      (hF.comp ((continuous_apply x).comp continuous_snd).continuousOn
        fun z hz => hz.2 x (Set.mem_univ x))

set_option maxHeartbeats 1000000 in
theorem main {a b : ℕ} [DecidableEq (Fin a)] [DecidableEq (Fin b)] (ha : 0 < a) (hb : 0 < b)
    (N : Superop (Fin a) (Fin b)) (hN : IsChannel N) :
    ∃ e : Ensemble (Fin a), e.size ≤ a ^ 2 ∧ channelObjective N e = channelPotential N := by
  obtain ⟨m0, K, hK, hNK⟩ := hN
  have hNe : N = krausApply K := funext hNK
  subst hNe
  haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  haveI : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  obtain ⟨hfu, C, hC⟩ := form_usc K hK
  set f := channelFormation (krausApply K) with hf
  let D : Set (Matrix (Fin a) (Fin a) ℂ) := {τ | IsDensityMatrix τ}
  let X : Set ((Fin (a ^ 2) → ℝ) × (Fin (a ^ 2) → Matrix (Fin a) (Fin a) ℂ)) :=
    stdSimplex ℝ (Fin (a ^ 2)) ×ˢ Set.univ.pi (fun _ => D)
  let G : (Fin (a ^ 2) → ℝ) × (Fin (a ^ 2) → Matrix (Fin a) (Fin a) ℂ) → ℝ := fun z =>
    vnEntropy (krausApply K (∑ x, z.1 x • z.2 x)) -
      ∑ x, z.1 x * vnEntropy (krausApply K (z.2 x)) + ∑ x, z.1 x * f (z.2 x)
  have hens : ∀ z ∈ X, ∃ e : Ensemble (Fin a), e.size = a ^ 2 ∧
      channelObjective (krausApply K) e = G z := fun z hz =>
    ⟨⟨a ^ 2, z.1, z.2, hz.1.1, hz.1.2, fun x => hz.2 x (Set.mem_univ x)⟩, rfl, rfl⟩
  let ρ0 : Matrix (Fin a) (Fin a) ℂ := pureDensity (EuclideanSpace.single (⟨0, ha⟩ : Fin a) (1 : ℂ))
  have hρ0 : IsDensityMatrix ρ0 := pure_dens _ (by simp [EuclideanSpace.norm_single])
  have hpad : ∀ e : Ensemble (Fin a), e.size ≤ a ^ 2 → ∃ z ∈ X,
      G z = channelObjective (krausApply K) e := by
    intro e hk
    let p : Fin (a ^ 2) → ℝ := fun x => if h : (x : ℕ) < e.size then e.prob ⟨x, h⟩ else 0
    let τ : Fin (a ^ 2) → Matrix (Fin a) (Fin a) ℂ :=
      fun x => if h : (x : ℕ) < e.size then e.state ⟨x, h⟩ else ρ0
    have e1 : ∑ x, p x • τ x = ensembleAverage e :=
      pad_gen hk e.prob e.state ρ0 (fun r M => r • M) (fun M => zero_smul _ _)
    have e2 : ∑ x, p x * vnEntropy (krausApply K (τ x)) =
        ∑ x, e.prob x * vnEntropy (krausApply K (e.state x)) :=
      pad_gen hk e.prob e.state ρ0 (fun r M => r * vnEntropy (krausApply K M))
        (fun M => zero_mul _)
    have e3 : ∑ x, p x * f (τ x) = ∑ x, e.prob x * f (e.state x) :=
      pad_gen hk e.prob e.state ρ0 (fun r M => r * f M) (fun M => zero_mul _)
    refine ⟨(p, τ), ⟨⟨fun x => ?_, ?_⟩, fun x _ => ?_⟩, ?_⟩
    · simp only [p]; split_ifs
      · exact e.nonneg _
      · exact le_rfl
    · have := pad_sum hk e.prob
      simp only [p]
      rw [this]; exact e.total
    · simp only [τ, D, Set.mem_setOf_eq]; split_ifs
      · exact e.density _
      · exact hρ0
    · show vnEntropy (krausApply K (∑ x, p x • τ x)) -
          ∑ x, p x * vnEntropy (krausApply K (τ x)) + ∑ x, p x * f (τ x) = _
      rw [e1, e2, e3]
      rfl
  have hX : IsCompact X :=
    (isCompact_stdSimplex (𝕜 := ℝ) (ι := Fin (a ^ 2))).prod
      (isCompact_univ_pi fun _ => dens_compact)
  have hXne : X.Nonempty := by
    let e1 : Ensemble (Fin a) := ⟨1, fun _ => 1, fun _ => ρ0, fun _ => zero_le_one,
      by simp, fun _ => hρ0⟩
    obtain ⟨z, hz, -⟩ := hpad e1 (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ ha.ne'))
    exact ⟨z, hz⟩
  have hSN : ContinuousOn (fun ρ => vnEntropy (krausApply K ρ)) D :=
    vn_contOn.comp (kraus_cont K).continuousOn fun ρ hρ => kraus_dens K hK hρ
  have hc1 : ContinuousOn (fun z : (Fin (a ^ 2) → ℝ) × (Fin (a ^ 2) → Matrix (Fin a) (Fin a) ℂ) =>
      vnEntropy (krausApply K (∑ x, z.1 x • z.2 x))) X :=
    hSN.comp (Continuous.continuousOn (continuous_finsetSum _ fun x _ =>
      ((continuous_apply x).comp continuous_fst).smul ((continuous_apply x).comp continuous_snd)))
      fun z hz => avg_dens hz.1.1 hz.1.2 fun x => hz.2 x (Set.mem_univ x)
  have hc2 := sum_cont (m := a ^ 2) (fun ρ => vnEntropy (krausApply K ρ)) hSN
  have hB := sum_usc (m := a ^ 2) f hfu C hC
  have hG : UpperSemicontinuousOn G X := ((hc1.sub hc2).upperSemicontinuousOn).add hB
  obtain ⟨z0, hz0, hmax⟩ := hG.exists_isMaxOn hXne hX
  obtain ⟨e0, he0, he0v⟩ := hens z0 hz0
  refine ⟨e0, he0.le, ?_⟩
  have hgreat : IsGreatest {r | ∃ e : Ensemble (Fin a), r = channelObjective (krausApply K) e}
      (G z0) := by
    refine ⟨⟨e0, he0v.symm⟩, ?_⟩
    rintro r ⟨e, rfl⟩
    obtain ⟨e', he's, he'v⟩ := reduce (krausApply K) e
    obtain ⟨z, hz, hzv⟩ := hpad e' he's
    rw [← hzv] at he'v
    exact he'v.trans (isMaxOn_iff.mp hmax z hz)
  rw [he0v]
  unfold channelPotential
  exact hgreat.csSup_eq.symm

end P08D

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P08 in
theorem solution {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (N : Superop (Fin a) (Fin b)) (hN : IsChannel N) :
    ∃ e : Ensemble (Fin a), e.size ≤ a ^ 2 ∧ channelObjective N e = channelPotential N := by
  exact P08D.main ha hb N hN
