-- Prove2me | solution 1 for SenTachyon.exists_trivializing_gauge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T20:36:54.847641+00:00
-- url     : https://prove2.me/submissions/1bd041bf-57db-4f0f-a1d7-e03dc1a83c15

import Mathlib
import Definitions.Def_SenTachyon_Defs

set_option autoImplicit false

open scoped ContDiff

/-- The matrix `[[p + i q, -r], [r, p - i q]]`; it lies in `SU(2)` when `p² + q² + r² = 1`. -/
noncomputable def stgP (p q r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(p : ℂ) + (q : ℂ) * Complex.I, -(r : ℂ); (r : ℂ), (p : ℂ) - (q : ℂ) * Complex.I]

/-- The candidate gauge field in terms of `b` (interpolation angle) and `θ` (loop angle):
`p = cos² b + sin² b cos θ`, `q = sin b sin θ`, `r = sin b cos b (1 - cos θ)`. -/
noncomputable def stgN (b θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  stgP (Real.cos b ^ 2 + Real.sin b ^ 2 * Real.cos θ) (Real.sin b * Real.sin θ)
    (Real.sin b * Real.cos b * (1 - Real.cos θ))

open SenTachyon in
theorem stg_omega1_eq (R : ℝ) (y : ℝ × ℝ) :
    omega1 R y = !![Complex.exp (Complex.I * ((y.2 / R : ℝ) : ℂ)), 0;
                    0, Complex.exp (-Complex.I * ((y.2 / R : ℝ) : ℂ))] := by
  have hp : pauli3 = Matrix.diagonal ![(1 : ℂ), -1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [pauli3]
  unfold omega1
  rw [hp, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]

theorem stg_e1 (z : ℂ) : Complex.exp (Complex.I * z) = Complex.cos z + Complex.sin z * Complex.I := by
  rw [mul_comm, Complex.exp_mul_I]

theorem stg_e2 (z : ℂ) :
    Complex.exp (-Complex.I * z) = Complex.cos z - Complex.sin z * Complex.I := by
  rw [show -Complex.I * z = (-z) * Complex.I by ring, Complex.exp_mul_I, Complex.cos_neg,
    Complex.sin_neg]
  ring

theorem stg_ofReal_contDiff {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p => ((f p : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hf

theorem stgP_contDiff {p q r : ℝ × ℝ → ℝ} (hp : ContDiff ℝ ∞ p) (hq : ContDiff ℝ ∞ q)
    (hr : ContDiff ℝ ∞ r) (i j : Fin 2) :
    ContDiff ℝ ∞ (fun x : ℝ × ℝ => stgP (p x) (q x) (r x) i j) := by
  have hI : ContDiff ℝ ∞ (fun _ : ℝ × ℝ => Complex.I) := contDiff_const
  fin_cases i <;> fin_cases j
  · simp only [stgP]
    simpa using (stg_ofReal_contDiff hp).add ((stg_ofReal_contDiff hq).mul hI)
  · simp only [stgP]
    simpa using (stg_ofReal_contDiff hr).neg
  · simp only [stgP]
    simpa using (stg_ofReal_contDiff hr)
  · simp only [stgP]
    simpa using (stg_ofReal_contDiff hp).sub ((stg_ofReal_contDiff hq).mul hI)

theorem stgN_contDiff (R : ℝ) (i j : Fin 2) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => stgN p.1 (p.2 / R) i j) := by
  have h1 : ContDiff ℝ ∞
      (fun p : ℝ × ℝ => Real.cos p.1 ^ 2 + Real.sin p.1 ^ 2 * Real.cos (p.2 / R)) := by
    fun_prop
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Real.sin p.1 * Real.sin (p.2 / R)) := by
    fun_prop
  have h3 : ContDiff ℝ ∞
      (fun p : ℝ × ℝ => Real.sin p.1 * Real.cos p.1 * (1 - Real.cos (p.2 / R))) := by
    fun_prop
  exact stgP_contDiff h1 h2 h3 i j

theorem stg_comp_contDiff (Φ : ℝ × ℝ → ℂ) (hΦ : ContDiff ℝ ∞ Φ) (B : ℝ → ℝ)
    (hB : ContDiff ℝ ∞ B) : ContDiff ℝ ∞ (fun x : ℝ × ℝ => Φ (B x.1, x.2)) :=
  hΦ.comp ((hB.comp contDiff_fst).prodMk contDiff_snd)

/-- The `x₁`-partial derivative of `y ↦ F (h y.1, y.2)` vanishes where `h' = 0`. -/
theorem stg_pd0_zero (F : ℝ × ℝ → ℂ) (h : ℝ → ℝ) (x : ℝ × ℝ)
    (hF : DifferentiableAt ℝ F (h x.1, x.2)) (hh : HasDerivAt h 0 x.1) :
    fderiv ℝ (fun y : ℝ × ℝ => F (h y.1, y.2)) x (1, 0) = 0 := by
  have hφ : HasFDerivAt (fun y : ℝ × ℝ => (h y.1, y.2))
      (((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (0 : ℝ)).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ)).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) x := by
    refine HasFDerivAt.prodMk ?_ hasFDerivAt_snd
    exact hh.hasFDerivAt.comp x hasFDerivAt_fst
  have hc := hF.hasFDerivAt.comp x hφ
  rw [show (fun y : ℝ × ℝ => F (h y.1, y.2)) = F ∘ (fun y : ℝ × ℝ => (h y.1, y.2)) from rfl,
    hc.fderiv]
  simp
  exact (fderiv ℝ F (h x.1, x.2)).map_zero

theorem stg_B_hasDerivAt (R₁ t : ℝ) (hs : Real.sin (t / (2 * R₁)) = 0) :
    HasDerivAt (fun t : ℝ => Real.pi / 4 * (1 + Real.cos (t / (2 * R₁)))) 0 t := by
  have h := (((hasDerivAt_id t).div_const (2 * R₁)).cos.const_add 1).const_mul (Real.pi / 4)
  exact h.congr_deriv (by simp [hs])

theorem stgP_mem (p q r : ℝ) (h : p ^ 2 + q ^ 2 + r ^ 2 = 1) :
    stgP p q r ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [stgP, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose,
        Complex.ext_iff] <;> constructor <;> first | ring1 | linear_combination h
  · rw [Matrix.det_fin_two]
    simp [stgP, Complex.ext_iff]
    constructor <;> first | ring1 | linear_combination h

theorem stgN_mem (b θ : ℝ) : stgN b θ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have hb := Real.cos_sq_add_sin_sq b
  have hθ := Real.cos_sq_add_sin_sq θ
  apply stgP_mem
  linear_combination (Real.cos b ^ 2 + Real.sin b ^ 2 * Real.cos θ ^ 2 + 1) * hb
    + Real.sin b ^ 2 * hθ

open SenTachyon in open scoped ContDiff in
theorem solution (R₁t R₂t : ℝ) (h₁ : 0 < R₁t) (h₂ : 0 < R₂t) :
    ∃ g : ℝ × ℝ → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ i j, ContDiff ℝ ∞ (fun x => g x i j)) ∧
      (∀ x ∈ Set.Icc 0 (2 * Real.pi * R₁t) ×ˢ Set.Icc 0 (2 * Real.pi * R₂t),
        g x ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) ∧
      (∀ x₂ ∈ Set.Icc 0 (2 * Real.pi * R₂t), g (0, x₂) = omega1 R₂t (0, x₂)) ∧
      (∀ x₂ ∈ Set.Icc 0 (2 * Real.pi * R₂t), g (2 * Real.pi * R₁t, x₂) = 1) ∧
      (∀ x₁ ∈ Set.Icc 0 (2 * Real.pi * R₁t), g (x₁, 2 * Real.pi * R₂t) = g (x₁, 0)) ∧
      (∀ x₂ ∈ Set.Icc 0 (2 * Real.pi * R₂t),
        partialDeriv 0 g (0, x₂) = 0 ∧ partialDeriv 0 g (2 * Real.pi * R₁t, x₂) = 0) := by
  have hR1 : R₁t ≠ 0 := h₁.ne'
  have hR2 : R₂t ≠ 0 := h₂.ne'
  obtain ⟨B, hB⟩ : ∃ B : ℝ → ℝ, B = fun t => Real.pi / 4 * (1 + Real.cos (t / (2 * R₁t))) :=
    ⟨_, rfl⟩
  have hB0 : B 0 = Real.pi / 2 := by rw [hB]; simp; ring
  have hL : 2 * Real.pi * R₁t / (2 * R₁t) = Real.pi := by field_simp
  have hBL : B (2 * Real.pi * R₁t) = 0 := by
    rw [hB]; simp [hL]
  have hBd : ContDiff ℝ ∞ B := by
    rw [hB]; fun_prop
  refine ⟨fun x => stgN (B x.1) (x.2 / R₂t), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact stg_comp_contDiff (fun q : ℝ × ℝ => stgN q.1 (q.2 / R₂t) i j) (stgN_contDiff R₂t i j)
      B hBd
  · intro x _
    exact stgN_mem _ _
  · intro x₂ _
    rw [stg_omega1_eq, stg_e1, stg_e2]
    simp only [hB0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [stgN, stgP]
  · intro x₂ _
    simp only [hBL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [stgN, stgP]
  · intro x₁ _
    have : 2 * Real.pi * R₂t / R₂t = 2 * Real.pi := by field_simp
    simp only [this, zero_div, stgN, Real.cos_two_pi, Real.sin_two_pi, Real.cos_zero,
      Real.sin_zero]
  · intro x₂ _
    have hdiff : ∀ i j : Fin 2, ∀ p : ℝ × ℝ,
        DifferentiableAt ℝ (fun q : ℝ × ℝ => stgN q.1 (q.2 / R₂t) i j) p := fun i j p =>
      ((stgN_contDiff R₂t i j).differentiable (by simp)) p
    have hd0 : HasDerivAt B 0 0 := by
      rw [hB]; exact stg_B_hasDerivAt R₁t 0 (by simp)
    have hdL : HasDerivAt B 0 (2 * Real.pi * R₁t) := by
      rw [hB]
      apply stg_B_hasDerivAt
      rw [hL, Real.sin_pi]
    constructor
    · ext i j
      simp only [partialDeriv, coordVec, Matrix.of_apply, if_true, Matrix.zero_apply]
      exact stg_pd0_zero (fun q : ℝ × ℝ => stgN q.1 (q.2 / R₂t) i j) B (0, x₂) (hdiff i j _) hd0
    · ext i j
      simp only [partialDeriv, coordVec, Matrix.of_apply, if_true, Matrix.zero_apply]
      exact stg_pd0_zero (fun q : ℝ × ℝ => stgN q.1 (q.2 / R₂t) i j) B _ (hdiff i j _) hdL
