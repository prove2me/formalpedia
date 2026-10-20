-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.explicitTwoDimensionalAlignment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:18:10.978919+00:00
-- url     : https://prove2.me/submissions/9a721b42-ae36-412b-9dc1-4a550e9c5839

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

lemma g53e_rank1 (F : Matrix (Fin 2) (Fin 2) ℂ) (u w : Fin 2 → ℂ) (a b : Fin 2)
    (hua : u a ≠ 0) (hwb : w b ≠ 0)
    (hcol : ∀ i j, F i j * u a = F a j * u i) (hrow : ∀ j, F a j * w b = F a b * w j) :
    F = (F a b / (u a * w b)) • Matrix.vecMulVec u w := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  field_simp
  linear_combination w b * hcol i j + u i * hrow j

lemma g53e_analytic (E0 E1 : ℂ) : AnalyticOnNhd ℝ (fun p : ℝ × ℝ => E0 * Complex.exp (Complex.I * (p.2 : ℂ)) * (Real.sin p.1 : ℂ) -
    E1 * (Real.cos p.1 : ℂ)) Set.univ := by
  intro p _
  have hof : ∀ q : ℝ × ℝ, AnalyticAt ℝ (fun x : ℝ => (x : ℂ)) q.2 := fun q =>
    Complex.ofRealCLM.analyticAt _
  have h2 : AnalyticAt ℝ (fun q : ℝ × ℝ => (q.2 : ℂ)) p :=
    (Complex.ofRealCLM.analyticAt _).comp ((ContinuousLinearMap.snd ℝ ℝ ℝ).analyticAt p)
  have h1 : AnalyticAt ℝ (fun q : ℝ × ℝ => (q.1 : ℂ)) p :=
    (Complex.ofRealCLM.analyticAt _).comp ((ContinuousLinearMap.fst ℝ ℝ ℝ).analyticAt p)
  have he : AnalyticAt ℝ (fun q : ℝ × ℝ => Complex.exp (Complex.I * (q.2 : ℂ))) p :=
    (analyticAt_cexp.restrictScalars).comp (analyticAt_const.mul h2)
  have hs : AnalyticAt ℝ (fun q : ℝ × ℝ => ((Real.sin q.1 : ℝ) : ℂ)) p := by
    simp only [Complex.ofReal_sin]
    exact (Complex.analyticAt_sin.restrictScalars).comp h1
  have hc : AnalyticAt ℝ (fun q : ℝ × ℝ => ((Real.cos q.1 : ℝ) : ℂ)) p := by
    simp only [Complex.ofReal_cos]
    exact (Complex.analyticAt_cos.restrictScalars).comp h1
  exact ((analyticAt_const.mul he).mul hs).sub (analyticAt_const.mul hc)

/-- PDF pp.24–25, VII D: explicit g=2 determinant and conjugate alignment equations.
The angular determinant is real analytic, while its vector-entry expression is polynomial. -/
theorem solution (theta phi : ℝ) (htheta0 : 0 < theta)
    (htheta1 : theta < Real.pi / 2) (E u v : Fin 2 → ℂ) (F : Mat 2)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    MvPolynomial.eval ![E 0,E 1,v 0,v 1] alignmentPolynomial = E 0*v 1 - E 1*v 0 ∧
    ((∃ a : ℂ, E = a • angularDirection theta phi) ↔
      angularDeterminant E (theta,phi) = 0) ∧
    AnalyticOnNhd ℝ (angularDeterminant E) {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < Real.pi / 2} ∧
    angularDeterminant ![0,1] (theta,phi) = -(Real.cos theta : ℂ) ∧
    angularDeterminant ![0,1] (theta,phi) ≠ 0 ∧
    ((∃ lambda : ℂ, F = lambda • Matrix.vecMulVec u (fun i => conj (v i))) ↔
      F 0 0 * u 1 - F 1 0 * u 0 = 0 ∧ F 0 1 * u 1 - F 1 1 * u 0 = 0 ∧
      conj (F 0 0) * v 1 - conj (F 0 1) * v 0 = 0 ∧
      conj (F 1 0) * v 1 - conj (F 1 1) * v 0 = 0) := by
  have hcos : 0 < Real.cos theta := Real.cos_pos_of_mem_Ioo ⟨by linarith, htheta1⟩
  have hcos' : (Real.cos theta : ℂ) ≠ 0 := by exact_mod_cast hcos.ne'
  have hcc : Complex.cos (theta : ℂ) ≠ 0 := by rw [← Complex.ofReal_cos]; exact hcos'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [alignmentPolynomial]
  · constructor
    · rintro ⟨a, rfl⟩
      simp [angularDeterminant, angularDirection]; ring
    · intro h
      refine ⟨E 0 / (Real.cos theta : ℂ), ?_⟩
      simp only [angularDeterminant, Complex.ofReal_sin, Complex.ofReal_cos] at h
      ext i; fin_cases i
      · simp [angularDirection]; field_simp
      · simp [angularDirection]; field_simp; linear_combination -h
  · intro p _
    exact g53e_analytic (E 0) (E 1) p (Set.mem_univ _)
  · simp [angularDeterminant]
  · simp [angularDeterminant, hcc]
  · constructor
    · rintro ⟨l, rfl⟩
      simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, map_mul, Complex.conj_conj]
      refine ⟨by ring, by ring, by ring, by ring⟩
    · rintro ⟨e1, e2, e3, e4⟩
      let w : Fin 2 → ℂ := fun i => conj (v i)
      have e3' : F 0 0 * w 1 - F 0 1 * w 0 = 0 := by
        have := congrArg conj e3; simpa [w] using this
      have e4' : F 1 0 * w 1 - F 1 1 * w 0 = 0 := by
        have := congrArg conj e4; simpa [w] using this
      have hw : w ≠ 0 := by
        intro h; apply hv; ext i; have := congrFun h i; simpa [w] using this
      obtain ⟨a, ha⟩ : ∃ a, u a ≠ 0 := by
        by_contra h; push Not at h; exact hu (funext h)
      obtain ⟨b, hb⟩ : ∃ b, w b ≠ 0 := by
        by_contra h; push Not at h; exact hw (funext h)
      refine ⟨F a b / (u a * w b), g53e_rank1 F u w a b ha hb ?_ ?_⟩
      · intro i j
        fin_cases a <;> fin_cases i <;> fin_cases j <;> simp <;>
          first | ring1 | linear_combination e1 | linear_combination -e1 | linear_combination e2 | linear_combination -e2
      · intro j
        fin_cases a <;> fin_cases b <;> fin_cases j <;> simp <;>
          first | ring1 | linear_combination e3' | linear_combination -e3' | linear_combination e4' | linear_combination -e4'

end
