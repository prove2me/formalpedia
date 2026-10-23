-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P14.beamSplitterParametrization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:00:38.837167+00:00
-- url     : https://prove2.me/submissions/b4899a62-3034-4f9b-9c34-9b5865c3868e

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14
noncomputable section
open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Frontier18.P14

lemma x8_fact (phi theta psi lam : ℝ) :
      beamEuler phi theta psi lam = Complex.exp (Complex.I * (lam / 2 : ℝ)) •
        (relativeModePhase psi * realModeRotation (theta / 2) * relativeModePhase phi) := by
  unfold beamEuler relativeModePhase realModeRotation
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> ring_nf <;>
    simp only [Complex.exp_add] <;> ring_nf

lemma x8_E_conj (x : ℝ) : conj (Complex.exp (Complex.I * (x : ℂ))) =
    Complex.exp (-Complex.I * (x : ℂ)) := by
  rw [← Complex.exp_conj]; simp

lemma x8_E_mul (x : ℝ) : Complex.exp (Complex.I * (x : ℂ)) * Complex.exp (-Complex.I * (x : ℂ)) = 1 := by
  rw [← Complex.exp_add]; simp

lemma x8_phase_unitary (x : ℝ) : relativeModePhase x ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h1 := x8_E_mul (x / 2)
  have h2 := x8_E_conj (x / 2)
  have h3 : conj (Complex.exp (-Complex.I * ((x/2 : ℝ) : ℂ))) =
      Complex.exp (Complex.I * ((x/2:ℝ) : ℂ)) := by
    rw [← h2, Complex.conj_conj]
  simp only [neg_mul] at h1 h2 h3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [relativeModePhase, Matrix.mul_apply, Matrix.star_apply, h2, h3, -Complex.ofReal_div] <;>
    linear_combination h1

lemma x8_rot_unitary (x : ℝ) : realModeRotation x ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h : ((Real.cos x : ℂ)) ^ 2 + ((Real.sin x : ℂ)) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add, Real.cos_sq_add_sin_sq]; simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realModeRotation, Matrix.mul_apply, Matrix.star_apply, -Complex.ofReal_cos,
      -Complex.ofReal_sin, Complex.conj_ofReal] <;>
    first | linear_combination h | linear_combination -h | ring

lemma x8_smul_unitary (x : ℝ) (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    Complex.exp (Complex.I * (x : ℂ)) • U ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at *
  rw [star_smul, smul_mul_smul_comm, hU, Complex.star_def, x8_E_conj, x8_E_mul, one_smul]

lemma x8_euler_unitary (phi theta psi lam : ℝ) :
    beamEuler phi theta psi lam ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [x8_fact]
  exact x8_smul_unitary _ _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ (x8_phase_unitary _)
    (x8_rot_unitary _)) (x8_phase_unitary _))

lemma x8_E_conj' (x : ℝ) : conj (Complex.exp (Complex.I * (x : ℂ))) =
    Complex.exp (Complex.I * ((-x : ℝ) : ℂ)) := by
  rw [x8_E_conj]; push_cast; ring_nf

lemma x8_polar (x : ℂ) : x = (‖x‖ : ℂ) * Complex.exp (Complex.I * ((Complex.arg x : ℝ) : ℂ)) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I x]
  rw [mul_comm Complex.I]

lemma x8_of_entries (B : Matrix (Fin 2) (Fin 2) ℂ) (phi theta psi lam : ℝ)
    (h00 : B 0 0 = Complex.exp (Complex.I * (lam / 2 : ℝ)) *
      ((Real.cos (theta / 2) : ℂ) * Complex.exp (Complex.I * ((psi + phi) / 2 : ℝ))))
    (h01 : B 0 1 = Complex.exp (Complex.I * (lam / 2 : ℝ)) *
      ((Real.sin (theta / 2) : ℂ) * Complex.exp (Complex.I * ((psi - phi) / 2 : ℝ))))
    (h10 : B 1 0 = Complex.exp (Complex.I * (lam / 2 : ℝ)) *
      (-(Real.sin (theta / 2) : ℂ) * Complex.exp (Complex.I * ((phi - psi) / 2 : ℝ))))
    (h11 : B 1 1 = Complex.exp (Complex.I * (lam / 2 : ℝ)) *
      ((Real.cos (theta / 2) : ℂ) * Complex.exp (-Complex.I * ((psi + phi) / 2 : ℝ)))) :
    B = beamEuler phi theta psi lam := by
  unfold beamEuler
  ext i j
  fin_cases i <;> fin_cases j
  exacts [h00, h01, h10, h11]

lemma x8_surj (B : Matrix (Fin 2) (Fin 2) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ phi theta psi lam : ℝ, B = beamEuler phi theta psi lam := by
  rw [Matrix.mem_unitaryGroup_iff] at hB
  have e00 : B 0 0 * conj (B 0 0) + B 0 1 * conj (B 0 1) = 1 := by
    have := congrFun (congrFun hB 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] using this
  have e10 : B 1 0 * conj (B 0 0) + B 1 1 * conj (B 0 1) = 0 := by
    have := congrFun (congrFun hB 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] using this
  have e11 : B 1 0 * conj (B 1 0) + B 1 1 * conj (B 1 1) = 1 := by
    have := congrFun (congrFun hB 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] using this
  set p := B 0 0
  set q := B 0 1
  set r := B 1 0
  set s := B 1 1
  obtain ⟨d, hd⟩ : ∃ d, d = p * s - q * r := ⟨_, rfl⟩
  have hs : s = d * conj p := by rw [hd]; linear_combination (-s) * e00 + q * e10
  have hr : r = -d * conj q := by rw [hd]; linear_combination (-r) * e00 + p * e10
  have hsc : conj s = conj d * p := by rw [hs]; simp
  have hrc : conj r = -conj d * q := by rw [hr]; simp
  have hdd : d * conj d = 1 := by
    linear_combination e11 - conj r * hr + d * conj q * hrc - conj s * hs - d * conj p * hsc
      - d * conj d * e00
  have hdn : ‖d‖ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at hdd
    have : ‖d‖ ^ 2 = 1 := by exact_mod_cast hdd
    nlinarith [norm_nonneg d]
  set lam := Complex.arg d
  set μ := Complex.exp (Complex.I * ((lam / 2 : ℝ) : ℂ))
  set μ' := Complex.exp (-Complex.I * ((lam / 2 : ℝ) : ℂ))
  have hμ : μ * μ' = 1 := x8_E_mul _
  have hμc : conj μ = μ' := x8_E_conj _
  have hdμ : d = μ * μ := by
    rw [x8_polar d, hdn, ← Complex.exp_add]; push_cast; ring_nf; rfl
  set α := p * μ'
  set β := q * μ'
  have hα := x8_polar α
  have hβ := x8_polar β
  have hαc : conj α = (‖α‖ : ℂ) * Complex.exp (-Complex.I * ((Complex.arg α : ℝ) : ℂ)) := by
    rw [← x8_E_conj, ← Complex.conj_ofReal, ← map_mul, ← hα]
  have hβc : conj β = (‖β‖ : ℂ) * Complex.exp (Complex.I * ((-Complex.arg β : ℝ) : ℂ)) := by
    rw [← x8_E_conj', ← Complex.conj_ofReal, ← map_mul, ← hβ]
  have hμ'c : conj μ' = μ := by rw [← hμc, Complex.conj_conj]
  have hpα : p = α * μ := by linear_combination (-p) * hμ
  have hqβ : q = β * μ := by linear_combination (-q) * hμ
  have hab : ‖α‖ ^ 2 + ‖β‖ ^ 2 = 1 := by
    have h1 : ((‖α‖ : ℂ)) ^ 2 = α * conj α := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    have h2 : ((‖β‖ : ℂ)) ^ 2 = β * conj β := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    have h3 : ((‖α‖ : ℂ)) ^ 2 + (‖β‖ : ℂ) ^ 2 = 1 := by
      rw [h1, h2]; simp only [α, β, map_mul, hμ'c]
      linear_combination e00 + (p * conj p + q * conj q) * hμ
    exact_mod_cast h3
  have ha0 : 0 ≤ ‖α‖ := norm_nonneg _
  have hb0 : 0 ≤ ‖β‖ := norm_nonneg _
  have ha1 : ‖α‖ ≤ 1 := by nlinarith
  have hcos : Real.cos ((2 * Real.arccos ‖α‖) / 2) = ‖α‖ := by
    rw [mul_div_cancel_left₀ _ two_ne_zero, Real.cos_arccos (by linarith) ha1]
  have hsin : Real.sin ((2 * Real.arccos ‖α‖) / 2) = ‖β‖ := by
    rw [mul_div_cancel_left₀ _ two_ne_zero, Real.sin_arccos,
      show 1 - ‖α‖ ^ 2 = ‖β‖ ^ 2 by linarith, Real.sqrt_sq hb0]
  refine ⟨Complex.arg α - Complex.arg β, 2 * Real.arccos ‖α‖, Complex.arg α + Complex.arg β,
    lam, x8_of_entries B _ _ _ _ ?_ ?_ ?_ ?_⟩ <;>
    simp only [hcos, hsin, show (Complex.arg α + Complex.arg β + (Complex.arg α - Complex.arg β)) / 2 =
        Complex.arg α by ring,
      show (Complex.arg α + Complex.arg β - (Complex.arg α - Complex.arg β)) / 2 =
        Complex.arg β by ring,
      show (Complex.arg α - Complex.arg β - (Complex.arg α + Complex.arg β)) / 2 =
        -Complex.arg β by ring]
  · show p = _
    rw [← hα]; linear_combination hpα
  · show q = _
    rw [← hβ]; linear_combination hqβ
  · show r = _
    rw [neg_mul, ← hβc, hr, hdμ, hqβ, map_mul, hμc]; linear_combination (-(μ * conj β)) * hμ
  · show s = _
    rw [← hαc, hs, hdμ, hpα, map_mul, hμc]; linear_combination (μ * conj α) * hμ

theorem x8_main :
    (∀ B : Matrix (Fin 2) (Fin 2) ℂ,
      B ∈ Matrix.unitaryGroup (Fin 2) ℂ ↔
        ∃ phi theta psi lam : ℝ, B = beamEuler phi theta psi lam) ∧
    (∀ phi theta psi lam : ℝ,
      beamEuler phi theta psi lam = Complex.exp (Complex.I * (lam / 2 : ℝ)) •
        (relativeModePhase psi * realModeRotation (theta / 2) * relativeModePhase phi)) := by
  refine ⟨fun B => ⟨x8_surj B, ?_⟩, x8_fact⟩
  rintro ⟨phi, theta, psi, lam, rfl⟩
  exact x8_euler_unitary _ _ _ _

end QAlgorithms.Papers.Independent.Frontier18.P14

open QAlgorithms.Papers.Independent.Frontier18.P14 in
theorem solution :
    (∀ B : Matrix (Fin 2) (Fin 2) ℂ,
      B ∈ Matrix.unitaryGroup (Fin 2) ℂ ↔
        ∃ phi theta psi lam : ℝ, B = beamEuler phi theta psi lam) ∧
    (∀ phi theta psi lam : ℝ,
      beamEuler phi theta psi lam = Complex.exp (Complex.I * (lam / 2 : ℝ)) •
        (relativeModePhase psi * realModeRotation (theta / 2) * relativeModePhase phi)) :=
  x8_main
