-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P14.amplifierParametrization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:03:28.005691+00:00
-- url     : https://prove2.me/submissions/bfba01c3-8465-414a-87e9-b0b3dc372dbd

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14
noncomputable section
open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Frontier18.P14

lemma x8_afact (phi theta psi lam : ℝ) :
      amplifierEuler phi theta psi lam = Complex.exp (Complex.I * (lam / 2 : ℝ)) •
        (relativeModePhase psi * boost (theta / 2) * relativeModePhase phi) := by
  unfold amplifierEuler relativeModePhase boost
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply] <;> ring_nf <;>
    simp only [Complex.exp_add] <;> ring_nf

lemma x8_E_conj (x : ℝ) : conj (Complex.exp (Complex.I * (x : ℂ))) =
    Complex.exp (-Complex.I * (x : ℂ)) := by
  rw [← Complex.exp_conj]; simp

lemma x8_E_mul (x : ℝ) : Complex.exp (Complex.I * (x : ℂ)) * Complex.exp (-Complex.I * (x : ℂ)) = 1 := by
  rw [← Complex.exp_add]; simp

lemma x8_E_conj' (x : ℝ) : conj (Complex.exp (Complex.I * (x : ℂ))) =
    Complex.exp (Complex.I * ((-x : ℝ) : ℂ)) := by
  rw [x8_E_conj]; push_cast; ring_nf

lemma x8_polar (x : ℂ) : x = (‖x‖ : ℂ) * Complex.exp (Complex.I * ((Complex.arg x : ℝ) : ℂ)) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I x]
  rw [mul_comm Complex.I]


lemma x8_nsq (z : ℂ) : ((Complex.normSq z : ℝ) : ℂ) = z * conj z := (Complex.mul_conj z).symm

lemma x8_metric_iff (B : Matrix (Fin 2) (Fin 2) ℂ) :
    B * pairMetric * B.conjTranspose = pairMetric ↔
        Complex.normSq (B 0 0) - Complex.normSq (B 0 1) = 1 ∧
        Complex.normSq (B 1 1) - Complex.normSq (B 1 0) = 1 ∧
        star (B 0 0) * B 1 0 - star (B 0 1) * B 1 1 = 0 := by
  have key : ∀ i j, (B * pairMetric * B.conjTranspose) i j =
      B i 0 * conj (B j 0) - B i 1 * conj (B j 1) := by
    intro i j
    simp [pairMetric, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
    ring
  constructor
  · intro h
    have h00 := key 0 0; have h11 := key 1 1; have h10 := key 1 0
    rw [h] at h00 h11 h10
    simp [pairMetric] at h00 h11 h10
    refine ⟨?_, ?_, ?_⟩
    · have : ((Complex.normSq (B 0 0) - Complex.normSq (B 0 1) : ℝ) : ℂ) = 1 := by
        push_cast; rw [x8_nsq, x8_nsq]; linear_combination -h00
      exact_mod_cast this
    · have : ((Complex.normSq (B 1 1) - Complex.normSq (B 1 0) : ℝ) : ℂ) = 1 := by
        push_cast; rw [x8_nsq, x8_nsq]; linear_combination h11
      exact_mod_cast this
    · simp only [Complex.star_def]; linear_combination -h10
  · rintro ⟨h1, h2, h3⟩
    have h1' : ((Complex.normSq (B 0 0) - Complex.normSq (B 0 1) : ℝ) : ℂ) = 1 := by
      exact_mod_cast h1
    have h2' : ((Complex.normSq (B 1 1) - Complex.normSq (B 1 0) : ℝ) : ℂ) = 1 := by
      exact_mod_cast h2
    push_cast at h1' h2'
    rw [x8_nsq, x8_nsq] at h1' h2'
    simp only [Complex.star_def] at h3
    have h3c := congrArg conj h3
    simp only [map_sub, map_mul, Complex.conj_conj, map_zero] at h3c
    ext i j
    rw [key]
    fin_cases i <;> fin_cases j <;> simp [pairMetric]
    · linear_combination h1'
    · linear_combination h3c
    · linear_combination h3
    · linear_combination -h2'

lemma x8_pres_mul (M N : Matrix (Fin 2) (Fin 2) ℂ)
    (hM : M * pairMetric * M.conjTranspose = pairMetric)
    (hN : N * pairMetric * N.conjTranspose = pairMetric) :
    (M * N) * pairMetric * (M * N).conjTranspose = pairMetric := by
  calc (M * N) * pairMetric * (M * N).conjTranspose
      = M * (N * pairMetric * N.conjTranspose) * M.conjTranspose := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = pairMetric := by rw [hN, hM]

lemma x8_pres_phase (x : ℝ) :
    relativeModePhase x * pairMetric * (relativeModePhase x).conjTranspose = pairMetric := by
  have h1 := x8_E_mul (x / 2)
  have h2 := x8_E_conj (x / 2)
  have h3 : conj (Complex.exp (-Complex.I * ((x/2 : ℝ) : ℂ))) =
      Complex.exp (Complex.I * ((x/2:ℝ) : ℂ)) := by
    rw [← h2, Complex.conj_conj]
  simp only [neg_mul] at h1 h2 h3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [relativeModePhase, pairMetric, Matrix.mul_apply, Matrix.conjTranspose_apply, h2, h3,
      -Complex.ofReal_div] <;>
    linear_combination h1

lemma x8_pres_boost (x : ℝ) :
    boost x * pairMetric * (boost x).conjTranspose = pairMetric := by
  have h : ((Real.cosh x : ℂ)) ^ 2 - ((Real.sinh x : ℂ)) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_sub, Real.cosh_sq_sub_sinh_sq]
    simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boost, pairMetric, Matrix.mul_apply, Matrix.conjTranspose_apply, -Complex.ofReal_cosh,
      -Complex.ofReal_sinh, Complex.conj_ofReal] <;>
    first | linear_combination h | linear_combination -h | ring

lemma x8_pres_smul (x : ℝ) (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U * pairMetric * U.conjTranspose = pairMetric) :
    (Complex.exp (Complex.I * (x : ℂ)) • U) * pairMetric *
      (Complex.exp (Complex.I * (x : ℂ)) • U).conjTranspose = pairMetric := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hU,
    Complex.star_def, x8_E_conj, x8_E_mul, one_smul]

lemma x8_pres_euler (phi theta psi lam : ℝ) :
    amplifierEuler phi theta psi lam * pairMetric *
      (amplifierEuler phi theta psi lam).conjTranspose = pairMetric := by
  rw [x8_afact]
  exact x8_pres_smul _ _ (x8_pres_mul _ _ (x8_pres_mul _ _ (x8_pres_phase _) (x8_pres_boost _))
    (x8_pres_phase _))

lemma x8_aof_entries (B : Matrix (Fin 2) (Fin 2) ℂ) (phi theta psi lam : ℝ)
    (h00 : B 0 0 = Complex.exp (Complex.I * (lam / 2 : ℝ)) *
      ((Real.cosh (theta / 2) : ℂ) * Complex.exp (Complex.I * ((psi + phi) / 2 : ℝ))))
    (h01 : B 0 1 = Complex.exp (Complex.I * (lam / 2 : ℝ)) *
      ((Real.sinh (theta / 2) : ℂ) * Complex.exp (Complex.I * ((psi - phi) / 2 : ℝ))))
    (h10 : B 1 0 = Complex.exp (Complex.I * (lam / 2 : ℝ)) *
      ((Real.sinh (theta / 2) : ℂ) * Complex.exp (Complex.I * ((phi - psi) / 2 : ℝ))))
    (h11 : B 1 1 = Complex.exp (Complex.I * (lam / 2 : ℝ)) *
      ((Real.cosh (theta / 2) : ℂ) * Complex.exp (-Complex.I * ((psi + phi) / 2 : ℝ)))) :
    B = amplifierEuler phi theta psi lam := by
  unfold amplifierEuler
  ext i j
  fin_cases i <;> fin_cases j
  exacts [h00, h01, h10, h11]

lemma x8_asurj (B : Matrix (Fin 2) (Fin 2) ℂ)
    (hB : B * pairMetric * B.conjTranspose = pairMetric) :
    ∃ phi theta psi lam : ℝ, B = amplifierEuler phi theta psi lam := by
  obtain ⟨h1, h2, h3⟩ := (x8_metric_iff B).1 hB
  have e00 : B 0 0 * conj (B 0 0) - B 0 1 * conj (B 0 1) = 1 := by
    have h1' : ((Complex.normSq (B 0 0) - Complex.normSq (B 0 1) : ℝ) : ℂ) = 1 := by
      exact_mod_cast h1
    push_cast at h1'; rwa [x8_nsq, x8_nsq] at h1'
  have e11 : B 1 1 * conj (B 1 1) - B 1 0 * conj (B 1 0) = 1 := by
    have h2' : ((Complex.normSq (B 1 1) - Complex.normSq (B 1 0) : ℝ) : ℂ) = 1 := by
      exact_mod_cast h2
    push_cast at h2'; rwa [x8_nsq, x8_nsq] at h2'
  have e10 : B 1 0 * conj (B 0 0) - B 1 1 * conj (B 0 1) = 0 := by
    simp only [Complex.star_def] at h3; linear_combination h3
  set p := B 0 0
  set q := B 0 1
  set r := B 1 0
  set s := B 1 1
  obtain ⟨d, hd⟩ : ∃ d, d = p * s - q * r := ⟨_, rfl⟩
  have hs : s = d * conj p := by rw [hd]; linear_combination (-s) * e00 + q * e10
  have hr : r = d * conj q := by rw [hd]; linear_combination (-r) * e00 + p * e10
  have hsc : conj s = conj d * p := by rw [hs]; simp
  have hrc : conj r = conj d * q := by rw [hr]; simp
  have hdd : d * conj d = 1 := by
    linear_combination e11 + conj r * hr + d * conj q * hrc - conj s * hs - d * conj p * hsc
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
  have hab : ‖α‖ ^ 2 - ‖β‖ ^ 2 = 1 := by
    have h1 : ((‖α‖ : ℂ)) ^ 2 = α * conj α := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    have h2 : ((‖β‖ : ℂ)) ^ 2 = β * conj β := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    have h3 : ((‖α‖ : ℂ)) ^ 2 - (‖β‖ : ℂ) ^ 2 = 1 := by
      rw [h1, h2]; simp only [α, β, map_mul, hμ'c]
      linear_combination e00 + (p * conj p - q * conj q) * hμ
    exact_mod_cast h3
  have ha0 : 0 ≤ ‖α‖ := norm_nonneg _
  have hcosh : Real.cosh ((2 * Real.arsinh ‖β‖) / 2) = ‖α‖ := by
    rw [mul_div_cancel_left₀ _ two_ne_zero, Real.cosh_arsinh,
      show 1 + ‖β‖ ^ 2 = ‖α‖ ^ 2 by linarith, Real.sqrt_sq ha0]
  have hsinh : Real.sinh ((2 * Real.arsinh ‖β‖) / 2) = ‖β‖ := by
    rw [mul_div_cancel_left₀ _ two_ne_zero, Real.sinh_arsinh]
  refine ⟨Complex.arg α - Complex.arg β, 2 * Real.arsinh ‖β‖, Complex.arg α + Complex.arg β,
    lam, x8_aof_entries B _ _ _ _ ?_ ?_ ?_ ?_⟩ <;>
    simp only [hcosh, hsinh, show
        (Complex.arg α + Complex.arg β + (Complex.arg α - Complex.arg β)) / 2 =
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
    rw [← hβc, hr, hdμ, hqβ, map_mul, hμc]; linear_combination (μ * conj β) * hμ
  · show s = _
    rw [← hαc, hs, hdμ, hpα, map_mul, hμc]; linear_combination (μ * conj α) * hμ

theorem x8_main :
    (∀ B : Matrix (Fin 2) (Fin 2) ℂ,
      (B * pairMetric * B.conjTranspose = pairMetric ↔
        Complex.normSq (B 0 0) - Complex.normSq (B 0 1) = 1 ∧
        Complex.normSq (B 1 1) - Complex.normSq (B 1 0) = 1 ∧
        star (B 0 0) * B 1 0 - star (B 0 1) * B 1 1 = 0)) ∧
    (∀ B : Matrix (Fin 2) (Fin 2) ℂ,
      B * pairMetric * B.conjTranspose = pairMetric ↔
        ∃ phi theta psi lam : ℝ, B = amplifierEuler phi theta psi lam) ∧
    (∀ phi theta psi lam : ℝ,
      amplifierEuler phi theta psi lam = Complex.exp (Complex.I * (lam / 2 : ℝ)) •
        (relativeModePhase psi * boost (theta / 2) * relativeModePhase phi)) := by
  refine ⟨x8_metric_iff, fun B => ⟨x8_asurj B, ?_⟩, x8_afact⟩
  rintro ⟨phi, theta, psi, lam, rfl⟩
  exact x8_pres_euler _ _ _ _

end QAlgorithms.Papers.Independent.Frontier18.P14

open QAlgorithms.Papers.Independent.Frontier18.P14 in
theorem solution :
    (∀ B : Matrix (Fin 2) (Fin 2) ℂ,
      (B * pairMetric * B.conjTranspose = pairMetric ↔
        Complex.normSq (B 0 0) - Complex.normSq (B 0 1) = 1 ∧
        Complex.normSq (B 1 1) - Complex.normSq (B 1 0) = 1 ∧
        star (B 0 0) * B 1 0 - star (B 0 1) * B 1 1 = 0)) ∧
    (∀ B : Matrix (Fin 2) (Fin 2) ℂ,
      B * pairMetric * B.conjTranspose = pairMetric ↔
        ∃ phi theta psi lam : ℝ, B = amplifierEuler phi theta psi lam) ∧
    (∀ phi theta psi lam : ℝ,
      amplifierEuler phi theta psi lam = Complex.exp (Complex.I * (lam / 2 : ℝ)) •
        (relativeModePhase psi * boost (theta / 2) * relativeModePhase phi)) :=
  x8_main
