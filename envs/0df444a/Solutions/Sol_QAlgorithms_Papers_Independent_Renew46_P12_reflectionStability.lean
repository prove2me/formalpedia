-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P12.reflectionStability
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T23:28:25.047748+00:00
-- url     : https://prove2.me/submissions/8d2c804a-c1af-42e3-bf9b-ca3180f5d56d

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P12
open QAlgorithms.Papers.Independent.Renew46.P12
open QAlgorithms

noncomputable section

theorem g64r_frob {ι : Type*} [Fintype ι] (X : Matrix ι ι ℂ) :
    frobNorm X = Real.sqrt (∑ i, ∑ j, Complex.normSq (X i j)) := by
  unfold frobNorm
  rw [@Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [Real.rpow_two, Complex.sq_norm]

theorem g64r_nsq {ι : Type*} [Fintype ι] (ψ : EuclideanSpace ℂ ι) :
    ‖ψ‖ ^ 2 = ∑ i, Complex.normSq (ψ i) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  exact Finset.sum_congr rfl (fun i _ => Complex.sq_norm _)

theorem g64r_main {ι : Type*} [Fintype ι] [DecidableEq ι] (psi phi : EuclideanSpace ℂ ι)
    (hpsi : ‖psi‖ = 1) (hphi : ‖phi‖ = 1) :
    frobNorm (householderReflection psi - householderReflection phi) ≤ 2 * Real.sqrt 2 * ‖psi - phi‖ := by
  have nψ : ∑ i, Complex.normSq (psi i) = 1 := by rw [← g64r_nsq, hpsi]; norm_num
  have nφ : ∑ i, Complex.normSq (phi i) = 1 := by rw [← g64r_nsq, hphi]; norm_num
  set d : ℂ := ∑ i, phi i * (starRingEnd ℂ) (psi i) with hd
  have hS : ∑ i, ∑ j, Complex.normSq ((householderReflection psi - householderReflection phi) i j) =
      4 * (2 - 2 * Complex.normSq d) := by
    have e : ∀ i j, (householderReflection psi - householderReflection phi) i j =
        2 * (phi i * (starRingEnd ℂ) (phi j) - psi i * (starRingEnd ℂ) (psi j)) := by
      intro i j; simp [householderReflection]; ring
    simp only [e, Complex.normSq_mul, Complex.normSq_sub, map_mul, Complex.normSq_conj]
    have h4 : Complex.normSq 2 = 4 := by norm_num [Complex.normSq_apply]
    rw [h4]
    have hcross : ∑ i, ∑ j, (phi i * (starRingEnd ℂ) (phi j) * (starRingEnd ℂ) (psi i * (starRingEnd ℂ) (psi j))).re
        = Complex.normSq d := by
      have : Complex.normSq d = (d * (starRingEnd ℂ) d).re := by
        rw [Complex.mul_conj]; simp
      rw [this, hd, map_sum, Finset.sum_mul_sum, Complex.re_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [map_mul, Complex.conj_conj]; ring_nf
    simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul]
    simp only [map_mul] at hcross
    rw [hcross, nψ, nφ]; ring
  have hD : ‖psi - phi‖ ^ 2 = 2 - 2 * d.re := by
    rw [g64r_nsq]
    simp only [WithLp.ofLp_sub, Pi.sub_apply, Complex.normSq_sub, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, nψ, nφ, ← Finset.mul_sum, ← Complex.re_sum]
    have : ∑ i, psi i * (starRingEnd ℂ) (phi i) = (starRingEnd ℂ) d := by
      rw [hd, map_sum]; refine Finset.sum_congr rfl (fun i _ => ?_); simp [mul_comm]
    rw [this, Complex.conj_re]; ring
  rw [g64r_frob, hS, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), hD]
  have := Complex.normSq_apply d
  nlinarith [sq_nonneg (d.re - 1), sq_nonneg d.im]

/-- Proposition 1, PDF p.2: ordinary Frobenius distance is bounded by 2 sqrt(2)
times Euclidean vector distance, with both vectors normalized. Includes n=0. -/
theorem solution (n : ℕ) (psi phi : EuclideanSpace ℂ (Qubits n))
    (hpsi : IsState psi) (hphi : IsState phi) :
    frobNorm (householderReflection psi - householderReflection phi) ≤ 2 * Real.sqrt 2 * ‖psi - phi‖ := g64r_main psi phi hpsi hphi

end

