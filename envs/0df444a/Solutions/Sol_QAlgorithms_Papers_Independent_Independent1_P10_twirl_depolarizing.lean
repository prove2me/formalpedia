-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P10.twirl_depolarizing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T01:12:35.020247+00:00
-- url     : https://prove2.me/submissions/1201b6e3-5167-498d-a025-eb24f0f5229e

import Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P10_twirl_invariance
import Mathlib.LinearAlgebra.Matrix.Permutation

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexOrder ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Independent1.P10 Matrix

private lemma channel_linear {d : ℕ} (E : Superop (Fin d) (Fin d)) (hE : IsChannel E) :
    ∃ L : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ, ∀ X, L X = E X := by
  obtain ⟨m, K, _, hK⟩ := hE
  refine ⟨{ toFun := E, map_add' := ?_, map_smul' := ?_ }, fun _ => rfl⟩
  · intro X Y
    simp only [hK, krausApply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  · intro c X
    simp only [hK, krausApply, Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum]
    rfl

private lemma proj_density {d : ℕ} (i : Fin d) :
    IsDensityMatrix (Matrix.single i i (1 : ℂ)) := by
  have he : Matrix.single i i (1 : ℂ) = pureDensity (ket i) := by
    ext a b
    simp [pureDensity, ket, Matrix.single_apply]
    split_ifs <;> simp_all; aesop
  rw [he]
  refine ⟨Matrix.posSemidef_vecMulVec_self_star _, ?_⟩
  simp [pureDensity, ket, Matrix.trace]

private def signUnitary {d : ℕ} (i : Fin d) : Matrix.unitaryGroup (Fin d) ℂ :=
  ⟨Matrix.diagonal (fun k => if k = i then -1 else 1), by
    apply Matrix.mem_unitaryGroup_iff.mpr
    ext a b
    simp only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp_all⟩

private lemma sign_conj {d : ℕ} (i : Fin d) (X : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d) :
    conjSuperop (signUnitary i : Matrix (Fin d) (Fin d) ℂ) X a b =
      (if a = i then -1 else 1) * X a b * (if b = i then -1 else 1) := by
  change (Matrix.diagonal (fun k : Fin d => if k = i then (-1 : ℂ) else 1) * X *
    (Matrix.diagonal (fun k : Fin d => if k = i then (-1 : ℂ) else 1))ᴴ) a b = _
  simp only [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  split_ifs <;> simp_all


private def permUnitary {d : ℕ} (s : Equiv.Perm (Fin d)) : Matrix.unitaryGroup (Fin d) ℂ :=
  ⟨s.permMatrix ℂ, by
    apply Matrix.mem_unitaryGroup_iff.mpr
    simp [Matrix.star_eq_conjTranspose, ← Matrix.permMatrix_mul]⟩

private lemma perm_conj {d : ℕ} (s : Equiv.Perm (Fin d)) (X : Matrix (Fin d) (Fin d) ℂ) :
    conjSuperop (permUnitary s : Matrix (Fin d) (Fin d) ℂ) X = X.submatrix s s := by
  ext a b
  simp [permUnitary, conjSuperop, Matrix.mul_apply,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Equiv.symm_apply_eq]

private lemma perm_proj {d : ℕ} (s : Equiv.Perm (Fin d)) (i : Fin d) :
    conjSuperop (permUnitary s : Matrix (Fin d) (Fin d) ℂ) (Matrix.single i i 1) =
      Matrix.single (s.symm i) (s.symm i) 1 := by
  rw [perm_conj]
  ext a b
  simp [Matrix.single_apply, Equiv.symm_apply_eq]

private lemma covariant_projections {d : ℕ}
    (L : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hc : ∀ rho, IsDensityMatrix rho → ∀ V : Matrix.unitaryGroup (Fin d) ℂ,
      conjSuperop (V : Matrix (Fin d) (Fin d) ℂ) (L rho) =
        L (conjSuperop (V : Matrix (Fin d) (Fin d) ℂ) rho))
    (z o : Fin d) (hzo : z ≠ o) :
    ∃ a b : ℂ, ∀ i, L (Matrix.single i i 1) =
      b • (1 : Matrix (Fin d) (Fin d) ℂ) + (a-b) • Matrix.single i i 1 := by
  let A := L (Matrix.single z z 1)
  have hdiag (i a b : Fin d) (hab : a ≠ b) : L (Matrix.single i i 1) a b = 0 := by
    have hfix : conjSuperop (signUnitary a : Matrix (Fin d) (Fin d) ℂ)
        (Matrix.single i i 1) = Matrix.single i i 1 := by
      ext j k
      rw [sign_conj]
      simp only [Matrix.single_apply]
      split_ifs <;> simp_all <;> aesop

    have hh := congrArg (fun M => M a b) (hc _ (proj_density i) (signUnitary a))
    rw [hfix, sign_conj] at hh
    simp only [ite_true, if_neg (Ne.symm hab), neg_one_mul, mul_one] at hh
    linear_combination -(1/2 : ℂ) * hh
  have hoff (j : Fin d) (hj : j ≠ z) : A j j = A o o := by
    let s := Equiv.swap o j
    have hz : s z = z := Equiv.swap_apply_of_ne_of_ne hzo (Ne.symm hj)
    have hz' : s.symm z = z := by simpa [s] using hz
    have hh := congrArg (fun M => M o o) (hc _ (proj_density z) (permUnitary s))
    rw [perm_proj, hz', perm_conj] at hh
    simpa [A, s] using hh
  refine ⟨A z z, A o o, ?_⟩
  intro i
  let s := Equiv.swap z i
  have hh := hc _ (proj_density z) (permUnitary s)
  rw [perm_proj, perm_conj] at hh
  have hsi : s.symm z = i := by simp [s]
  rw [hsi] at hh
  rw [← hh]
  ext j k
  by_cases hjk : j = k
  · subst k
    by_cases hji : j = i
    · subst j
      simp [s, A]
    · have hsj : s j ≠ z := by
        intro h
        apply hji
        simpa [s] using congrArg s.symm h
      change A (s j) (s j) = _
      simp [hoff _ hsj, Ne.symm hji]
  · have hsjk : s j ≠ s k := fun h => hjk (s.injective h)
    simp [Matrix.submatrix_apply, hdiag _ _ _ hsjk, Matrix.single_apply, hjk]
    aesop

private lemma channel_density {d : ℕ} (E : Superop (Fin d) (Fin d)) (hE : IsChannel E)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho) : IsDensityMatrix (E rho) := by
  obtain ⟨m, K, hK, hE⟩ := hE
  rw [hE]
  constructor
  · exact Matrix.posSemidef_sum Finset.univ (fun i _ => hrho.1.mul_mul_conjTranspose_same (K i))
  · have ht : ∀ i, (K i*rho*(K i)ᴴ).trace = ((K i)ᴴ*K i*rho).trace := by
      intro i; rw [Matrix.trace_mul_cycle]
    simp only [krausApply, Matrix.trace_sum, ht]
    rw [← Matrix.trace_sum, ← Finset.sum_mul]
    change ((∑ i, (K i)ᴴ*K i)*rho).trace = 1
    rw [hK, one_mul, hrho.2]

private lemma spectral_sum {d : ℕ} (rho : Matrix (Fin d) (Fin d) ℂ) (hr : rho.IsHermitian) :
    rho = ∑ i, (hr.eigenvalues i : ℂ) •
      conjSuperop (hr.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) (Matrix.single i i 1) := by
  conv_lhs => rw [hr.spectral_theorem, Unitary.conjStarAlgAut_apply]
  have hd : Matrix.diagonal (fun i => (hr.eigenvalues i : ℂ)) =
      ∑ i, (hr.eigenvalues i : ℂ) • Matrix.single i i (1 : ℂ) := by
    ext a b
    simp [Matrix.single_apply, Matrix.diagonal_apply, Matrix.sum_apply, ite_and, eq_comm]
  change (hr.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
    Matrix.diagonal (fun i => (hr.eigenvalues i : ℂ)) * star (hr.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) = _
  rw [hd]
  simp only [conjSuperop, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.star_eq_conjTranspose]

private lemma conj_normal {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ)
    (b c : ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    conjSuperop (U : Matrix (Fin d) (Fin d) ℂ) (b • 1 + c • X) =
      b • 1 + c • conjSuperop (U : Matrix (Fin d) (Fin d) ℂ) X := by
  have hu := Matrix.mem_unitaryGroup_iff.mp U.property
  simp [conjSuperop, Matrix.mul_add, Matrix.add_mul, hu, Matrix.star_eq_conjTranspose] at *

private lemma covariant_density {d : ℕ}
    (L : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hc : ∀ rho, IsDensityMatrix rho → ∀ V : Matrix.unitaryGroup (Fin d) ℂ,
      conjSuperop (V : Matrix (Fin d) (Fin d) ℂ) (L rho) =
        L (conjSuperop (V : Matrix (Fin d) (Fin d) ℂ) rho))
    (a b : ℂ) (hp : ∀ i, L (Matrix.single i i 1) = b • 1 + (a-b) • Matrix.single i i 1)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho) :
    L rho = b • 1 + (a-b) • rho := by
  let hr := hrho.1.1
  let U := hr.eigenvectorUnitary
  let P := fun i => conjSuperop (U : Matrix (Fin d) (Fin d) ℂ) (Matrix.single i i 1)
  have hs : rho = ∑ i, (hr.eigenvalues i : ℂ) • P i := spectral_sum rho hr
  have hl (i : Fin d) : L (P i) = b • 1 + (a-b) • P i := by
    dsimp [P]
    rw [← hc _ (proj_density i) U, hp, conj_normal]
  have hsum : ∑ i, (hr.eigenvalues i : ℂ) = 1 := by
    have he := hr.spectral_theorem
    have ht := congrArg Matrix.trace he
    simp only [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, Matrix.one_mul,
      Matrix.trace_diagonal, Function.comp_def] at ht
    rw [hrho.2] at ht
    exact ht.symm
  calc
    L rho = ∑ i, (hr.eigenvalues i : ℂ) • L (P i) := by
      calc L rho = L (∑ i, (hr.eigenvalues i : ℂ) • P i) := congrArg L hs
           _ = _ := by simp
    _ = (∑ i, (hr.eigenvalues i : ℂ)) • (b • 1) +
        (a-b) • (∑ i, (hr.eigenvalues i : ℂ) • P i) := by
      simp_rw [hl, smul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_smul, Finset.smul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact smul_comm _ _ _
    _ = b • 1 + (a-b) • rho := by rw [hsum, one_smul, ← hs]

private lemma covariant_channel_depolarizing (d : ℕ) (hd : 0 < d)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E)
    (hc : ∀ rho, IsDensityMatrix rho → ∀ V : Matrix.unitaryGroup (Fin d) ℂ,
      conjSuperop (V : Matrix (Fin d) (Fin d) ℂ) (E rho) =
        E (conjSuperop (V : Matrix (Fin d) (Fin d) ℂ) rho)) :
    ∃ p : ℝ, ∀ rho, IsDensityMatrix rho →
      E rho = ((p/(d : ℝ) : ℝ) : ℂ) • 1 + ((1-p : ℝ) : ℂ) • rho := by
  by_cases hd1 : d = 1
  · subst d
    have hu (X : Matrix (Fin 1) (Fin 1) ℂ) (hX : IsDensityMatrix X) : X = 1 := by
      ext i j
      fin_cases i
      fin_cases j
      simpa [Matrix.trace, Fin.sum_univ_one] using hX.2
    refine ⟨0, ?_⟩
    intro rho hrho
    simp only [zero_div, Complex.ofReal_zero, zero_smul, sub_zero, Complex.ofReal_one,
      one_smul, zero_add]
    rw [hu _ (channel_density E hE _ hrho), hu _ hrho]
  have hd2 : 1 < d := by omega
  let z : Fin d := ⟨0, hd⟩
  let o : Fin d := ⟨1, hd2⟩
  have hzo : z ≠ o := by simp [z, o, Fin.ext_iff]
  obtain ⟨L, hL⟩ := channel_linear E hE
  have hcL : ∀ rho, IsDensityMatrix rho → ∀ V : Matrix.unitaryGroup (Fin d) ℂ,
      conjSuperop (V : Matrix (Fin d) (Fin d) ℂ) (L rho) =
        L (conjSuperop (V : Matrix (Fin d) (Fin d) ℂ) rho) := by
    simpa only [hL] using hc
  obtain ⟨a, b, hp⟩ := covariant_projections L hcL z o hzo
  have hden : IsDensityMatrix (L (Matrix.single z z 1)) := by
    rw [hL]
    exact channel_density E hE _ (proj_density z)
  have hb0 : L (Matrix.single z z 1) o o = b := by
    rw [hp]
    simp [hzo]
  have hb : (b.re : ℂ) = b := Complex.conj_eq_iff_re.mp (by
    simpa only [hb0, Complex.star_def] using hden.1.1.apply o o)
  have ht : (d : ℂ)*b + (a-b) = 1 := by
    have hh := hden.2
    rw [hp] at hh
    simpa [Matrix.trace_add, Matrix.trace_smul, mul_comm] using hh
  refine ⟨(d : ℝ)*b.re, ?_⟩
  intro rho hrho
  rw [← hL, covariant_density L hcL a b hp rho hrho]
  have hdiv : (d : ℝ)*b.re/(d : ℝ) = b.re := by
    field_simp
  have hcoeff : ((1-(d : ℝ)*b.re : ℝ) : ℂ) = a-b := by
    push_cast
    rw [hb]
    linear_combination -ht
  rw [hdiv, hb, hcoeff]

/-- Nielsen's stabilizer and spectral-decomposition argument, using twirl covariance. -/
theorem solution (d : ℕ) (hd : 0 < d)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E) :
    ∃ p : ℝ, ∀ rho : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix rho →
      QuditFidelity.haarTwirl d hd E rho =
        ((p/(d : ℝ) : ℝ) : ℂ) • 1 + ((1-p : ℝ) : ℂ) • rho := by
  have hT := twirl_invariance d hd E hE
  exact covariant_channel_depolarizing d hd _ hT.1 hT.2.2.2
