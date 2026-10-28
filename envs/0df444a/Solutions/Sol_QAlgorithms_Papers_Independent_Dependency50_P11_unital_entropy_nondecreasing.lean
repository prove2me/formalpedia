-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P11.unital_entropy_nondecreasing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:09:31.48788+00:00
-- url     : https://prove2.me/submissions/a95ddbb0-652c-4fe5-bf31-b626b44c71a5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P11

namespace X5UE

open Matrix QAlgorithms
open scoped ComplexOrder

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma tr_cfc {X : Matrix ι ι ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    (cfc f X).trace = ∑ i, ((f (hX.eigenvalues i) : ℝ) : ℂ) := by
  rw [hX.cfc_eq]
  unfold IsHermitian.cfc
  simp only [Unitary.conjStarAlgAut_apply]
  set U := (hX.eigenvectorUnitary : Matrix ι ι ℂ)
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem (hX.eigenvectorUnitary).2
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul, Matrix.trace_diagonal]
  rfl

lemma ent_eq {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    -(cfc (fun x : ℝ => x * Real.log x) X).trace.re = ∑ i, Real.negMulLog (hX.eigenvalues i) := by
  rw [tr_cfc hX, Complex.re_sum, ← Finset.sum_neg_distrib]
  simp [Real.negMulLog]

lemma spec {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    star (hX.eigenvectorUnitary : Matrix ι ι ℂ) * X * (hX.eigenvectorUnitary : Matrix ι ι ℂ) =
      diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) := by
  set U := (hX.eigenvectorUnitary : Matrix ι ι ℂ)
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem (hX.eigenvectorUnitary).2
  conv_lhs => rw [hX.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply]
  change star U * (U * _ * star U) * U = _
  rw [show star U * (U * diagonal (RCLike.ofReal ∘ hX.eigenvalues) * star U) * U =
    (star U * U) * diagonal (RCLike.ofReal ∘ hX.eigenvalues) * (star U * U) by
      simp only [Matrix.mul_assoc], hU]
  simp

lemma spec_sum {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    X = ∑ i, ((hX.eigenvalues i : ℝ) : ℂ) •
      vecMulVec (fun a => (hX.eigenvectorUnitary : Matrix ι ι ℂ) a i)
        (star fun a => (hX.eigenvectorUnitary : Matrix ι ι ℂ) a i) := by
  conv_lhs => rw [hX.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply]
  ext a b
  simp [Matrix.mul_apply, Matrix.sum_apply, vecMulVec_apply, diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma kraus_sum {n : ℕ} (K : Fin n → Matrix ι ι ℂ) (c : ι → ℂ) (R : ι → Matrix ι ι ℂ) :
    krausApply K (∑ i, c i • R i) = ∑ i, c i • krausApply K (R i) := by
  simp only [krausApply, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Finset.smul_sum]
  rw [Finset.sum_comm]

lemma kraus_psd {n : ℕ} (K : Fin n → Matrix ι ι ℂ) {R : Matrix ι ι ℂ} (hR : R.PosSemidef) :
    (krausApply K R).PosSemidef := by
  unfold krausApply
  exact Matrix.posSemidef_sum _ fun k _ => hR.mul_mul_conjTranspose_same (K k)

lemma kraus_trace {n : ℕ} (K : Fin n → Matrix ι ι ℂ) (hK : IsKrausFamily K) (R : Matrix ι ι ℂ) :
    (krausApply K R).trace = R.trace := by
  unfold krausApply
  rw [Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (K _) R]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hK, Matrix.one_mul]

theorem main {n : ℕ} (K : Fin n → Matrix ι ι ℂ) (hK : IsKrausFamily K)
    (hU : krausApply K 1 = 1) (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) :
    ∑ i, Real.negMulLog (hρ.1.eigenvalues i) ≤
      ∑ j, Real.negMulLog ((kraus_psd K hρ).1.eigenvalues j) := by
  set hH := hρ.1
  set σ := krausApply K ρ
  set hS := (kraus_psd K hρ).1
  set U := (hH.eigenvectorUnitary : Matrix ι ι ℂ)
  set W := (hS.eigenvectorUnitary : Matrix ι ι ℂ)
  have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem (hH.eigenvectorUnitary).2
  have hUU' : U * star U = 1 := Unitary.mul_star_self_of_mem (hH.eigenvectorUnitary).2
  have hWW : star W * W = 1 := Unitary.star_mul_self_of_mem (hS.eigenvectorUnitary).2
  have hWW' : W * star W = 1 := Unitary.mul_star_self_of_mem (hS.eigenvectorUnitary).2
  set lam := hH.eigenvalues
  set μ := hS.eigenvalues
  let u : ι → ι → ℂ := fun i a => U a i
  let R : ι → Matrix ι ι ℂ := fun i => vecMulVec (u i) (star (u i))
  have hR : ∀ i, (R i).PosSemidef := fun i => Matrix.posSemidef_vecMulVec_self_star (u i)
  let P : ι → ι → ℝ := fun j i => (star W * krausApply K (R i) * W) j j |>.re
  have hP0 : ∀ j i, 0 ≤ P j i := by
    intro j i
    have h := ((kraus_psd K (hR i)).conjTranspose_mul_mul_same W).diag_nonneg (i := j)
    simp only [Matrix.star_eq_conjTranspose] at *
    exact (Complex.nonneg_iff.mp h).1
  have hsumR : ∑ i, R i = 1 := by
    rw [← hUU']; ext a b
    simp [R, u, vecMulVec_apply, Matrix.mul_apply, Matrix.sum_apply]
  have hPi : ∀ j, ∑ i, P j i = 1 := by
    intro j
    simp only [P]
    rw [← Complex.re_sum]
    have : ∑ i, (star W * krausApply K (R i) * W) j j = (star W * krausApply K (∑ i, R i) * W) j j := by
      have := kraus_sum K (fun _ => 1) R
      simp only [one_smul] at this
      rw [this, Finset.mul_sum, Finset.sum_mul, Matrix.sum_apply]
    rw [this, hsumR, hU, Matrix.mul_one, hWW]; simp
  have hPj : ∀ i, ∑ j, P j i = 1 := by
    intro i
    simp only [P]
    rw [← Complex.re_sum]
    change ((star W * krausApply K (R i) * W).trace).re = 1
    rw [Matrix.trace_mul_cycle, hWW', Matrix.one_mul, kraus_trace K hK, trace_vecMulVec]
    have : (star U * U) i i = u i ⬝ᵥ star (u i) := by
      simp [Matrix.mul_apply, dotProduct, u, mul_comm]
    rw [← this, hUU]; simp
  have hμ : ∀ j, μ j = ∑ i, P j i * lam i := by
    intro j
    have h1 : (star W * krausApply K ρ * W) j j = (μ j : ℂ) := by
      have := congrFun (congrFun (spec hS) j) j
      simpa only [diagonal_apply_eq] using this
    clear_value W μ
    have h2 : ρ = ∑ i, ((lam i : ℝ) : ℂ) • R i := spec_sum hH
    have h3 : krausApply K ρ = ∑ i, ((lam i : ℝ) : ℂ) • krausApply K (R i) := by
      conv_lhs => rw [h2]
      exact kraus_sum K _ R
    have : (μ j : ℂ) = ∑ i, (lam i : ℂ) * (star W * krausApply K (R i) * W) j j := by
      rw [← h1, h3, Finset.mul_sum, Finset.sum_mul, Matrix.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Matrix.mul_smul, Matrix.smul_mul]
    have := congrArg Complex.re this
    rw [Complex.re_sum] at this
    simp only [Complex.ofReal_re, Complex.re_ofReal_mul] at this
    rw [this]; simp only [P]; exact Finset.sum_congr rfl fun i _ => by ring
  have hlam : ∀ i, 0 ≤ lam i := hρ.eigenvalues_nonneg
  calc ∑ i, Real.negMulLog (lam i) = ∑ i, ∑ j, P j i * Real.negMulLog (lam i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_mul, hPj, one_mul]
    _ = ∑ j, ∑ i, P j i * Real.negMulLog (lam i) := Finset.sum_comm
    _ ≤ ∑ j, Real.negMulLog (μ j) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [hμ j]
        have := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ) (w := P j) (p := lam)
          (fun i _ => hP0 j i) (hPi j) (fun i _ => Set.mem_Ici.mpr (hlam i))
        simpa [smul_eq_mul] using this

end X5UE

namespace X5UE
open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P11

theorem ue {d : ℕ} (E : Superop (Fin d) (Fin d)) (hE : IsChannel E) (hU : IsUnital E)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : QAlgorithms.IsDensityMatrix rho) :
    vonNeumannEntropy rho ≤ vonNeumannEntropy (E rho) := by
  obtain ⟨n, K, hK, hEK⟩ := hE
  have hE' : E = krausApply K := funext hEK
  subst hE'
  have hent : ∀ X : Matrix (Fin d) (Fin d) ℂ, vonNeumannEntropy X =
      -(cfc (fun x : ℝ => x * Real.log x) X).trace.re := by
    intro X
    simp [vonNeumannEntropy, QAlgorithms.Papers.Independent.Information100.P39.quantumEntropy]
  rw [hent, hent, ent_eq hrho.1.1, ent_eq (kraus_psd K hrho.1).1]
  exact main K hK hU rho hrho.1

end X5UE

open QAlgorithms QAlgorithms.Papers.Independent.Dependency50.P11 in
open QAlgorithms.Papers.Independent.Information100.P23 (Operator) in
theorem solution {d : ℕ} (hd : 0 < d)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E) (hU : IsUnital E)
    (rho : Operator d) (hrho : IsDensityMatrix rho) :
    vonNeumannEntropy rho ≤ vonNeumannEntropy (E rho) := X5UE.ue E hE hU rho hrho
