-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P17.minimumEigenvalueSeparation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T12:07:20.438875+00:00
-- url     : https://prove2.me/submissions/78c19585-13a5-4868-9c62-bb179f7d35aa

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P17

noncomputable section

set_option linter.unusedSectionVars false

open scoped Matrix ComplexOrder

namespace X6ME

open QAlgorithms

variable {J : Type*} [Fintype J] [DecidableEq J]

lemma cfc_spec {X : Matrix J J ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    cfc f X = (hX.eigenvectorUnitary : Matrix J J ℂ) *
      Matrix.diagonal (fun i => ((f (hX.eigenvalues i) : ℝ) : ℂ)) *
      star (hX.eigenvectorUnitary : Matrix J J ℂ) := by
  rw [hX.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rfl

lemma spec {X : Matrix J J ℂ} (hX : X.IsHermitian) :
    X = (hX.eigenvectorUnitary : Matrix J J ℂ) *
      Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) *
      star (hX.eigenvectorUnitary : Matrix J J ℂ) := by
  have hs := hX.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  exact hs

lemma trace_cfc {X : Matrix J J ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    (cfc f X).trace = ∑ i, ((f (hX.eigenvalues i) : ℝ) : ℂ) := by
  have hU := Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2
  rw [cfc_spec hX, Matrix.trace_mul_cycle, hU, Matrix.one_mul, Matrix.trace_diagonal]

lemma sq_eq_cfc {X : Matrix J J ℂ} (hX : X.IsHermitian) :
    X * X = cfc (fun x : ℝ => x ^ 2) X := by
  have hU := Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2
  rw [cfc_spec hX]
  conv_lhs => rw [spec hX]
  set U := (hX.eigenvectorUnitary : Matrix J J ℂ)
  calc U * Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) * star U *
        (U * Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) * star U)
      = U * (Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) * (star U * U) *
        Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ))) * star U := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [hU, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
        congr 2; funext i; push_cast; ring

lemma traceNorm_herm {X : Matrix J J ℂ} (hX : X.IsHermitian) :
    traceNorm X = ∑ i, |hX.eigenvalues i| := by
  rw [traceNorm, hX.eq, sq_eq_cfc hX, ← cfc_comp Real.sqrt (fun x : ℝ => x ^ 2) X]
  have : (Real.sqrt ∘ fun x : ℝ => x ^ 2) = fun x => |x| := by
    funext x; simp [Real.sqrt_sq_eq_abs]
  rw [this, trace_cfc hX, Complex.re_sum]
  simp

/-- real quadratic form -/
def q (X : Matrix J J ℂ) (x : J → ℂ) : ℝ := (star x ⬝ᵥ X *ᵥ x).re

lemma q_add (X Y : Matrix J J ℂ) (x : J → ℂ) : q (X + Y) x = q X x + q Y x := by
  simp [q, Matrix.add_mulVec, dotProduct_add]

lemma qf_spec {X : Matrix J J ℂ} (hX : X.IsHermitian) (x : J → ℂ) :
    ∃ c : J → ℝ, (∀ k, 0 ≤ c k) ∧ ∑ k, c k = (star x ⬝ᵥ x).re ∧
      q X x = ∑ k, hX.eigenvalues k * c k := by
  have hU := Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2
  have hU' := Unitary.mul_star_self_of_mem hX.eigenvectorUnitary.2
  set U := (hX.eigenvectorUnitary : Matrix J J ℂ)
  set v := star U *ᵥ x
  have hUU : (star U)ᴴ = U := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  refine ⟨fun k => Complex.normSq (v k), fun k => Complex.normSq_nonneg _, ?_, ?_⟩
  · have : star x ⬝ᵥ x = star v ⬝ᵥ v := by
      simp only [v, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hUU]
      rw [hU', Matrix.vecMul_one]
    rw [this]
    simp only [dotProduct, Complex.re_sum, Pi.star_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.normSq_apply]; simp [Complex.mul_re]
  · have hspec : X = U * Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) * star U := by
      exact spec hX
    have : star x ⬝ᵥ X *ᵥ x =
        star v ⬝ᵥ Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) *ᵥ v := by
      conv_lhs => rw [hspec]
      simp only [v, Matrix.star_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hUU]
    rw [q, this]
    simp only [dotProduct, Matrix.mulVec_diagonal, Complex.re_sum, Pi.star_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.normSq_apply]; simp [Complex.mul_re, Complex.mul_im]; ring

lemma minEig_le {σ : Matrix J J ℂ} (hσ : σ.IsHermitian) (j : J) :
    minEigenvalue σ ≤ hσ.eigenvalues j := by
  unfold minEigenvalue ascEigenvalues
  have hpos : 0 < Fintype.card J := Fintype.card_pos_iff.mpr ⟨j⟩
  rw [dif_pos hpos, dif_pos hσ]
  show hσ.eigenvalues₀ (Fin.rev ⟨0, hpos⟩) ≤ hσ.eigenvalues₀ _
  apply hσ.eigenvalues₀_antitone
  rw [Fin.le_def]; simp only [Fin.val_rev]
  have := ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j).isLt
  omega

lemma minEig_eq [Nonempty J] {σ : Matrix J J ℂ} (hσ : σ.IsHermitian) :
    ∃ j, minEigenvalue σ = hσ.eigenvalues j := by
  have hpos : 0 < Fintype.card J := Fintype.card_pos
  refine ⟨Fintype.equivOfCardEq (Fintype.card_fin _) (Fin.rev ⟨0, hpos⟩), ?_⟩
  unfold minEigenvalue ascEigenvalues
  rw [dif_pos hpos, dif_pos hσ]
  simp [Matrix.IsHermitian.eigenvalues]

lemma q_lower {X : Matrix J J ℂ} (hX : X.IsHermitian) (x : J → ℂ) :
    minEigenvalue X * (star x ⬝ᵥ x).re ≤ q X x := by
  obtain ⟨c, hc0, hcs, hq⟩ := qf_spec hX x
  rw [hq, ← hcs, Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (minEig_le hX k) (hc0 k)

lemma q_eig {X : Matrix J J ℂ} (hX : X.IsHermitian) (j : J) :
    q X (hX.eigenvectorBasis j) = hX.eigenvalues j ∧
      (star (⇑(hX.eigenvectorBasis j)) ⬝ᵥ ⇑(hX.eigenvectorBasis j)).re = 1 := by
  have hn : (star (⇑(hX.eigenvectorBasis j)) ⬝ᵥ ⇑(hX.eigenvectorBasis j)) = 1 := by
    have := hX.eigenvectorBasis.orthonormal.1 j
    have h2 : inner ℂ (hX.eigenvectorBasis j) (hX.eigenvectorBasis j) = (1 : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K, this]; simp
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h2
    rw [← h2, dotProduct_comm]
  refine ⟨?_, by rw [hn]; simp⟩
  rw [q, hX.mulVec_eigenvectorBasis j, dotProduct_smul, hn]
  simp

lemma neg_part (μ c : J → ℝ) (hc0 : ∀ k, 0 ≤ c k) (hc1 : ∑ k, c k = 1) (hμ : ∑ k, μ k = 0) :
    -(∑ k, μ k * c k) ≤ 2⁻¹ * ∑ k, |μ k| := by
  have hle : ∀ k, c k ≤ 1 := fun k => by
    rw [← hc1]; exact Finset.single_le_sum (fun i _ => hc0 i) (Finset.mem_univ k)
  have h1 : -(∑ k, μ k * c k) ≤ ∑ k, (|μ k| - μ k) / 2 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    have ha : 0 ≤ (|μ k| - μ k) / 2 := by linarith [le_abs_self (μ k)]
    have hb : -(μ k * c k) ≤ (|μ k| - μ k) / 2 * c k := by
      rcases le_or_gt 0 (μ k) with h | h
      · rw [abs_of_nonneg h]; simp; nlinarith [hc0 k]
      · rw [abs_of_neg h]; nlinarith [hc0 k]
    calc -(μ k * c k) ≤ (|μ k| - μ k) / 2 * c k := hb
      _ ≤ (|μ k| - μ k) / 2 * 1 := mul_le_mul_of_nonneg_left (hle k) ha
      _ = _ := mul_one _
  have h2 : ∑ k, (|μ k| - μ k) / 2 = 2⁻¹ * ∑ k, |μ k| := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib, hμ]; ring
  linarith

lemma one_side [Nonempty J] (A B : Matrix J J ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (htrace : A.trace = B.trace) :
    minEigenvalue B - 2⁻¹ * traceNorm (A - B) ≤ minEigenvalue A := by
  have hD : (A - B).IsHermitian := hA.sub hB
  obtain ⟨j, hj⟩ := minEig_eq hA
  obtain ⟨hqA, hn⟩ := q_eig hA j
  set x := ⇑(hA.eigenvectorBasis j)
  have hsplit : q A x = q B x + q (A - B) x := by
    rw [← q_add]; congr 1; abel
  have hBx := q_lower hB x
  rw [hn, mul_one] at hBx
  obtain ⟨c, hc0, hcs, hq⟩ := qf_spec hD x
  rw [hn] at hcs
  have hμ : ∑ k, hD.eigenvalues k = 0 := by
    have := hD.trace_eq_sum_eigenvalues
    rw [Matrix.trace_sub, htrace, sub_self] at this
    have := congrArg Complex.re this
    simpa [Complex.re_sum] using this.symm
  have := neg_part _ c hc0 hcs hμ
  rw [traceNorm_herm hD]
  linarith

end X6ME

open QAlgorithms in
theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (A B : Matrix I I ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (htrace : A.trace = B.trace) :
    |minEigenvalue A - minEigenvalue B| ≤ traceDistance A B := by
  have h1 := X6ME.one_side A B hA.1 hB.1 htrace
  have h2 := X6ME.one_side B A hB.1 hA.1 htrace.symm
  have hs : traceNorm (B - A) = traceNorm (A - B) := by
    unfold traceNorm
    rw [show B - A = -(A - B) by abel, Matrix.conjTranspose_neg, neg_mul_neg]
  rw [hs] at h2
  unfold traceDistance
  rw [abs_le]; constructor <;> linarith
