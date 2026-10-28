-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P04.relative_entropy_maximum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:18:03.468145+00:00
-- url     : https://prove2.me/submissions/71807e01-a87d-421f-8611-e3c269a3f3f1

import Definitions.Def_QAlgorithms_Defs_BasisCoherence
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P04_Model
set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexOrder
namespace QAlgorithms.Papers.Independent.Independent1.P04
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

lemma S173D_cfc_trace {n : Type} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma S173D_pt {d : ℝ} (hd : 0 < d) {x : ℝ} (hx : 0 ≤ x) :
    -(x * Real.log x) ≤ x * Real.log d + (1 / d - x) := by
  rcases hx.lt_or_eq with hx | hx
  · have h := Real.log_le_sub_one_of_pos (show 0 < 1 / (d * x) by positivity)
    rw [Real.log_div (by norm_num) (by positivity), Real.log_one, Real.log_mul hd.ne' hx.ne'] at h
    have : x * (1 / (d * x)) = 1 / d := by field_simp
    nlinarith
  · subst hx; simp; positivity

lemma S173F_ent_eq {d : ℕ} (σ : CoherenceMatrix d) (hσ : σ.IsHermitian) :
    naturalEntropy σ = -∑ i, hσ.eigenvalues i * Real.log (hσ.eigenvalues i) := by
  unfold naturalEntropy vnEntropy
  rw [S173D_cfc_trace hσ, Complex.re_sum]
  simp only [Complex.ofReal_re, Real.logb]
  rw [mul_neg, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have : Real.log 2 ≠ 0 := by positivity
  field_simp

lemma S173F_eig_sum {d : ℕ} (σ : CoherenceMatrix d) (hσ : IsDensityMatrix σ) :
    ∑ i, hσ.1.1.eigenvalues i = 1 := by
  have := hσ.1.1.trace_eq_sum_eigenvalues
  have h2 := hσ.2
  rw [this] at h2
  have h := congrArg Complex.re h2.symm
  simp only [Complex.one_re, Complex.re_sum, Complex.ofReal_re] at h
  exact h.symm

lemma S173F_ent_le {d : ℕ} (hd : 0 < d) (σ : CoherenceMatrix d) (hσ : IsDensityMatrix σ) :
    naturalEntropy σ ≤ Real.log d := by
  rw [S173F_ent_eq σ hσ.1.1]
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hs := S173F_eig_sum σ hσ
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    S173D_pt hdr (hσ.1.eigenvalues_nonneg i)
  have h2 : ∑ i, (hσ.1.1.eigenvalues i * Real.log d + (1 / d - hσ.1.1.eigenvalues i)) = Real.log d := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, hs]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp; ring
  rw [← Finset.sum_neg_distrib]
  linarith

lemma S173F_ent_nonneg {d : ℕ} (σ : CoherenceMatrix d) (hσ : IsDensityMatrix σ) :
    0 ≤ naturalEntropy σ := by
  rw [S173F_ent_eq σ hσ.1.1, neg_nonneg]
  have hs := S173F_eig_sum σ hσ
  refine Finset.sum_nonpos fun i _ => Real.mul_log_nonpos (hσ.1.eigenvalues_nonneg i) ?_
  rw [← hs]
  exact Finset.single_le_sum (fun j _ => hσ.1.eigenvalues_nonneg j) (Finset.mem_univ i)

lemma S173F_deph_dens {d : ℕ} (ρ : CoherenceMatrix d) (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (dephasedMatrix ρ) := by
  refine ⟨?_, ?_⟩
  · unfold dephasedMatrix
    rw [Matrix.posSemidef_diagonal_iff]
    intro i; exact hρ.1.diag_nonneg
  · unfold dephasedMatrix
    rw [Matrix.trace_diagonal, ← hρ.2]; rfl

/-- entropy zero for an idempotent PSD matrix -/
lemma S173F_ent_idem {d : ℕ} (P : CoherenceMatrix d) (hP : P.IsHermitian) (hPP : P * P = P) :
    naturalEntropy P = 0 := by
  rw [S173F_ent_eq P hP]
  have hD : star (hP.eigenvectorUnitary : CoherenceMatrix d) * P * (hP.eigenvectorUnitary : CoherenceMatrix d) =
      Matrix.diagonal (RCLike.ofReal ∘ hP.eigenvalues) := by
    have hs := hP.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hs
    have hu := Unitary.star_mul_self_of_mem hP.eigenvectorUnitary.2
    generalize (hP.eigenvectorUnitary : CoherenceMatrix d) = U at *
    generalize (Matrix.diagonal (RCLike.ofReal ∘ hP.eigenvalues) : CoherenceMatrix d) = D at *
    subst hs
    calc star U * (U * D * star U) * U
        = (star U * U) * D * (star U * U) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hu, one_mul, mul_one]
  have hu := Unitary.mul_star_self_of_mem hP.eigenvectorUnitary.2
  set U := (hP.eigenvectorUnitary : CoherenceMatrix d)
  have hsq : Matrix.diagonal (RCLike.ofReal ∘ hP.eigenvalues) * Matrix.diagonal (RCLike.ofReal ∘ hP.eigenvalues)
      = (Matrix.diagonal (RCLike.ofReal ∘ hP.eigenvalues) : CoherenceMatrix d) := by
    rw [← hD]
    calc star U * P * U * (star U * P * U) = star U * P * (U * star U) * P * U := by
          simp only [Matrix.mul_assoc]
      _ = star U * (P * P) * U := by rw [hu, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPP]
  rw [neg_eq_zero]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h := congrFun (congrFun hsq i) i
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at h
  simp only [Function.comp_apply] at h
  have h' : hP.eigenvalues i * hP.eigenvalues i = hP.eigenvalues i := by exact_mod_cast h
  have : hP.eigenvalues i = 0 ∨ hP.eigenvalues i = 1 := by
    rcases mul_eq_zero.mp (show hP.eigenvalues i * (hP.eigenvalues i - 1) = 0 by linarith) with h0 | h1
    · left; exact h0
    · right; linarith
  rcases this with h0 | h1
  · rw [h0]; simp
  · rw [h1]; simp

lemma S173F_ent_scalar {d : ℕ} (hd : 0 < d) :
    naturalEntropy (((d : ℂ)⁻¹) • (1 : CoherenceMatrix d)) = Real.log d := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  unfold naturalEntropy vnEntropy
  have e : ((d : ℂ)⁻¹ • (1 : CoherenceMatrix d)) = algebraMap ℝ (CoherenceMatrix d) ((d : ℝ)⁻¹) := by
    rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]; push_cast; rfl
  rw [e, cfc_algebraMap, Algebra.algebraMap_eq_smul_one, Matrix.trace_smul, Matrix.trace_one]
  simp only [Fintype.card_fin, Complex.smul_re, Complex.natCast_re, smul_eq_mul, Real.logb, Real.log_inv]
  have : Real.log 2 ≠ 0 := by positivity
  field_simp

lemma S173F_pure (d : ℕ) (hd : 0 < d) :
    pureDensity (uniformCoherentVector d) = Matrix.of fun _ _ => ((d : ℂ)⁻¹) := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  ext a b
  simp only [pureDensity, uniformCoherentVector, Matrix.of_apply]
  change ((Real.sqrt d)⁻¹ : ℂ) * (starRingEnd ℂ) ((Real.sqrt d)⁻¹ : ℂ) = _
  rw [map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hdr.le]
  simp

end QAlgorithms.Papers.Independent.Independent1.P04

open QAlgorithms QAlgorithms.Papers.Independent.Independent1.P04 in
theorem solution (d : ℕ) (hd : 0 < d) :
    (∀ rho : CoherenceMatrix d, IsDensityMatrix rho →
      entropyCoherence d rho ≤ naturalEntropy (dephasedMatrix rho) ∧
        naturalEntropy (dephasedMatrix rho) ≤ Real.log d) ∧
    IsState (uniformCoherentVector d) ∧
    entropyCoherence d (pureDensity (uniformCoherentVector d)) = Real.log d := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨fun rho hrho => ⟨?_, S173F_ent_le hd _ (S173F_deph_dens rho hrho)⟩, ?_, ?_⟩
  · unfold entropyCoherence
    linarith [S173F_ent_nonneg rho hrho]
  · unfold IsState
    rw [EuclideanSpace.norm_eq]
    simp only [uniformCoherentVector]
    change Real.sqrt (∑ _i : Fin d, ‖((Real.sqrt d)⁻¹ : ℂ)‖ ^ 2) = 1
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt hdr.le, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_inv_cancel₀ hdr.ne', Real.sqrt_one]
  · rw [S173F_pure d hd]
    unfold entropyCoherence
    have hdeph : dephasedMatrix (Matrix.of fun _ _ => ((d : ℂ)⁻¹) : CoherenceMatrix d) =
        ((d : ℂ)⁻¹) • (1 : CoherenceMatrix d) := by
      ext i j
      simp only [dephasedMatrix, Matrix.diagonal_apply, Matrix.of_apply, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp
    have hherm : (Matrix.of fun _ _ => ((d : ℂ)⁻¹) : CoherenceMatrix d).IsHermitian := by
      ext i j; simp [Matrix.conjTranspose_apply]
    have hidem : (Matrix.of fun _ _ => ((d : ℂ)⁻¹) : CoherenceMatrix d) *
        (Matrix.of fun _ _ => ((d : ℂ)⁻¹)) = Matrix.of fun _ _ => ((d : ℂ)⁻¹) := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      field_simp
    rw [hdeph, S173F_ent_scalar hd, S173F_ent_idem _ hherm hidem, sub_zero]
