-- Prove2me | solution 1 for SYKFastMix.FastMixing.traceMoment_opNorm_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:16:44.184612+00:00
-- url     : https://prove2.me/submissions/571e0beb-21e4-47cc-ba50-d4491c8fc1f2

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Coefficients

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace SYKFastMix.FastMixing

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma hermitian_norm_eq_eigenvalues_norm (B : Mat ι) (hB : B.IsHermitian) :
    ‖B‖ = ‖fun i ↦ (hB.eigenvalues i : ℂ)‖ := by
  conv_lhs => rw [hB.spectral_theorem]
  rw [StarAlgEquiv.norm_map, Matrix.l2_opNorm_diagonal]
  rfl

lemma traceMoment_eq_sum_eigenvalues_pow (p : ℕ) (A : Mat ι) :
    traceMoment p A = ∑ i, ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i) ^ p := by
  let hB := Matrix.isHermitian_conjTranspose_mul_self A
  unfold traceMoment
  conv_lhs => rw [hB.spectral_theorem, ← map_pow]
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.diagonal_pow, Matrix.trace_diagonal]
  simp only [Complex.re_sum, Pi.pow_apply, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change (((hB.eigenvalues i : ℝ) : ℂ) ^ p).re = _
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

lemma traceMoment_nonneg (p : ℕ) (A : Mat ι) : 0 ≤ traceMoment p A := by
  rw [traceMoment_eq_sum_eigenvalues_pow]
  exact Finset.sum_nonneg fun i _ ↦ pow_nonneg (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i) _

lemma opNorm_pow_le_traceMoment [Nonempty ι] (p : ℕ) (A : Mat ι) :
    SYKEdge.opNorm A ^ (2*p) ≤ traceMoment p A := by
  let hB := Matrix.isHermitian_conjTranspose_mul_self A
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ hB.eigenvalues Finset.univ_nonempty
  have hn (j : ι) : 0 ≤ hB.eigenvalues j := Matrix.eigenvalues_conjTranspose_mul_self_nonneg A j
  have he : ‖Aᴴ * A‖ = hB.eigenvalues i := by
    rw [hermitian_norm_eq_eigenvalues_norm _ hB]
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (hn i)).mpr
      intro j
      change ‖(hB.eigenvalues j : ℂ)‖ ≤ _
      rw [Complex.norm_real, Real.norm_of_nonneg (hn j)]
      exact hmax j (Finset.mem_univ j)
    · have h := norm_le_pi_norm (fun j ↦ (hB.eigenvalues j : ℂ)) i
      simpa only [Complex.norm_real, Real.norm_of_nonneg (hn i)] using h
  rw [traceMoment_eq_sum_eigenvalues_pow]
  calc
    SYKEdge.opNorm A ^ (2*p) = ‖Aᴴ * A‖ ^ p := by
      change ‖A‖ ^ (2*p) = _
      rw [Matrix.l2_opNorm_conjTranspose_mul_self, ← pow_two, pow_mul]
    _ = hB.eigenvalues i ^ p := by rw [he]
    _ ≤ ∑ j, hB.eigenvalues j ^ p :=
      Finset.single_le_sum (fun j _ ↦ pow_nonneg (hn j) p) (Finset.mem_univ i)

lemma traceMoment_le_card_mul_opNorm_pow (p : ℕ) (A : Mat ι) :
    traceMoment p A ≤ (Fintype.card ι : ℝ) * SYKEdge.opNorm A ^ (2*p) := by
  let hB := Matrix.isHermitian_conjTranspose_mul_self A
  have hn (j : ι) : 0 ≤ hB.eigenvalues j := Matrix.eigenvalues_conjTranspose_mul_self_nonneg A j
  have he (j : ι) : hB.eigenvalues j ≤ ‖Aᴴ * A‖ := by
    rw [hermitian_norm_eq_eigenvalues_norm _ hB]
    have h := norm_le_pi_norm (fun j ↦ (hB.eigenvalues j : ℂ)) j
    simpa only [Complex.norm_real, Real.norm_of_nonneg (hn j)] using h
  rw [traceMoment_eq_sum_eigenvalues_pow]
  calc
    ∑ j, hB.eigenvalues j ^ p ≤ ∑ _ : ι, ‖Aᴴ * A‖ ^ p :=
      Finset.sum_le_sum (fun j _ ↦ pow_le_pow_left₀ (hn j) (he j) p)
    _ = (Fintype.card ι : ℝ) * SYKEdge.opNorm A ^ (2*p) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      congr 1
      change ‖Aᴴ * A‖ ^ p = ‖A‖ ^ (2*p)
      rw [Matrix.l2_opNorm_conjTranspose_mul_self, ← pow_two, pow_mul]

end SYKFastMix.FastMixing

open SYKFastMix.FastMixing

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (p : ℕ) (A : Mat ι) :
    SYKEdge.opNorm A ^ (2*p) ≤ traceMoment p A ∧
      traceMoment p A ≤ (Fintype.card ι : ℝ) * SYKEdge.opNorm A ^ (2*p) :=
  ⟨opNorm_pow_le_traceMoment p A, traceMoment_le_card_mul_opNorm_pow p A⟩
