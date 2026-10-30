-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P40.commutingMinimum
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-29T00:10:13.463275+00:00
-- url     : https://prove2.me/submissions/97078836-b755-4295-bca2-8966c5c8e0c5

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_minimumAt_attained
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_relativeEntropy_pinch_le

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

namespace QAlgorithms.Papers.Independent.Gap48.P40

namespace CMAux

/-- Pinching in the basis given by the columns of `U`. -/
def pinch {d : ℕ} (U : Mat d) (X : Mat d) : Mat d :=
  U * Matrix.diagonal (fun i => (Uᴴ * X * U) i i) * Uᴴ

lemma pinch_sub {d : ℕ} (U X Y : Mat d) : pinch U X - pinch U Y = pinch U (X - Y) := by
  simp only [pinch, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply, ← Matrix.diagonal_sub]

lemma pinch_density {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (X : Mat d)
    (hX : IsDensityMatrix X) : IsDensityMatrix (pinch (U : Mat d) X) := by
  have hY := hX.1.conjTranspose_mul_mul_same (U : Mat d)
  have hUU : (U : Mat d)ᴴ * (U : Mat d) = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.1 U.2
  have hUU' : (U : Mat d) * (U : Mat d)ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.1 U.2
  refine ⟨(Matrix.PosSemidef.diagonal fun i => hY.diag_nonneg).mul_mul_conjTranspose_same _, ?_⟩
  rw [pinch, Matrix.trace_mul_cycle, hUU, Matrix.one_mul, Matrix.trace_diagonal]
  change ((U : Mat d)ᴴ * X * (U : Mat d)).trace = 1
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU', Matrix.one_mul, hX.2]

end CMAux

open CMAux in
theorem cm_main {d : ℕ} (hd : 2 ≤ d) (N : Mat d → ℝ) (hN : IsUINorm N)
    (T : ℝ) (hT : 0 ≤ T ∧ T ≤ N (matrixF d)) :
    ∃ rho sigma : Mat d, IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧
      N (rho - sigma) = T ∧ sigma * (rho - sigma) = (rho - sigma) * sigma ∧
      relativeEntropy rho sigma = minimumAt d N T := by
  obtain ⟨rho, sigma, hr, hs, hNT, hD⟩ := minimumAt_attained hd N hN T hT
  have hH : (rho - sigma).IsHermitian := hr.1.isHermitian.sub hs.1.isHermitian
  set U := hH.eigenvectorUnitary
  have hUU : (U : Mat d)ᴴ * (U : Mat d) = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.1 U.2
  have hspec : rho - sigma =
      (U : Mat d) * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) * (U : Mat d)ᴴ := by
    conv_lhs => rw [hH.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rfl
  have hdiag : (U : Mat d)ᴴ * (rho - sigma) * (U : Mat d) =
      Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
    have h := congrArg (fun M => (U : Mat d)ᴴ * M * (U : Mat d)) hspec
    rw [h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hUU, Matrix.one_mul, Matrix.mul_assoc,
      hUU, Matrix.mul_one]
  have hfix : pinch (U : Mat d) (rho - sigma) = rho - sigma := by
    rw [pinch, hdiag]
    refine Eq.trans ?_ hspec.symm
    congr 2
    ext i j
    by_cases h : i = j <;> simp [h]
  have hΔ : pinch (U : Mat d) rho - pinch (U : Mat d) sigma = rho - sigma := by
    rw [pinch_sub, hfix]
  refine ⟨pinch (U : Mat d) rho, pinch (U : Mat d) sigma, pinch_density U rho hr,
    pinch_density U sigma hs, by rw [hΔ, hNT], ?_, ?_⟩
  · rw [hΔ, hspec, pinch]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U : Mat d)ᴴ (U : Mat d), hUU, Matrix.one_mul,
      ← Matrix.mul_assoc (U : Mat d)ᴴ (U : Mat d), hUU, Matrix.one_mul,
      ← Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal _),
      ← Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal _),
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    simp only [mul_comm]
  · apply le_antisymm
    · rw [← hD]; exact relativeEntropy_pinch_le U rho sigma hr hs
    · apply sInf_le
      exact ⟨_, _, pinch_density U rho hr, pinch_density U sigma hs, by rw [hΔ, hNT], rfl⟩

end QAlgorithms.Papers.Independent.Gap48.P40

open QAlgorithms.Papers.Independent.Gap48.P40 in
theorem solution {d : ℕ} (hd : 2 ≤ d) (N : Mat d → ℝ) (hN : IsUINorm N)
    (T : ℝ) (hT : 0 ≤ T ∧ T ≤ N (matrixF d)) :
    ∃ rho sigma : Mat d, IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧
      N (rho - sigma) = T ∧ sigma * (rho - sigma) = (rho - sigma) * sigma ∧
      relativeEntropy rho sigma = minimumAt d N T :=
  cm_main hd N hN T hT

end
