-- Prove2me | solution 1 for QEC.Coding.SmallSetExpansion.LinearMap.IsSymmetric.norm_sq_apply_le_of_abs_eigenvalues_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:46:37.033204+00:00
-- url     : https://prove2.me/submissions/545e6a5c-1860-4fed-b94d-d54923a15dd7

import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSpectrum

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.SmallSetExpansion
universe u
variable {V : Type u}
namespace QEC.Coding.SmallSetExpansion
namespace LinearMap.IsSymmetric
theorem _root_.solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    {spectral : ℝ} (hSpectralNonnegative : 0 ≤ spectral)
    (hEigen : ∀ i : Fin (Module.finrank ℂ E),
      |hT.eigenvalues rfl i| ≤ spectral)
    (x : E) :
    ‖T x‖ ^ 2 ≤ spectral ^ 2 * ‖x‖ ^ 2 := by
  let b := hT.eigenvectorBasis (n := Module.finrank ℂ E) rfl
  have hCoordinate (i : Fin (Module.finrank ℂ E)) :
      ‖((hT.eigenvalues rfl i : ℝ) : ℂ) * (b.repr x) i‖ ^ 2 ≤
        spectral ^ 2 * ‖(b.repr x) i‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hAbsNonnegative : 0 ≤ |hT.eigenvalues rfl i| := abs_nonneg _
    have hSquare : |hT.eigenvalues rfl i| ^ 2 ≤ spectral ^ 2 :=
      (sq_le_sq₀ hAbsNonnegative hSpectralNonnegative).2 (hEigen i)
    calc
      (|hT.eigenvalues rfl i| * ‖(b.repr x) i‖) ^ 2 =
          |hT.eigenvalues rfl i| ^ 2 * ‖(b.repr x) i‖ ^ 2 := by ring
      _ ≤ spectral ^ 2 * ‖(b.repr x) i‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hSquare (sq_nonneg _)
  calc
    ‖T x‖ ^ 2 = ‖b.repr (T x)‖ ^ 2 := by
      rw [b.repr.norm_map]
    _ = ∑ i, ‖(b.repr (T x)) i‖ ^ 2 :=
      EuclideanSpace.norm_sq_eq _
    _ = ∑ i, ‖((hT.eigenvalues rfl i : ℝ) : ℂ) *
          (b.repr x) i‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [show (b.repr (T x)) i =
          ((hT.eigenvalues rfl i : ℝ) : ℂ) * (b.repr x) i by
        simpa [b] using
          hT.eigenvectorBasis_apply_self_apply rfl x i]
    _ ≤ ∑ i, spectral ^ 2 * ‖(b.repr x) i‖ ^ 2 :=
      Finset.sum_le_sum fun i _hi => hCoordinate i
    _ = spectral ^ 2 * ∑ i, ‖(b.repr x) i‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ = spectral ^ 2 * ‖b.repr x‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
    _ = spectral ^ 2 * ‖x‖ ^ 2 := by rw [b.repr.norm_map]
end LinearMap.IsSymmetric
end QEC.Coding.SmallSetExpansion
