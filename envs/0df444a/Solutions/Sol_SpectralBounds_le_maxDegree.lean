-- Prove2me | solution 1 for SpectralBounds.le_maxDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:25:04.878813+00:00
-- url     : https://prove2.me/submissions/62704137-e996-4235-a3d5-08d404e1da43

module
public import Mathlib
public import Definitions.Def_SpectralLib_SpectralBounds
public import Theorems.Thm_SpectralBounds_exists_unit_eigenvector_iSup

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open SpectralBounds
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)
open Matrix
namespace SpectralBounds
theorem _root_.solution : ⨆ i, hA.eigenvalues i ≤ G.maxDegree := by
  obtain ⟨x, hx, hxx⟩ := exists_unit_eigenvector_iSup hA
  set lam := ⨆ i, hA.eigenvalues i
  obtain ⟨u, -, hu⟩ := exists_max_image univ (fun v => |x v|) univ_nonempty
  have hpos : 0 < |x u| := by
    by_contra hneg
    have h0 : ∀ v, x v = 0 := fun v =>
      abs_eq_zero.1 (le_antisymm ((hu v (mem_univ v)).trans (not_lt.1 hneg)) (abs_nonneg _))
    simp [dotProduct, h0] at hxx
  have hxu : lam * x u = ∑ w ∈ G.neighborFinset u, x w := by
    rw [← adjMatrix_mulVec_apply, hx]
    simp
  have hbound : |lam| * |x u| ≤ G.maxDegree * |x u| := by
    rw [← abs_mul, hxu]
    calc |∑ w ∈ G.neighborFinset u, x w| ≤ ∑ w ∈ G.neighborFinset u, |x w| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ w ∈ G.neighborFinset u, |x u| := sum_le_sum fun w _ => hu w (mem_univ w)
      _ = G.degree u * |x u| := by simp
      _ ≤ G.maxDegree * |x u| := by
          gcongr
          exact_mod_cast G.degree_le_maxDegree u
  exact (le_abs_self lam).trans (le_of_mul_le_mul_right hbound hpos)
end SpectralBounds
