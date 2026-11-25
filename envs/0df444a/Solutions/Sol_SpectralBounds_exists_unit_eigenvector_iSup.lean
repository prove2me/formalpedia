-- Prove2me | solution 1 for SpectralBounds.exists_unit_eigenvector_iSup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:19:35.075716+00:00
-- url     : https://prove2.me/submissions/b8d0fbf4-10f8-467d-b116-7c3619f4e190

module
public import Mathlib
public import Definitions.Def_SpectralLib_SpectralBounds

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open SpectralBounds
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)
variable {W : Type*} [Fintype W] [DecidableEq W] {M : Matrix W W ℝ}
open Matrix
namespace SpectralBounds
theorem _root_.solution [Nonempty W] (hM : M.IsHermitian) :
    ∃ x : W → ℝ, M *ᵥ x = (⨆ i, hM.eigenvalues i) • x ∧ x ⬝ᵥ x = 1 := by
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := hM.eigenvalues)
  refine ⟨⇑(hM.eigenvectorBasis i), ?_, ?_⟩
  · rw [hM.mulVec_eigenvectorBasis, hi]
  · have h1 := hM.eigenvectorBasis.orthonormal.1 i
    have h2 := real_inner_self_eq_norm_sq (hM.eigenvectorBasis i)
    rw [h1, one_pow, EuclideanSpace.inner_eq_star_dotProduct] at h2
    simpa [dotProduct_comm] using h2
end SpectralBounds
