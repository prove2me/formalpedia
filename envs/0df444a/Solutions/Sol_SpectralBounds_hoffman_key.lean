-- Prove2me | solution 1 for SpectralBounds.hoffman_key
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:30:37.005045+00:00
-- url     : https://prove2.me/submissions/b16ba8f8-299c-442a-9c55-a99ba10a6da5

module
public import Mathlib
public import Definitions.Def_SpectralLib_SpectralBounds
public import Theorems.Thm_SpectralBounds_iInf_le_quadForm
public import Theorems.Thm_SpectralBounds_dotProduct_adjMatrix_mulVec_comm

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open SpectralBounds
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)
open Matrix
omit [Nonempty V]
namespace SpectralBounds
theorem _root_.solution (x z : V → ℝ) (θ t : ℝ) (hx : G.adjMatrix ℝ *ᵥ x = θ • x)
    (hz : z ⬝ᵥ (G.adjMatrix ℝ *ᵥ z) = 0) :
    (⨅ i, hA.eigenvalues i) * (z ⬝ᵥ z - 2 * t * (z ⬝ᵥ x) + t ^ 2 * (x ⬝ᵥ x)) ≤
      -2 * t * θ * (z ⬝ᵥ x) + t ^ 2 * θ * (x ⬝ᵥ x) := by
  have h := iInf_le_quadForm hA (z - t • x)
  have hxz : x ⬝ᵥ (G.adjMatrix ℝ *ᵥ z) = θ * (z ⬝ᵥ x) := by
    rw [dotProduct_adjMatrix_mulVec_comm, hx, dotProduct_smul, smul_eq_mul]
  have hzx : z ⬝ᵥ x = x ⬝ᵥ z := dotProduct_comm _ _
  simp only [mulVec_sub, mulVec_smul, hx, sub_dotProduct, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, hz] at h
  rw [hxz] at h
  rw [← hzx] at h
  nlinarith [h]
end SpectralBounds
