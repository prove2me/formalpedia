-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.rz_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:05:05.395202+00:00
-- url     : https://prove2.me/submissions/67f1cab9-3698-4e9e-8a36-d04bea85b624

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentOnHyperbolicComplement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
noncomputable section
variable {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution (hG : (G.map τ).det ≠ 0) (φ : (Fin r → ℂ) →ₗ[ℂ] ℂ) (v : Fin r → ℂ) :
    hermC τ G v (rz τ G φ) = φ v := by
  have hM : G.map τ * (G.map τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hG)
  have key : ∀ a, ∑ b, τ (G a b) * (((G.map τ)⁻¹).mulVec
      (fun a => φ (fun j => if a = j then 1 else 0))) b = φ (fun j => if a = j then 1 else 0) := by
    intro a
    have h2 := congrFun (Matrix.mulVec_mulVec (fun a => φ (fun j => if a = j then 1 else 0))
      (G.map τ) (G.map τ)⁻¹) a
    rw [hM, Matrix.one_mulVec] at h2
    simpa [Matrix.mulVec, dotProduct] using h2
  have hv : v = ∑ a, v a • (fun j => if a = j then (1 : ℂ) else 0) := by
    funext j
    simp [Finset.sum_apply]
  calc hermC τ G v (rz τ G φ)
      = ∑ a, v a * ∑ b, τ (G a b) * (((G.map τ)⁻¹).mulVec
          (fun a => φ (fun j => if a = j then 1 else 0))) b := by
        simp only [hermC, rz, Complex.conj_conj, Finset.mul_sum, mul_assoc]
    _ = ∑ a, v a * φ (fun j => if a = j then 1 else 0) := by simp only [key]
    _ = φ v := by
        conv_rhs => rw [hv]
        simp only [map_sum, map_smul, smul_eq_mul]
end ReciprocityTheory.ChartRestriction.G.FD
