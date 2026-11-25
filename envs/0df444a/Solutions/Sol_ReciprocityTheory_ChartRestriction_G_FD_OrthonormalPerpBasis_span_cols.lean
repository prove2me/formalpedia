-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis.span_cols
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:59:52.660991+00:00
-- url     : https://prove2.me/submissions/d3cfd0c5-4f31-414e-bf98-14f06276d355

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PosCoordNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
open NumberField Complex Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (w : Fin r → ℂ) :
    ∃ c : Fin r → ℂ, w = ∑ a, c a • col (mat x τ) a := by
  have hdet : IsUnit (mat x τ).det := isUnit_iff_ne_zero.mpr (hx τ).1
  refine ⟨(mat x τ)⁻¹ *ᵥ w, ?_⟩
  have hBB : mat x τ *ᵥ ((mat x τ)⁻¹ *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  calc w = mat x τ *ᵥ ((mat x τ)⁻¹ *ᵥ w) := hBB.symm
    _ = _ := by
      funext k
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
