-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis.ppos_ortho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:59:47.792257+00:00
-- url     : https://prove2.me/submissions/f392bc74-203c-4b4b-a964-63026a78339e

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
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.ppos x τ v = ∑ a : Fin X.p0, hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le a)) •
      col (mat x τ) (Fin.castLE X.p0_le a) := by
  have hg : X.gramPos x τ = 1 := by
    ext a b
    simp only [Data.gramPos, Matrix.submatrix_apply, ho τ, Matrix.diagonal_apply, Fin.castLE_inj,
      Matrix.one_apply]
    split_ifs with h
    · simp [sgn, Fin.coe_castLE, a.isLt]
    · rfl
  unfold Data.ppos
  rw [hg, Matrix.inv_eq_left_inv (mul_one (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ))]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  simp [Matrix.one_apply]
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
