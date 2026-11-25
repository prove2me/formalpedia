-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis.ortho_h
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:59:44.896648+00:00
-- url     : https://prove2.me/submissions/3a4b6b7b-ba4c-40de-97c9-1a3f25dc0de9

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
theorem _root_.solution {x : Frame X.Ψ r} (ho : X.IsOrtho x) (τ : X.Ψ) (a b : Fin r) :
    hermC τ.1 X.Gm (col (mat x τ) a) (col (mat x τ) b) =
      if a = b then ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) else 0 := by
  have h := congrFun (congrFun (ho τ) a) b
  rw [Matrix.diagonal_apply] at h
  exact h
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
