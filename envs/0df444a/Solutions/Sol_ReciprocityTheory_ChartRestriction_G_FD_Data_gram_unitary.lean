-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.gram_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:35.270662+00:00
-- url     : https://prove2.me/submissions/ad08714c-23a9-4aa0-ae25-a7c66bf31608

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowFixesComplementOfIsotropic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryComplementMoveOfIsotropic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_col_mul


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
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
variable (x : Frame X.Ψ r) (τ : X.Ψ) (g : Matrix (Fin r) (Fin r) ℂ)
  (hg : ∀ u w, hermC τ.1 X.Gm (Matrix.mulVec g u) (Matrix.mulVec g w) = hermC τ.1 X.Gm u w)
include hg
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution : gram τ.1 X.Gm (g * mat x τ) = gram τ.1 X.Gm (mat x τ) := by
  ext a b
  simp only [gram, Matrix.of_apply, col_mul, hg]
end ReciprocityTheory.ChartRestriction.G.FD.Data
