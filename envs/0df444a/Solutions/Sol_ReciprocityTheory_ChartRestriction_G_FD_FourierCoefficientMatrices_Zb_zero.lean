-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices.Zb_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:34:01.445652+00:00
-- url     : https://prove2.me/submissions/7c51ae15-11d1-4f87-bd43-dfdd310b05e2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealEmbeddingCharacters
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientMatrices
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FourierCoefficientMatrices_zmat_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  (u : Fin 2 → Fin r → E)
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices
theorem _root_.solution (x : Frame X.Ψ r) : X.Zb u 0 x = x := by
  funext τ
  show X.zmat u 0 τ * mat x τ = x τ
  rw [zmat_zero, one_mul]
  rfl
end ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices
