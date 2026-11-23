-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.gramPos_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:34.948294+00:00
-- url     : https://prove2.me/submissions/89f0bbbb-4b03-4722-8b4c-21ace9f86a8c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_gram_isHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Matrix NumberField
open scoped ComplexOrder ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (x : Frame X.Ψ r) (τ : X.Ψ) : (X.gramPos x τ).IsHermitian := by
  exact (gram_isHermitian τ.1 X.Gm_herm (mat x τ)).submatrix (Fin.castLE X.p0_le)
end ReciprocityTheory.ChartRestriction.G.FD.Data
