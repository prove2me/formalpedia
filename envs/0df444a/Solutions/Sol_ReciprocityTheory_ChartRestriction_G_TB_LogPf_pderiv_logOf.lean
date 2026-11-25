-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_logOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:54:20.899173+00:00
-- url     : https://prove2.me/submissions/9bdbe38b-3869-46f7-8ba4-c309115b0411

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_om_closed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_prim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {d : ℕ} (G : FGLaw k d)
variable [Algebra ℚ k]
namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf
theorem _root_.solution (i a : Fin d) : pderiv k ((0 : Fin 1), a) (logOf G i) = Om G i a := by
  unfold logOf
  refine pderiv_prim _ ?_ _
  rintro ⟨a0, a'⟩ ⟨c0, c'⟩
  have h0 : a0 = 0 := Subsingleton.elim _ _
  have h1 : c0 = 0 := Subsingleton.elim _ _
  subst h0 h1
  exact om_closed G i a' c'
end ReciprocityTheory.ChartRestriction.G.TB.LogPf
