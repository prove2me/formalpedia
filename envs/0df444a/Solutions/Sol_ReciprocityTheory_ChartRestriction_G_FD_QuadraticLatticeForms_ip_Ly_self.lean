-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms.ip_Ly_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:00:07.639479+00:00
-- url     : https://prove2.me/submissions/87afd2e0-8251-416e-ba8e-da77672678ac

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealPlaceEmbeddings
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_DetToMatrixSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticLatticeForms
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_QuadraticLatticeForms_ip_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms
open Matrix NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms
theorem _root_.solution (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (v : Fin r → E) :
    ip X (Ly X y (X.embV v)) (Ly X y (X.embV v)) = Qy X y v := by
  rw [ip_self]
  rfl
end ReciprocityTheory.ChartRestriction.G.FD.QuadraticLatticeForms
