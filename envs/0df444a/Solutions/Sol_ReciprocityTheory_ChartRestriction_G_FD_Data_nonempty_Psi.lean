-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.nonempty_Psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:05.741881+00:00
-- url     : https://prove2.me/submissions/3871a1bf-7bcc-4ba4-8d10-388bd794bec0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_card_Psi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution : Nonempty X.Ψ := by
  have h := X.card_Psi
  have hpos : 0 < finrank ℚ E := Module.finrank_pos
  rw [← Fintype.card_pos_iff]
  omega
end ReciprocityTheory.ChartRestriction.G.FD.Data
