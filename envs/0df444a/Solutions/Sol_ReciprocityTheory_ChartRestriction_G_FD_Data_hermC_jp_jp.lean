-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.hermC_jp_jp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:56:56.335189+00:00
-- url     : https://prove2.me/submissions/89cd5d93-316d-4f29-a9df-aadd00ec1032

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_jp_jp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hermC_jp_left

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
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.jp x τ u) (X.jp x τ v) = hermC τ.1 X.Gm u v := by
  rw [X.hermC_jp_left hx τ u (X.jp x τ v), X.jp_jp hx]
end ReciprocityTheory.ChartRestriction.G.FD.Data
