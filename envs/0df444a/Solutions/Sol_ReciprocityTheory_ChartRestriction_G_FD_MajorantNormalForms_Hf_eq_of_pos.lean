-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms.Hf_eq_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:56:42.878543+00:00
-- url     : https://prove2.me/submissions/daf15914-1968-4688-9102-e9837e384f1a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentCoefficientShift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajorantNormalForms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms
open Matrix NumberField Complex
open scoped ComplexConjugate ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms
theorem _root_.solution (x : Frame X.Ψ r) (τ : X.Ψ) {u : Fin r → ℂ} (hu : X.ppos x τ u = u)
    (w : Fin r → ℂ) : X.Hf x τ u w = hermC τ.1 X.Gm u w := by
  unfold Data.Hf
  rw [hu, two_smul, add_sub_cancel_right]
end ReciprocityTheory.ChartRestriction.G.FD.MajorantNormalForms
