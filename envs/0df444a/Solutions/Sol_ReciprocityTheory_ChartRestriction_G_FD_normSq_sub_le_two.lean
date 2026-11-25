-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.normSq_sub_le_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:00:37.745805+00:00
-- url     : https://prove2.me/submissions/5250dc17-ef53-40c6-834f-c6b4602e7fe1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentOnHyperbolicComplement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnipotentSubOneMajorantBound

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
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution (a b : ℂ) :
    Complex.normSq (a - b) ≤ 2 * Complex.normSq a + 2 * Complex.normSq b := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  nlinarith [sq_nonneg (a.re + b.re), sq_nonneg (a.im + b.im)]
end ReciprocityTheory.ChartRestriction.G.FD
