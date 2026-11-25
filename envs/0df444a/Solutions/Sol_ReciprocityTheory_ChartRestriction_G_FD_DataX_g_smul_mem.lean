-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.DataX.g_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:31:24.845927+00:00
-- url     : https://prove2.me/submissions/ff70084d-0b22-48d9-bdbd-8082241ea316

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscrMulHermitianIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.DataX
variable {r : ℕ} (X : DataX E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.DataX
theorem _root_.solution {y : Fin r → E} (hy : y ∈ X.Λ) : (X.g : E) • y ∈ X.Λ := by
  rw [Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hy _
end ReciprocityTheory.ChartRestriction.G.FD.DataX
