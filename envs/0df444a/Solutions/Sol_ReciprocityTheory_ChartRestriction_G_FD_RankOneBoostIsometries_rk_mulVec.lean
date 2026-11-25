-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.RankOneBoostIsometries.rk_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:00:27.875853+00:00
-- url     : https://prove2.me/submissions/9d9771ce-e389-4cf2-ae93-c678556a8794

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatrixMajorants
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RankOneBoostIsometries

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
open ReciprocityTheory.ChartRestriction.G.FD.RankOneBoostIsometries
open MajorantConjugateTransfer FlowMatrixMajorants
variable {r : ℕ} (X : Data E r) (τ : X.Ψ)
namespace ReciprocityTheory.ChartRestriction.G.FD.RankOneBoostIsometries
theorem _root_.solution (p w v : Fin r → ℂ) :
    Matrix.mulVec (rk X τ p w) v = hermC τ.1 X.Gm v w • p := by
  funext i
  simp only [Matrix.mulVec, dotProduct, rk, Matrix.of_apply, hermC, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  ring
end ReciprocityTheory.ChartRestriction.G.FD.RankOneBoostIsometries
