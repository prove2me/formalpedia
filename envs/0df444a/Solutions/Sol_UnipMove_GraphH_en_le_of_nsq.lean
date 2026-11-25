-- Prove2me | solution 1 for UnipMove.GraphH.en_le_of_nsq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:00:10.369177+00:00
-- url     : https://prove2.me/submissions/67711984-30ad-4e6b-ba37-e6badabbc958

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Theorems.Thm_UnipMove_GraphH_en_eq_sqrt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnipMove UnipMove.GraphH
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds NumberField Complex
open scoped ComplexConjugate Matrix
noncomputable section
namespace UnipMove.GraphH
theorem _root_.solution {m n : ℕ} (u : Fin m → ℂ) (v : Fin n → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (h : nsq u ≤ c ^ 2 * nsq v) : en u ≤ c * en v := by
  rw [en_eq_sqrt, en_eq_sqrt]
  calc Real.sqrt (nsq u) ≤ Real.sqrt (c ^ 2 * nsq v) := Real.sqrt_le_sqrt h
    _ = c * Real.sqrt (nsq v) := by rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
end UnipMove.GraphH
