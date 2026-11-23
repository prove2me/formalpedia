-- Prove2me | solution 1 for UnipMove.GraphH.en_eq_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:08.447236+00:00
-- url     : https://prove2.me/submissions/0f65da5f-4064-4524-8738-948722d54a0c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_KatoClassHeckeEulerFactorRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt

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
theorem _root_.solution {n : ℕ} (v : Fin n → ℂ) : en v = Real.sqrt (nsq v) := by
  unfold en nsq
  first
    | (rw [EuclideanSpace.norm_eq]; rfl)
    | (rw [EuclideanSpace.norm_eq]; simp)
    | simp [EuclideanSpace.norm_eq]
end UnipMove.GraphH
