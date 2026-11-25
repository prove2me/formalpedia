-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable.flow_eq_Zb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:34:03.038807+00:00
-- url     : https://prove2.me/submissions/e0a77a0e-dd76-4398-8bc4-c9fe01fa411d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SpanColsMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealEmbeddingCharacters
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainTranslate
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PeriodLatticeCountable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r) (u : Fin 2 → Fin r → E)
namespace ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable
theorem _root_.solution (s : X.Ψ → ℝ) (y : Frame X.Ψ r) :
    X.flow (u 0) (cR X s) y = X.Zb u (e00 X s) y := by
  funext τ
  simp only [Data.flow, Data.Zb]
  congr 1
  ext a j
  simp [Data.flowMat, Data.zmat, e00, Fin.sum_univ_two, Data.emb, cR]
  ring
end ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable
