-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable.Zb_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:00:07.810631+00:00
-- url     : https://prove2.me/submissions/a4a96e0b-c905-4414-a5fb-d51e953bff5d

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
theorem _root_.solution (y : Frame X.Ψ r) : Continuous fun b : X.Ψ → Fin 2 → Fin 2 → ℂ => X.Zb u b y := by
  refine continuous_pi fun τ => ?_
  simp only [Data.Zb, Data.zmat]
  refine continuous_pi fun a => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop
end ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable
