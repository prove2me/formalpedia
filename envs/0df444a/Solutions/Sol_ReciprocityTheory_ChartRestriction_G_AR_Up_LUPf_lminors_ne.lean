-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf.lminors_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:31:56.798406+00:00
-- url     : https://prove2.me/submissions/dcaca3b8-5ebd-4dec-beed-5b1cd143cfbc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r)
variable {X x0}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
theorem _root_.solution {x : Frame X.Ψ r} (hΔ : DeltaF X x0 x ≠ 0) (τ : X.Ψ) (k : Fin (r + 1)) :
    lminor (Mx X x0 x τ) k ≠ 0 := by
  unfold DeltaF at hΔ
  rw [Finset.prod_ne_zero_iff] at hΔ
  have h1 := hΔ τ (Finset.mem_univ _)
  rw [Finset.prod_ne_zero_iff] at h1
  exact h1 k (Finset.mem_univ _)
end ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
