-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.nb_uniq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:32:38.108017+00:00
-- url     : https://prove2.me/submissions/f518d70e-b604-49b3-86b8-6588ce2a280a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfD
import Definitions.Def_Lemmata_GeneralBFactTer_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Theorems.Thm_Bl_DetMonotoneStarMulSelf_goal1
import Theorems.Thm_Bl_PosDefOfRealQuadratic_goal1
import Theorems.Thm_Bl_general_b_fact_alt_form_goal1
import Theorems.Thm_Bl_general_b_fact_bis_form_goal1
import Theorems.Thm_Bl_general_b_fact_ter_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Set
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf
theorem _root_.solution {N N' B B' : Matrix (Fin r) (Fin r) ℂ} (hN : ∀ a c : Fin r, a < c → N a c = 0)
    (hN1 : ∀ a, N a a = 1) (hN' : ∀ a c : Fin r, a < c → N' a c = 0) (hN'1 : ∀ a, N' a a = 1)
    (hB : ∀ a c : Fin r, c < a → B a c = 0) (hB' : ∀ a c : Fin r, c < a → B' a c = 0) (hBd : B.det ≠ 0)
    (h : N * B = N' * B') : N = N' := by
  exact Bl.general_b_fact_ter.goal1 hN hN1 hN' hN'1 hB hB' hBd h
end ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf
