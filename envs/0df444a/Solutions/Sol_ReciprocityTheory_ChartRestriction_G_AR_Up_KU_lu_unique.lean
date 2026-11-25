-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.KU.lu_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:37:34.137866+00:00
-- url     : https://prove2.me/submissions/82971f31-9f22-47d5-a22e-b2dd9ffe9236

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_Lemmata_GeneralBFactVariant_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfB
import Theorems.Thm_Bl_general_b_fact_alt_form_goal1
import Theorems.Thm_Bl_general_b_fact_bis_form_goal1
import Theorems.Thm_Bl_general_b_fact_variant_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.KU
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU
theorem _root_.solution {n : ℕ} {N N' B B' : Matrix (Fin n) (Fin n) ℂ}
    (hN : N.BlockTriangular OrderDual.toDual) (hN' : N'.BlockTriangular OrderDual.toDual)
    (hd : ∀ i, N i i = 1) (hd' : ∀ i, N' i i = 1)
    (hB : B.BlockTriangular id) (hB' : B'.BlockTriangular id) (hBd : B.det ≠ 0)
    (h : N * B = N' * B') : N = N' := by
  exact Bl.general_b_fact_variant.goal1 hN hN' hd hd' hB hB' hBd h
end ReciprocityTheory.ChartRestriction.G.AR.Up.KU
