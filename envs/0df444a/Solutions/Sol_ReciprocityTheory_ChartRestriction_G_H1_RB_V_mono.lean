-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.RB.V_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:30.921698+00:00
-- url     : https://prove2.me/submissions/25ce78d9-4465-41ea-b22c-294c70f23323

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ReducedBasisStatement
import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_IndepOfFlag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.RB
open Finset InnerProductSpace Submodule Module ReciprocityTheory.ReducedBases.T2
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace ReciprocityTheory.ChartRestriction.G.H1.RB
theorem _root_.solution {d : ℕ} (u : Fin d → E) {m n : ℕ} (h : m ≤ n) : V u m ≤ V u n := by
  exact Submodule.span_mono (Set.image_mono fun l hl => show l.val < n from lt_of_lt_of_le (show l.val < m from hl) h)
end ReciprocityTheory.ChartRestriction.G.H1.RB
