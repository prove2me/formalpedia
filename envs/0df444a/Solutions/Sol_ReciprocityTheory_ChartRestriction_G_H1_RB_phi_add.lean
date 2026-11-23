-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.RB.phi_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:30.934802+00:00
-- url     : https://prove2.me/submissions/edabab91-8c8f-497e-b8b1-10a205f3fe2e

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
variable {d : ℕ} (u : Fin d → E) (k : Fin d)
namespace ReciprocityTheory.ChartRestriction.G.H1.RB
theorem _root_.solution (x y : E) : phi u k (x + y) = phi u k x + phi u k y := by
  simp only [phi, inner_add_right, add_div]
end ReciprocityTheory.ChartRestriction.G.H1.RB
