-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.H1.RB.phi_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:50:12.18612+00:00
-- url     : https://prove2.me/submissions/e5ad0b88-cc6a-4e16-9e3e-9ed1a1ba21ff

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
theorem _root_.solution (a : ℝ) (x : E) : phi u k (a • x) = a * phi u k x := by
  simp only [phi, real_inner_smul_right, mul_div_assoc]
end ReciprocityTheory.ChartRestriction.G.H1.RB
