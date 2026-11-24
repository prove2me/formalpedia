-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_cycR_eq_finsum_b745b6d310f8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:20.702364+00:00
-- url     : https://prove2.me/submissions/2c40129b-7ee0-4405-b28b-02115a3d0dd5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Inter.DiagRAux
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.DiagRAux
theorem _root_.solution (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) {n : ℕ}
    (L : Fin n → HermLine ι) (s : MRing ι) :
    cycR I P L s = ∑ᶠ W, (divCycle P s W : ℝ) * cycTerm I L W := by
  classical
  unfold cycR cycTerm
  rw [finsum_mem_def]
  refine finsum_congr fun W => ?_
  by_cases hW : W ∈ divSupp P s
  · simp [divCycle, Finsupp.ofSupportFinite_coe, hW]
  · simp [divCycle, Finsupp.ofSupportFinite_coe, hW]
end GroundTheory.Heights₂.Heights.Inter.DiagRAux
