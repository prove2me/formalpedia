-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.mem_standardLattice_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:56:48.675806+00:00
-- url     : https://prove2.me/submissions/ce2e961e-d69b-4255-a139-c2715932628e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OrthogonalProjectorMulVecConjugate
import Definitions.Def_ReciprocityTheory_SemistableReduction_DegAddHolds
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SingleMemStandardLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Matrix NumberField
open scoped ComplexOrder
variable {K : Type} [Field K] [NumberField K] {r k : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {x : Fin r → K} :
    x ∈ hStd K r ↔ ∀ i, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = x i := by
  simp [hStd, Submodule.mem_pi, Submodule.mem_one]
end ReciprocityTheory.ChartRestriction.G.T0
