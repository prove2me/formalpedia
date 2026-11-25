-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.orthProjVector_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:30:34.255841+00:00
-- url     : https://prove2.me/submissions/81c4a093-5b76-4fc2-b7a6-c18e49caa14e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SingleMemStandardLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsNeZeroMemNormSqLeGramDetDivRelIndex
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsSmallSaturatingVector

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
theorem _root_.solution {m : ℕ} (b : Fin k → Fin r → K) (c : Fin m → Fin r → K)
    (hc : ∀ j, c j ∈ hStd K r) (p : Fin m × Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :
    hwv b c p ∈ (hStd K r).toAddSubgroup.map (hpvHom b) := by
  refine ⟨integralBasis K p.2 • c p.1, ?_, rfl⟩
  show integralBasis K p.2 • c p.1 ∈ hStd K r
  rw [integralBasis_apply, algebraMap_smul]
  exact Submodule.smul_mem _ _ (hc p.1)
end ReciprocityTheory.ChartRestriction.G.T0
