-- Prove2me | solution 1 for PI.Dv.TIW.mem_O_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:29.860489+00:00
-- url     : https://prove2.me/submissions/fb5b3569-0b4e-4ead-9b7e-484afe59fb2f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TauCentralScalar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_GrpNorm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_DvTransferIdxOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MemOOfIsIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open PI.Dv NumberField
variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.TIW
theorem _root_.solution (x : K) (hx : IsIntegral ℤ x) : x ∈ Set.range (algebraMap (𝓞 K) K) :=
  ⟨IsIntegralClosure.mk' (𝓞 K) x hx, IsIntegralClosure.algebraMap_mk' _ _ _⟩
end PI.Dv.TIW
