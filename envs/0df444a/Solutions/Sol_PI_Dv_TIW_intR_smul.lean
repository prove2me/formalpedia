-- Prove2me | solution 1 for PI.Dv.TIW.intR_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:24.40773+00:00
-- url     : https://prove2.me/submissions/9bac71db-6428-4aee-9e30-3347d0486862

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
theorem _root_.solution (c : K) (hc : c ∈ Set.range (algebraMap (𝓞 K) K)) {z : MonoidAlgebra K G} (hz : IntR z) :
    IntR (c • z) := by
  obtain ⟨u, rfl⟩ := hc
  rw [algebraMap_smul]
  exact Subalgebra.smul_mem _ hz u
end PI.Dv.TIW
