-- Prove2me | solution 1 for PI.Dv.TIW.intR_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:24.442634+00:00
-- url     : https://prove2.me/submissions/a3eb0ea1-b2a6-42cd-8810-93e7b7517445

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
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → MonoidAlgebra K G) (hf : ∀ i ∈ s, IntR (f i)) :
    IntR (∑ i ∈ s, f i) := Subalgebra.sum_mem _ hf
end PI.Dv.TIW
