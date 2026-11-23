-- Prove2me | solution 1 for PI.Dv.TIW.intR_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:24.243798+00:00
-- url     : https://prove2.me/submissions/42bd14f9-938d-4878-b00d-ce19d3f1322d

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
theorem _root_.solution {z z' : MonoidAlgebra K G} (hz : IntR z) (hz' : IntR z') : IntR (z * z') :=
  Subalgebra.mul_mem _ hz hz'
end PI.Dv.TIW
