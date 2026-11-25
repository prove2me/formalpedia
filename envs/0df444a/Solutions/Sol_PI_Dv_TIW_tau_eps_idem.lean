-- Prove2me | solution 1 for PI.Dv.TIW.tau_eps_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:18:26.927795+00:00
-- url     : https://prove2.me/submissions/2174163f-93f1-4aa8-bf58-c3515044dd3e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MemOOfIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_AsAlgebraHomMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TraceMemOfIntR
import Theorems.Thm_PI_Dv_TIW_eps_idem


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
  {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W] (τ : Representation K G W)
namespace PI.Dv.TIW
theorem _root_.solution (P : Pair K G) : τ.asAlgebraHom (eps P) * τ.asAlgebraHom (eps P) = τ.asAlgebraHom (eps P) := by
  rw [← map_mul, eps_idem]
end PI.Dv.TIW
