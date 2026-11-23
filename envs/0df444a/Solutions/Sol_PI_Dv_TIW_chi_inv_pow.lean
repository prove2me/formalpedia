-- Prove2me | solution 1 for PI.Dv.TIW.chi_inv_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:22.938804+00:00
-- url     : https://prove2.me/submissions/c2e1303c-f309-4a4b-bb86-d8fcb19104e0

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
theorem _root_.solution (P : Pair K G) (h : P.H) : ((((P.chi h)⁻¹ : Kˣ) : K)) ^ (Nat.card P.H) = 1 := by
  classical
  rw [← Units.val_pow_eq_pow_val, inv_pow, ← map_pow, Nat.card_eq_fintype_card, pow_card_eq_one, map_one,
    inv_one, Units.val_one]
end PI.Dv.TIW
