-- Prove2me | solution 1 for PI.AddIntG.Wk.Gv_algHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:01:46.956297+00:00
-- url     : https://prove2.me/submissions/d04a9b78-a8e8-4916-a23c-84290ee514d4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_ThirdRootSubVarZeroNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DXEqDerivative
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DvCoeffMulEqZeroOfLtOrder
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_VarZeroSubVarOneNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.AddIntG PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]
namespace PI.AddIntG.Wk
theorem _root_.solution {R R' : Type*} [CommRing R] [Algebra ℂ_[p] R] [CommRing R'] [Algebra ℂ_[p] R']
    (φ : R →ₐ[ℂ_[p]] R') (W : WeierstrassCurve ℂ_[p]) (u v : R) :
    φ (Gv W u v) = Gv W (φ u) (φ v) := by
  simp [Gv, map_add, map_mul, map_sub, map_pow, AlgHom.commutes, map_ofNat]
end PI.AddIntG.Wk
