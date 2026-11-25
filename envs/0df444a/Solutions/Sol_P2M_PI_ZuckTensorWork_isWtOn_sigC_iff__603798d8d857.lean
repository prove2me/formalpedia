-- Prove2me | solution 1 for P2M_PI_ZuckTensorWork_isWtOn_sigC_iff__603798d8d857
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:56:55.751694+00:00
-- url     : https://prove2.me/submissions/b7e1adb1-b5d8-45ff-9ddd-250f561e6a2b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_DualChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZuckermanTensor_ConjRep
import Theorems.Thm_PI_ZuckTensorWork_isWtOn_sigC_iff
import Theorems.Thm_PI_ZuckTensorWork_dualWeight_dualWeight


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
open PI PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ} {ε : Fin n → Bool}
namespace PI.ZuckTensorWork
theorem _root_.solution (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (μ : Fin n → ℝ) (x : Cj H) :
    IsWtOn (Kset (revE ε)) (sigC σ) μ x ↔ IsWtOn (Kset ε) σ (revP μ) (Cj.un x) := by
  rw [isWtOn_sigC_iff (ε := ε) σ (revP μ) (Cj.un x), dualWeight_dualWeight]
  exact Iff.rfl
end PI.ZuckTensorWork
