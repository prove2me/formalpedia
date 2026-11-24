-- Prove2me | solution 1 for PIW.AdelClassFin.dual_hat_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:12:45.179052+00:00
-- url     : https://prove2.me/submissions/308cd4f7-a56f-473a-a3ad-5b86f3a07519

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictLat
import Theorems.Thm_PIW_AdelClassFin_DictLat_hhat_iv
import Theorems.Thm_PIW_AdelClassFin_DictLat_Lf_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
namespace PIW.AdelClassFin
theorem _root_.solution : LHatInt := by
  intro I y hy z hz
  have h1 : ∀ l ∈ I.L, I.Lf ≤ dualR I (iv I l) := fun l hl => DictLat.Lf_le I _ fun l' hl' => by
    show hhat I (iv I l) (iv I l') ∈ IntAf I.F I.E
    rw [DictLat.hhat_iv]
    exact DictLat.inclE_int I ((I.L_dual l').mp hl' l hl)
  have h2 : I.Lf ≤ dualL I z := DictLat.Lf_le I _ fun l hl => h1 l hl hz
  exact h2 hy
end PIW.AdelClassFin
