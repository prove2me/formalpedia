-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.measure_subFacts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:53:35.307899+00:00
-- url     : https://prove2.me/submissions/1e3a991f-8125-462d-b0a9-9fc7d9724b3f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_inN_conj
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_uMat_mul_inv
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_uMat_inUJ
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_isClosed_Ninf
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_isClosed_Hset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
variable (I : Formalism.MainNotions.S.AutInst)
variable {r : ℕ}
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution : SubFacts := by
  intro I r e f z
  refine ⟨NSub I e z, HSub I (frameSet I e f z), rfl, rfl, isClosed_Ninf I e z, isClosed_Hset I _, ?_⟩
  intro h hh x hx
  have hh' : h ∈ Hset I (frameSet I e f z) := hh
  have hx' : x ∈ Ninf I e z := hx
  show ∀ v, InN _ _ _ (Formalism.MainNotions.S.uMat ((h * x * h⁻¹) v))
  intro v
  show InN _ _ _ (Formalism.MainNotions.S.uMat (h v * x v * (h v)⁻¹))
  rw [uMat_mul, uMat_mul]
  exact inN_conj (uMat_inUJ _) (uMat_mul_inv _) (uMat_inv_mul _)
    (fun a => hh' v _ (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_range_self a))))
    (hh' v _ (Set.mem_union_right _ rfl)) (hx' v)
end PI.ScMuExists.UnitaryGroupMassFormula
