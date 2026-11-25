-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.A_spanLt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:57:26.65673+00:00
-- url     : https://prove2.me/submissions/eb83a8ce-c530-4d5a-845c-e113791c68ae

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_AmatInvMul
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_Alin_apply
import Theorems.Thm_PI_NMeasInv_UnitaryGroupMassFormula_A_e

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
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
variable {n r : ℕ} (ε : Fin n → Bool)
variable {ε} {e f : Fin r → Fin n → ℂ}
variable (hG : Gram ε e f)
include hG
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution (s : Fin r → ℝ) (k : ℕ) {v : Fin n → ℂ} (hv : v ∈ spanLt e k) :
    Afun ε e f s v ∈ spanLt e k := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, hd, rfl⟩ := hx
    rw [A_e hG]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, hd, rfl⟩)
  | zero => rw [← Alin_apply, map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [← Alin_apply, map_add, Alin_apply, Alin_apply]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [← Alin_apply, map_smul, Alin_apply]
    exact Submodule.smul_mem _ _ hx
end PI.NMeasInv.UnitaryGroupMassFormula
