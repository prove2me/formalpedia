-- Prove2me | solution 1 for PI.IsoDualPair.UnitaryGroupMassFormula.isoDualPair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:09:47.298558+00:00
-- url     : https://prove2.me/submissions/8f23f89a-84fe-40fb-84a8-ee526a7e4c5a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDualPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDualPair_SymmetricMeasureL2NormEqResolutionL2
import Theorems.Thm_PI_IsoDualPair_UnitaryGroupMassFormula_cs
import Theorems.Thm_PI_IsoDualPair_UnitaryGroupMassFormula_conj_mem
import Theorems.Thm_PI_IsoDualPair_UnitaryGroupMassFormula_prC_conj
import Theorems.Thm_PI_IsoDualPair_UnitaryGroupMassFormula_l2_conj
import Theorems.Thm_PI_IsoDualPair_UnitaryGroupMassFormula_pairL_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.IsoDualPair PI.IsoDualPair.UnitaryGroupMassFormula
open PI.IsoDualPair
variable {Lt : Type} [Fintype Lt] {N : ℕ} {nu : Lt → YoungDiagram}
namespace PI.IsoDualPair.UnitaryGroupMassFormula
theorem _root_.solution : IsoDualPair := by
  intro Lt _ _ N nu
  refine ⟨fun φ hφ => ⟨fun ψ _ => cs φ ψ, ⟨_, conj_mem hφ, l2_conj φ, prC_conj φ⟩⟩, fun Λ => ?_⟩
  obtain ⟨φ, hφ⟩ := pairL_surjective Λ
  refine ⟨φ, φ.2, fun ψ => ?_⟩
  rw [← hφ]
  rfl
end PI.IsoDualPair.UnitaryGroupMassFormula
