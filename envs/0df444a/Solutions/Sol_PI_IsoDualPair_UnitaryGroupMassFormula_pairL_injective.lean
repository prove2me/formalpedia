-- Prove2me | solution 1 for PI.IsoDualPair.UnitaryGroupMassFormula.pairL_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:56:49.550786+00:00
-- url     : https://prove2.me/submissions/035a5b84-f63f-40e3-9222-6323ac0d3ce4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDualPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDualPair_SymmetricMeasureL2NormEqResolutionL2
import Theorems.Thm_PI_IsoDualPair_UnitaryGroupMassFormula_conj_mem
import Theorems.Thm_PI_IsoDualPair_UnitaryGroupMassFormula_prC_conj
import Theorems.Thm_PI_IsoDualPair_UnitaryGroupMassFormula_eq_zero_of_l2_eq_zero
import Theorems.Thm_PI_IsoDualPair_UnitaryGroupMassFormula_pairL_apply

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
theorem _root_.solution : Function.Injective (pairL (N := N) (nu := nu)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro φ hφ
  have h1 := LinearMap.congr_fun hφ ⟨_, conj_mem φ.2⟩
  rw [pairL_apply, LinearMap.zero_apply] at h1
  have h2 : prC (φ : LaC N nu) (fun J => conj ((φ : LaC N nu) J)) = 0 := h1
  rw [prC_conj] at h2
  have h3 : l2 (φ : LaC N nu) = 0 := by exact_mod_cast h2
  exact Subtype.ext (eq_zero_of_l2_eq_zero _ h3)
end PI.IsoDualPair.UnitaryGroupMassFormula
