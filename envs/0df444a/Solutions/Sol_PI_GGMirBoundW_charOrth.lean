-- Prove2me | solution 1 for PI.GGMirBoundW.charOrth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:02:41.444454+00:00
-- url     : https://prove2.me/submissions/c0173725-9883-405c-a7c2-28ff23aaaf62

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicBound_CharSumOne
import Theorems.Thm_PI_GGMirBoundW_charSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.GGMirBoundW
open Finset Matrix
noncomputable section
open Classical
namespace PI.GGMirBoundW
theorem _root_.solution : CharOrth := by
  intro F _ _ m ψ₀ hψ r s
  have h : ∀ x : Fin m → F, ψ₀ (r ⬝ᵥ x) * ψ₀ (-(s ⬝ᵥ x)) = ψ₀ (∑ i, (r - s) i * x i) := by
    intro x
    rw [← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← sub_dotProduct]
    rfl
  simp_rw [h]
  rw [charSum ψ₀ hψ (r - s)]
  simp only [sub_eq_zero]
end PI.GGMirBoundW
