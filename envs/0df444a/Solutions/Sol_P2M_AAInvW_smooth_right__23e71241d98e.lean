-- Prove2me | solution 1 for P2M_AAInvW_smooth_right__23e71241d98e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:55:14.674405+00:00
-- url     : https://prove2.me/submissions/3aac543b-a7d2-43ed-a6d6-603b7e90cdab

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_AnaHpartUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SmoothLinear
import Theorems.Thm_AAInvW_ana_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace AAInvW
theorem _root_.solution : SmoothRight := by
  unfold SmoothRight
  intro n H E _ _ f s hH hs hf
  unfold SmoothOnH at *
  have hL : ContDiff ℝ ∞ (fun x : Matrix (Fin n) (Fin n) ℂ => x * s) := by
    have h := (LinearMap.mulRight ℝ s).toContinuousLinearMap.contDiff (n := ∞)
    convert h using 1
    funext x
    first
    | rfl
    | simp
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf (g₀ * s) (ana_mul hg₀ hs)
  refine ⟨(fun x => x * s) ⁻¹' U, fun x => F (x * s), hU.preimage hL.continuous, hgU, ?_, ?_⟩
  · exact hF.comp hL.contDiffOn (fun x hx => hx)
  · intro g hg hgH
    exact hfF (g * s) hg (ana_mul hgH hs)
end AAInvW
