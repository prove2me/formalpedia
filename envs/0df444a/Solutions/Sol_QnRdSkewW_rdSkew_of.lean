-- Prove2me | solution 1 for QnRdSkewW.rdSkew_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:04:06.023254+00:00
-- url     : https://prove2.me/submissions/cb2e8199-cefa-4817-bf22-7ea9e69403d2

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open scoped ContDiff
noncomputable section
open QnRdSkewW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace QnRdSkewW
theorem _root_.solution (h1 : StepGroup) (h2 : StepAnalytic) : RdSkew := by
  intro k r i μ hμ X f₁ f₂ hX hs₁ hs₂ hc₁ hc₂
  obtain ⟨hcl, hfl, hexp⟩ := h1 k r i X hX
  exact h2 (2 * r + k + 1) (Glev k r i) μ X f₁ f₂ hcl hfl hμ.conc
    (fun t => hμ.right _ (hexp t)) hμ.finite_compact
    (fun g₀ hg₀ => hs₁ g₀ ⟨hg₀, Set.mem_univ _⟩) (fun g₀ hg₀ => hs₂ g₀ ⟨hg₀, Set.mem_univ _⟩) hc₁ hc₂
end QnRdSkewW
