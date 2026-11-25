-- Prove2me | solution 1 for PositivityTheory.CW.NoncommutativeSwapSum.sumS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:25:54.8975+00:00
-- url     : https://prove2.me/submissions/e2b695c0-c995-4628-9901-8aa6bd880aff

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_GrowthPolynomialOperator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.NoncommutativeSwapSum
namespace PositivityTheory.CW.NoncommutativeSwapSum
theorem _root_.solution {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (κ : ℂ)
    (hS : ∀ w, ∑ p ∈ nc ε, E p.1 p.2 (E p.2 p.1 w) = κ • w - casimirK ε E w) :
    ∑ p ∈ nc ε, E p.1 p.2 * E p.2 p.1 = κ • (1 : Module.End ℂ V) - casimirK ε E := by
  ext w
  rw [LinearMap.sum_apply]
  simpa using hS w
end PositivityTheory.CW.NoncommutativeSwapSum
