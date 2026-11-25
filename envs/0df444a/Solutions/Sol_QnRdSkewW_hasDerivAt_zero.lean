-- Prove2me | solution 1 for QnRdSkewW.hasDerivAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:04:05.061966+00:00
-- url     : https://prove2.me/submissions/9ef812f4-8a8c-4056-a16f-4158b3836d98

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_HasDerivAtShift
import Theorems.Thm_QnRdSkewW_hasDerivAt_local
import Theorems.Thm_QnRdSkewW_rdV_local

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology Set
open scoped ContDiff
noncomputable section
open QnRdSkewW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {X : Matrix (Fin n) (Fin n) ℂ}
namespace QnRdSkewW
theorem _root_.solution (hG : ∀ g ∈ G, ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ G)
    {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnSet G f) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G) :
    HasDerivAt (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) (RdV X f g) 0 := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  rw [rdV_local hG hU hgU hF hfF hg]
  exact hasDerivAt_local hG hU hgU hF hfF hg
end QnRdSkewW
