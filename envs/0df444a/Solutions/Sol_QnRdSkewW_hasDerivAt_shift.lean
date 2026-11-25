-- Prove2me | solution 1 for QnRdSkewW.hasDerivAt_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:23:09.923823+00:00
-- url     : https://prove2.me/submissions/e5106742-cb0f-4f75-9267-b646a6600123

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_HasDerivAtShift
import Theorems.Thm_QnRdSkewW_hasDerivAt_zero

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
    {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnSet G f) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (g * NormedSpace.exp ((s : ℂ) • X)))
      (RdV X f (g * NormedSpace.exp ((t : ℂ) • X))) t := by
  have hh : g * NormedSpace.exp ((t : ℂ) • X) ∈ G := hG g hg t
  have h0 := hasDerivAt_zero hG hf hh
  have h0' : HasDerivAt (fun u : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((u : ℂ) • X)))
      (RdV X f (g * NormedSpace.exp ((t : ℂ) • X))) (t - t) := by
    rw [sub_self]; exact h0
  refine (h0'.comp_sub_const t t).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  show f (g * NormedSpace.exp ((s : ℂ) • X)) =
    f (g * NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp (((s - t : ℝ) : ℂ) • X))
  have hcomm : Commute ((t : ℂ) • X) (((s - t : ℝ) : ℂ) • X) :=
    ((Commute.refl X).smul_left _).smul_right _
  have e : (t : ℂ) • X + ((s - t : ℝ) : ℂ) • X = (s : ℂ) • X := by
    rw [← add_smul]; congr 1; push_cast; ring
  rw [mul_assoc, ← Matrix.exp_add_of_commute _ _ hcomm, e]
end QnRdSkewW
