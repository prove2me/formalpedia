-- Prove2me | solution 1 for QnRdSkewW.hasDerivAt_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:14:27.926687+00:00
-- url     : https://prove2.me/submissions/1d23823b-86b2-40a7-8fcc-23ffecfcddb7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_HasDerivAtShift
import Theorems.Thm_QnRdSkewW_flow_zero
import Theorems.Thm_Formalism_REAL_hasDerivAt_matrix_exp_smul_at_zero


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
    {f F : Matrix (Fin n) (Fin n) ℂ → ℂ} {U : Set (Matrix (Fin n) (Fin n) ℂ)} {g : Matrix (Fin n) (Fin n) ℂ}
    (hU : IsOpen U) (hgU : g ∈ U) (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ h ∈ U, h ∈ G → f h = F h) (hg : g ∈ G) :
    HasDerivAt (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 := by
  have h0 := Formalism.REAL.hasDerivAt_matrix_exp_smul_at_zero X
  have hc : HasDerivAt (fun u : ℝ => g * NormedSpace.exp ((u : ℂ) • X)) (g * X) 0 := by
    have hL := (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ g)).hasFDerivAt
      (x := NormedSpace.exp (((0 : ℝ) : ℂ) • X))
    exact hL.comp_hasDerivAt (0 : ℝ) h0
  have hFd : HasFDerivAt F (fderiv ℝ F g) g :=
    ((hF.contDiffAt (hU.mem_nhds hgU)).differentiableAt (by simp)).hasFDerivAt
  have hcomp : HasDerivAt (fun u : ℝ => F (g * NormedSpace.exp ((u : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 :=
    hFd.comp_hasDerivAt_of_eq (0 : ℝ) hc (flow_zero g).symm
  have hU0 : U ∈ 𝓝 (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [flow_zero]; exact hU.mem_nhds hgU
  have hev : (fun u : ℝ => f (g * NormedSpace.exp ((u : ℂ) • X))) =ᶠ[𝓝 0]
      (fun u : ℝ => F (g * NormedSpace.exp ((u : ℂ) • X))) := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds hU0] with u hu
    exact hfF _ hu (hG g hg u)
  exact hcomp.congr_of_eventuallyEq hev
end QnRdSkewW
