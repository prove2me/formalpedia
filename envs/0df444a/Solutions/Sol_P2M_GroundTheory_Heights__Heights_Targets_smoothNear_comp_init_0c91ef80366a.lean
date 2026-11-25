-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_smoothNear_comp_init_0c91ef80366a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:22:01.775802+00:00
-- url     : https://prove2.me/submissions/b50928d5-1f92-4b27-89a4-8ef5acbb880f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLelongPolyLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StVarIntGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLocalMultComap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLelongWeightLimit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PLelongPolyLimit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_init_mem_zeroSet_874e3cb9df4e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_single_50b347f8c25b


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial Filter Topology Matrix
open scoped ContDiff
open GroundTheory.Heights₂.Heights (varInt SmoothNear localMult linEval linForm linForm_single)
open GroundTheory.Heights₂.Heights.ComplexSets (zeroSet)
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (p : MvPolynomial (Fin n) ℂ)
    {g : (Fin n → ℂ) → ℝ} (hg : SmoothNear (zeroSet J) g) :
    SmoothNear (zeroSet (graphIdeal J p)) (fun x => g (Fin.init x)) := by
  obtain ⟨U, hU, hJU, hgU⟩ := hg
  have hinit : ContDiff ℝ ∞ (fun x : Fin (n + 1) → ℂ => Fin.init x) :=
    contDiff_pi.2 fun i => contDiff_apply ℝ ℂ (Fin.castSucc i)
  exact ⟨(fun x => Fin.init x) ⁻¹' U, hU.preimage hinit.continuous,
    fun x hx => hJU (init_mem_zeroSet p hx), hgU.comp hinit.contDiffOn fun _ hx => hx⟩
end GroundTheory.Heights₂.Heights.Targets
