-- Prove2me | solution 1 for P2M_Formalism_LFunctionChainParameters_ProjectiveLineModels_projective_lines_model__022d26f503e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:57:05.429341+00:00
-- url     : https://prove2.me/submissions/335818a8-1883-477c-b4c4-5d102dc14f58

import Definitions.Def_Formalism_SizeWindowBrackets_JointDPublishedSizes
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ProjectiveLines
import Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_power_hyp_to_ramified
import Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_projective_lines_power_hypothesis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.ProjectiveLineModels
open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare (hsSq)
open Formalism.LFunctionChainParameters.MatrixLatticeEstimates
namespace Formalism.LFunctionChainParameters.ProjectiveLineModels
theorem _root_.solution : ExistsModelLines := by
  intro K _ _ _ _ v
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  obtain ⟨h, s, u, hu0, H⟩ := projective_lines_power_hypothesis 19 K le_rfl v
  have e1 : ((19 : ℕ) : ℝ) ^ 2 = 361 := by norm_num
  have e2 : ((19 : ℕ) : ℝ) + 1 = 20 := by norm_num
  rw [e1, e2] at H
  set k : ℝ := Real.log (Fintype.card (Option (ZMod 19) × ZMod 19) : ℝ) with hk
  have hk0 : 0 ≤ k := Real.log_natCast_nonneg _
  set t : ℝ := |s - muMinDef (Pi.basisFun K (ZMod 19 × ZMod 19)) (fun _ => 1)
    (stdLat K (ZMod 19 × ZMod 19))| with ht
  have ht0 : 0 ≤ t := abs_nonneg _
  have hx : (20 : ℝ) ^ (-(1 : ℝ)) = 1 / 20 := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_one]; norm_num
  have H1 := H (t + 1 + 20 * k) (1 * (1 * (20 * ((t + 1 + 20 * k) / 20)) * 1 + 0 + u))
    (by have := le_abs_self (s - muMinDef (Pi.basisFun K (ZMod 19 × ZMod 19)) (fun _ => 1)
          (stdLat K (ZMod 19 × ZMod 19)))
        linarith)
    (by positivity) (by linarith)
  have H2 := power_hyp_to_ramified _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1
  rw [hx] at H2
  exact ⟨h, s, u, t + 1 + 20 * k, (t + 1 + 20 * k) / 20, k, 1, 1, 20 * ((t + 1 + 20 * k) / 20), 1, 0, u, H2,
    rfl, le_rfl, le_rfl, le_rfl, hu0, le_rfl, by linarith⟩
end Formalism.LFunctionChainParameters.ProjectiveLineModels
