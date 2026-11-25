-- Prove2me | solution 1 for P2M_GlobalTheory_T_isSmoothFun_integral_mul_right__31ee4f82fd5d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:09:39.527775+00:00
-- url     : https://prove2.me/submissions/f57fe90c-26ac-47dc-86ee-aa4fcd925f87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothFunIntegralMulRight
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothFunIntegralMulRightStatement
import Theorems.Thm_GlobalTheory_isSmoothFun_integral_mul_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [IsFiniteMeasure ν] (K : Set G), IsCompact K → ν Kᶜ = 0 → ∀ κ : G → ℂ, h.IsSmoothFun κ → h.IsSmoothFun (fun z => ∫ y, κ (z * y) ∂ν) := by
  first | exact @GlobalTheory.isSmoothFun_integral_mul_right | exact GlobalTheory.isSmoothFun_integral_mul_right | (intros; apply GlobalTheory.isSmoothFun_integral_mul_right <;> assumption)
end _root_.GlobalTheory.T
