-- Prove2me | solution 1 for P2M_GlobalTheory_SobolevRep_continuous_prodExp__16071771a47c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:34:08.1485+00:00
-- url     : https://prove2.me/submissions/51e221f5-ca13-461b-8c41-be00af6032c7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivExpGLineEqRightDerivPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValueAtZeroEqSumIntegralKernelIteratedDerivStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSobolevRepresentationProdExp
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_continuous_revProdExp
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_revProdExp_inv


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
open GlobalTheory
open GlobalTheory.SobolevRep
variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
namespace GlobalTheory.SobolevRep
theorem _root_.solution {d : ℕ} (X : Fin d → 𝔤) : Continuous (h.prodExp X) := by
  have : h.prodExp X = fun t => (h.revProdExp X (-t))⁻¹ := by
    funext t; rw [h.revProdExp_inv, neg_neg]
  rw [this]
  exact ((h.continuous_revProdExp X).comp continuous_neg).inv
end GlobalTheory.SobolevRep
