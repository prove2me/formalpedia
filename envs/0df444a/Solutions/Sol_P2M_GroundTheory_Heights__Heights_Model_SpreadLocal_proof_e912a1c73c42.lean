-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_SpreadLocal_proof_e912a1c73c42
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:04:38.064999+00:00
-- url     : https://prove2.me/submissions/1995bc17-4e90-4d76-bb64-d762b35f217f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsBasisIsoFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSpreadLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_isVectorBundle_freeModule_ea3cf8102b36
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_isPreimmersion_baseChangeMap_52e3bc354d38
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_restrictImage_c6b16aec65a8


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.Model
namespace SpreadLocal
theorem _root_.solution (h₁ : FreeSheafBasis.Statement.{0}) (h₂ : BasisIsoFree.Statement.{0}) :
    SpreadLocal.Statement := by
  intro X f p E hE x
  obtain ⟨U, -, hxU, n, s, hs⟩ := hE x
  have := isPreimmersion_baseChangeMap f p
  obtain ⟨W, hWo, hW⟩ := (baseChangeMap f (ZLoc p)).isEmbedding.isInducing.isOpen_iff.mp U.2
  let W' : X.Opens := ⟨W, hWo⟩
  have hWU : baseChangeMap f (ZLoc p) ⁻¹ᵁ W' = U := Opens.ext hW
  refine ⟨W', hWU ▸ hxU, ?_⟩
  let V := baseChangeMap f (ZLoc p) ⁻¹ᵁ W'
  have hle : V.ι ''ᵁ ⊤ ≤ U := by simp [V, hWU]
  obtain ⟨eF⟩ := h₂ _ (E.restrict V.ι) n _ ((hs.restrict hle).restrictImage V.ι)
  let φ := (baseChangeMap f (ZLoc p) ∣_ W').toRingCatSheafHom
  have : (SheafOfModules.pushforward φ).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction (baseChangeMap f (ZLoc p) ∣_ W')).isRightAdjoint
  exact ⟨_, isVectorBundle_freeModule h₁ _ n,
    ⟨SheafOfModules.pullbackObjFreeIso φ (ULift.{0} (Fin n)) ≪≫ eF.symm ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback V.ι).app E⟩⟩
end SpreadLocal
end GroundTheory.Heights₂.Heights.Model
