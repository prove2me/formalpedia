-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_VectorBundleLocal_proof_2d8029ffb5b5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:04:53.76227+00:00
-- url     : https://prove2.me/submissions/294ae69d-58cd-4506-a4df-6ffca07597e7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_image_of_restrict_55b32d783d60
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_of_iso_15fe1f0a6e57
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsVectorBundle_of_iso_efcac834adba


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
namespace VectorBundleLocal
theorem _root_.solution : VectorBundleLocal.Statement := by
  intro X ι U hU E hE x
  have hx : x ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  have hR : IsVectorBundle (E.restrict (U i).ι) :=
    (hE i).of_iso ((Scheme.Modules.restrictFunctorIsoPullback (U i).ι).app E).symm
  obtain ⟨W, hWa, hyW, n, s, hs⟩ := hR ⟨x, hxi⟩
  exact ⟨(U i).ι ''ᵁ W, hWa.image_of_isOpenImmersion (U i).ι, ⟨⟨x, hxi⟩, hyW, rfl⟩, n, _,
    hs.image_of_restrict (U i).ι E⟩
end VectorBundleLocal
end GroundTheory.Heights₂.Heights.Model
