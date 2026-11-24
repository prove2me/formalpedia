-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_VectorBundleRestrict_proof_7423c8d31f2c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:48.663522+00:00
-- url     : https://prove2.me/submissions/b5e89639-537d-4914-956a-c00a0032f0b2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_restrictImage_c6b16aec65a8
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
namespace VectorBundleRestrict
theorem _root_.solution : VectorBundleRestrict.Statement := by
  intro X Y f _ E hE
  refine IsVectorBundle.of_iso ((Scheme.Modules.restrictFunctorIsoPullback f).app E) ?_
  intro x
  obtain ⟨U, -, hxU, n, s, hs⟩ := hE (f.base x)
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ f ⁻¹ᵁ U from hxU)
  have hle : f ''ᵁ V ≤ U := (Scheme.Hom.image_mono f hVU).trans (f.image_preimage_le U)
  exact ⟨V, hV, hxV, n, _, (hs.restrict hle).restrictImage f⟩
end VectorBundleRestrict
end GroundTheory.Heights₂.Heights.Model
