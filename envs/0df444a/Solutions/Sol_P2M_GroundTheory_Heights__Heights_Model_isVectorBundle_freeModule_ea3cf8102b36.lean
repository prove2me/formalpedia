-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_isVectorBundle_freeModule_ea3cf8102b36
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:05:41.899673+00:00
-- url     : https://prove2.me/submissions/c68857a6-256a-4d78-a4f6-dbc3f53572a6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsBasisIsoFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSpreadLocal

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
theorem _root_.solution (h : FreeSheafBasis.Statement.{u}) (Y : Scheme.{u}) (n : ℕ) :
    IsVectorBundle (freeModule Y n) := by
  intro y
  obtain ⟨V, hV, hyV, -⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (show y ∈ (⊤ : Y.Opens) from trivial)
  exact ⟨V, hV, hyV, n, _, (h Y n).restrict le_top⟩
end GroundTheory.Heights₂.Heights.Model
