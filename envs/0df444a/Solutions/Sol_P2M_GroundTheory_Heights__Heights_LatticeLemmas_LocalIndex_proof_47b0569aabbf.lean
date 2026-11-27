-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticeLemmas_LocalIndex_proof_47b0569aabbf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:09:36.423672+00:00
-- url     : https://prove2.me/submissions/6131afcc-2320-47b6-886c-b3b19e3b22f2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocalGlobalIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocalLatticeIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PLocalIndex
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_localLattice_isLocalLattice_dcaf16a6988c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField IsDedekindDomain TensorProduct
open GroundTheory.Heights₂.Heights
universe u v
namespace GroundTheory.Heights₂.Heights.LatticeLemmas
namespace LocalIndex
theorem _root_.solution (h₁ : LocalGlobalIndex.Statement.{u, v})
    (h₂ : LocalLatticeIndex.Statement.{u, v}) : LocalIndex.Statement.{u, v} := by
  intro K _ _ V _ _ _ _ M₁ M₂ g hle hloc
  rw [h₁ K V M₁ M₂ hle]
  refine finprod_congr fun w ↦ ?_
  exact h₂ K V w _ _ (g w) (localLattice_isLocalLattice w M₁) (hloc w)
    (Submodule.span_mono (Set.image_mono hle))
end LocalIndex
end GroundTheory.Heights₂.Heights.LatticeLemmas
