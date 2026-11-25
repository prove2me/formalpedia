-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_map_piece_65c72f83e5aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:37:45.7339+00:00
-- url     : https://prove2.me/submissions/34f9461e-6478-4497-8bcb-ac9d44c3fb24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_image_exps_fbf5ec376f1c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
variable {S : Type u} [CommRing S] {N : ℕ}
attribute [local instance] algP
namespace GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
theorem _root_.solution (c : ℤ) : ((polyGraded S N).piece c).map (polyToLaurent S N) =
    Finsupp.supported S S (laurentExps N c ∅) := by
  change (weightedHomogeneousSubmodule S (fun _ => (1 : ℤ)) c).map _ = _
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported, AddMonoidAlgebra.supported_eq_map,
    ← Submodule.map_comp]
  have : (polyToLaurent S N).comp (AddMonoidAlgebra.coeffLinearEquiv S).symm.toLinearMap =
      Finsupp.lmapDomain S S (expToInt N) := LinearMap.ext fun _ => rfl
  rw [this, Finsupp.lmapDomain_supported, image_exps]
end GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
