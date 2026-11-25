-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_isUnit_intCast_of_le_invOpen_ebaf15bce7bb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:40:45.019401+00:00
-- url     : https://prove2.me/submissions/8d38ed1e-ffad-440e-976e-6b8684c56663

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGenericSections
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_invOpen_eq_basicOpen_c5fee204da3b

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
open CategoryTheory Limits AlgebraicGeometry Opposite
noncomputable section
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {X : Scheme.{0}} (f : X ⟶ SpecZ) (k : ℤ) {V : X.Opens}
    (hV : V ≤ invOpen f k) : IsUnit (k : Γ(X, V)) := by
  rw [invOpen_eq_basicOpen] at hV
  have hu := X.toRingedSpace.isUnit_res_basicOpen ((k : Γ(X, f ⁻¹ᵁ ⊤)))
  rw [map_intCast] at hu
  have := hu.map (X.presheaf.map (homOfLE hV).op).hom
  convert this using 1
  exact (map_intCast (X.presheaf.map (homOfLE hV).op).hom k).symm
end GroundTheory.Heights₂.Heights.Model
