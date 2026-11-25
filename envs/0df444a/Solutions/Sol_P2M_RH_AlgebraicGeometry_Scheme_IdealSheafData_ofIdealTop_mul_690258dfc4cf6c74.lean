-- Prove2me | solution 1 for P2M_RH_AlgebraicGeometry_Scheme_IdealSheafData_ofIdealTop_mul_690258dfc4cf6c74
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:51:23.797381+00:00
-- url     : https://prove2.me/submissions/f828e922-4b94-433c-bc34-181b91a9402f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}}
namespace AlgebraicGeometry.Scheme.IdealSheafData
theorem _root_.solution [IsAffine X] (I J : Ideal Γ(X, ⊤)) :
    ofIdealTop (I * J) = ofIdealTop I * ofIdealTop J := by
  ext U : 2
  exact Ideal.map_mul _ _ _
end AlgebraicGeometry.Scheme.IdealSheafData
