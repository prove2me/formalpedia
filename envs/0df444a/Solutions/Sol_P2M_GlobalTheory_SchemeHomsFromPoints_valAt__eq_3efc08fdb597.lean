-- Prove2me | solution 1 for P2M_GlobalTheory_SchemeHomsFromPoints_valAt__eq_3efc08fdb597
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:31:16.578621+00:00
-- url     : https://prove2.me/submissions/7f34c1a4-5837-452a-9c54-84183607d5f6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DenseClosedPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp valAt valAt')
open GlobalTheory GlobalTheory.SchemeHomsFromPoints
namespace GlobalTheory.SchemeHomsFromPoints
theorem _root_.solution {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (W : X.Opens) (e : ⊤ ≤ x ⁻¹ᵁ W) (h : Γ(X, W)) :
    valAt' x W h = (ev x W e).hom h := by
  rw [valAt', dif_pos e]
  rfl
end GlobalTheory.SchemeHomsFromPoints
