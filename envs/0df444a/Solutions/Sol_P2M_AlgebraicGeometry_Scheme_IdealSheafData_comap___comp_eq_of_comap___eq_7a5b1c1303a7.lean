-- Prove2me | solution 1 for P2M_AlgebraicGeometry_Scheme_IdealSheafData_comap___comp_eq_of_comap___eq_7a5b1c1303a7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:54:03.184343+00:00
-- url     : https://prove2.me/submissions/8439f6aa-e328-45fa-9459-7c587fa9824e

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
theorem _root_.solution (f : X ⟶ Y) (V : Y.Opens) (U : X.Opens)
    (hle : U ≤ f ⁻¹ᵁ V) (I J : Y.IdealSheafData)
    (h : I.comap V.ι = J.comap V.ι) : I.comap (U.ι ≫ f) = J.comap (U.ι ≫ f) := by
  have hfac : X.homOfLE hle ≫ ((f ∣_ V) ≫ V.ι) = U.ι ≫ f := by
    rw [AlgebraicGeometry.morphismRestrict_ι, ← CategoryTheory.Category.assoc,
      AlgebraicGeometry.Scheme.homOfLE_ι]
  have e : ∀ K : Y.IdealSheafData,
      ((K.comap V.ι).comap (f ∣_ V)).comap (X.homOfLE hle) = K.comap (U.ι ≫ f) := by
    intro K
    rw [← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
      ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, CategoryTheory.Category.assoc, hfac]
  rw [← e I, ← e J, h]
end AlgebraicGeometry.Scheme.IdealSheafData
