-- Prove2me | solution 1 for P2M_RH_AlgebraicGeometry_Scheme_IdealSheafData_comap_ofIdealTop_bf5846d67e16db07
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:03.668676+00:00
-- url     : https://prove2.me/submissions/7af033ac-77da-44bc-90a1-f7a3fcb6ed72

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_ofIdealTop_ideal_top
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ideal_top_eq_map_appTop

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
theorem _root_.solution [IsAffine X] [IsAffine Y] (J : Ideal Γ(Y, ⊤)) (f : X ⟶ Y) :
    (ofIdealTop J).comap f = ofIdealTop (J.map f.appTop.hom) := by
  have h : ((ofIdealTop J).comap f).ideal ⟨⊤, isAffineOpen_top X⟩
      = (ofIdealTop (J.map f.appTop.hom)).ideal ⟨⊤, isAffineOpen_top X⟩ := by
    rw [comap_ideal_top_eq_map_appTop, ofIdealTop_ideal_top, ofIdealTop_ideal_top]
  exact (equivOfIsAffine (X := X)).injective h
end AlgebraicGeometry.Scheme.IdealSheafData
