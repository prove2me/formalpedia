-- Prove2me | solution 1 for P2M_RH_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul_ffd4b47c5064b9ee
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:42:39.110236+00:00
-- url     : https://prove2.me/submissions/7c62eb73-20fe-45cd-bb45-f2775c669008

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ideal_eq_map_appLE
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_affineOpens_mem
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_affineOpens_mem_le


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
theorem _root_.solution (I J : Y.IdealSheafData) (f : X ⟶ Y) :
    (I * J).comap f = I.comap f * J.comap f := by
  refine ext_of_iSup_eq_top
    (fun W : {W : X.affineOpens // ∃ U : Y.affineOpens, (W : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens)} =>
      W.1) ?_ ?_
  · refine TopologicalSpace.Opens.ext ?_
    simp only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top,
      Set.eq_univ_iff_forall, Set.mem_iUnion]
    intro x
    obtain ⟨W, hxW⟩ := Scheme.exists_affineOpens_mem (f.base x)
    obtain ⟨V, hxV, hVW⟩ :
        ∃ V : X.affineOpens, x ∈ (V : X.Opens) ∧ (V : X.Opens) ≤ f ⁻¹ᵁ (W : Y.Opens) :=
      Scheme.exists_affineOpens_mem_le hxW
    exact ⟨⟨V, W, hVW⟩, hxV⟩
  · rintro ⟨V, W, hVW⟩
    show ((I * J).comap f).ideal V = (I.comap f * J.comap f).ideal V
    rw [comap_ideal_eq_map_appLE (I * J) f W V hVW]
    simp only [ideal_mul, Pi.mul_apply]
    rw [Ideal.map_mul, comap_ideal_eq_map_appLE I f W V hVW,
      comap_ideal_eq_map_appLE J f W V hVW]
end AlgebraicGeometry.Scheme.IdealSheafData
