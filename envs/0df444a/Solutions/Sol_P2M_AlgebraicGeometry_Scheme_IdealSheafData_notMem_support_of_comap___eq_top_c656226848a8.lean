-- Prove2me | solution 1 for P2M_AlgebraicGeometry_Scheme_IdealSheafData_notMem_support_of_comap___eq_top_c656226848a8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:30:48.565012+00:00
-- url     : https://prove2.me/submissions/982c5e99-a812-4e6c-90ce-ccc32bb1ebfe

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
theorem _root_.solution (I : Y.IdealSheafData) {U : Y.Opens}
    (h : I.comap U.ι = ⊤) {x : Y} (hxU : x ∈ U) : x ∉ I.support := by
  intro hx
  have h1 : (⟨x, hxU⟩ : ↥U) ∈ (I.comap U.ι).support := by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.support_comap]
    exact hx
  rw [h, AlgebraicGeometry.Scheme.IdealSheafData.support_top] at h1
  have h2 : (⟨x, hxU⟩ : ↥U) ∈ ((⊥ : TopologicalSpace.Closeds ↥U) : Set ↥U) := h1
  simp at h2
end AlgebraicGeometry.Scheme.IdealSheafData
