-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds.finiteDimensional_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:05:22.353948+00:00
-- url     : https://prove2.me/submissions/ddca4ad6-06cc-4997-882b-05dff1e96cdd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjDefs
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsBisFurther
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjectiveFrameCoordNeZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_div_isIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_projective_frame_coord_ne_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_fnField_eq_adjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
theorem _root_.solution [Finite κ] (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) :
    FiniteDimensional (fnField (x ∘ e)) (IntermediateField.extendScalars (fnField_comp_le' x e)) := by
  rw [fnField_eq_adjoin x e (projective_frame_coord_ne_zero x e h)]
  have : Finite (Set.range fun i => x i / x (e 0)) := Set.finite_range _ |>.to_subtype
  exact IntermediateField.finiteDimensional_adjoin (by rintro _ ⟨i, rfl⟩; exact div_isIntegral x e h i)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
