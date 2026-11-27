-- Prove2me | solution 1 for P2M_GroundTheory_Arith_SchemeCoh_SchemeImage_exists_lift_image__morphismRestrict_9effc2b134c5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:52:21.896795+00:00
-- url     : https://prove2.me/submissions/3a217be0-f2da-4a03-bcb8-b89026c87cb6

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_SchemeImage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry CategoryTheory Limits
universe u
noncomputable section
open GroundTheory.Arith.SchemeCoh.SchemeImage
variable {Y Z : Scheme.{u}} (f : Y ⟶ Z) [QuasiCompact f] (W : Z.Opens)
namespace GroundTheory.Arith.SchemeCoh.SchemeImage
theorem _root_.solution {C : Scheme.{u}} (c : C ⟶ W.toScheme)
    [IsClosedImmersion c] (g : (f ⁻¹ᵁ W).toScheme ⟶ C) (hg : g ≫ c = f ∣_ W) :
    ∃ k : (f.imageι ⁻¹ᵁ W).toScheme ⟶ C, k ≫ c = f.imageι ∣_ W := by
  have H : c.ker ≤ (f.imageι ∣_ W).ker := by
    rw [ker_morphismRestrict, Scheme.IdealSheafData.ker_subschemeι, ← ker_morphismRestrict, ← hg]
    exact Scheme.Hom.le_ker_comp g c
  exact ⟨IsClosedImmersion.lift c _ H, IsClosedImmersion.lift_fac _ _ _⟩
end GroundTheory.Arith.SchemeCoh.SchemeImage
