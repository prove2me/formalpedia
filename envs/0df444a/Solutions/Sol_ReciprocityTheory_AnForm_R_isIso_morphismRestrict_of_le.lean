-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.isIso_morphismRestrict_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:10:11.851538+00:00
-- url     : https://prove2.me/submissions/e62f6144-e13d-4b93-b7c5-d1e452d5eeb2

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjBCompl
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {X Y : Scheme.{0}} (f : X ⟶ Y) {U V : Y.Opens} (h : V ≤ U)
    [IsIso (f ∣_ U)] : IsIso (f ∣_ V) := by
  have e : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    ext x
    simp only [Scheme.Hom.coe_image, Scheme.Hom.coe_preimage, Set.image_preimage_eq_inter_range,
      Scheme.Opens.range_ι, SetLike.mem_coe, Set.mem_inter_iff]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, h hx⟩⟩
  have h1 : IsIso (f ∣_ U ∣_ (U.ι ⁻¹ᵁ V)) := inferInstance
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f U _ ≪≫ morphismRestrictEq f e)).1 h1
end ReciprocityTheory.AnForm.R
