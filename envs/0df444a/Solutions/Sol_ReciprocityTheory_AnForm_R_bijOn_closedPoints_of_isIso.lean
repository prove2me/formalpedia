-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.bijOn_closedPoints_of_isIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:54:37.945014+00:00
-- url     : https://prove2.me/submissions/dd71d362-b7e3-4967-99c0-32e20b220834

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SecHomSurjective
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BijOnClosedPointsOfIsIso
import Theorems.Thm_ReciprocityTheory_AnForm_R_isClosed_image_of_closed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory MvPolynomial
noncomputable section
variable {W X : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)} {sX : X ⟶ Spec (.of ℂ)}
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (π : W ⟶ X) (hπ : π ≫ sX = sW) [LocallyOfFiniteType sW]
    [LocallyOfFiniteType sX] (U : X.Opens) [IsIso (π ∣_ U)] :
    Set.BijOn π.base {x | IsClosed ({x} : Set W) ∧ π.base x ∈ U}
      {y | IsClosed ({y} : Set X) ∧ y ∈ U} := by
  let h := Scheme.homeoOfIso (asIso (π ∣_ U))
  have hb : ∀ z, (h z).1 = π.base z.1 := fun z => morphismRestrict_base_coe π U z
  refine ⟨fun x hx => ⟨isClosed_image_of_closed sW sX π hπ x hx.1, hx.2⟩, ?_, ?_⟩
  · intro x₁ hx₁ x₂ hx₂ he
    have e1 : h ⟨x₁, hx₁.2⟩ = h ⟨x₂, hx₂.2⟩ :=
      Subtype.ext ((hb ⟨x₁, hx₁.2⟩).trans (he.trans (hb ⟨x₂, hx₂.2⟩).symm))
    exact congrArg Subtype.val (h.injective e1)
  · intro y hy
    let w := h.symm ⟨y, hy.2⟩
    have hw : h w = ⟨y, hy.2⟩ := h.apply_symm_apply _
    have hcl : IsClosed ({h w} : Set _) := by
      refine isClosed_induced_iff.mpr ⟨{y}, hy.1, Set.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
      · exact Subtype.ext (hz.trans (congrArg Subtype.val hw).symm)
      · exact (congrArg Subtype.val hz).trans (congrArg Subtype.val hw)
    have hcw : IsClosed ({w} : Set _) := by
      have := hcl.preimage h.continuous
      rwa [← Set.image_singleton, h.injective.preimage_image] at this
    have hW : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace sW
    refine ⟨w.1, ⟨?_, w.2⟩, (hb w).symm.trans (congrArg Subtype.val hw)⟩
    apply isClosed_singleton_of_isLocallyClosed_singleton
    obtain ⟨t, ht, hteq⟩ := isClosed_induced_iff.mp hcw
    refine ⟨((π ⁻¹ᵁ U : W.Opens) : Set W), t, (π ⁻¹ᵁ U).isOpen, ht, ?_⟩
    ext z
    constructor
    · rintro rfl
      exact ⟨w.2, (Set.ext_iff.mp hteq w).mpr rfl⟩
    · rintro ⟨hzV, hzt⟩
      have e : (⟨z, hzV⟩ : ((π ⁻¹ᵁ U : W.Opens) : Set W)) = w := (Set.ext_iff.mp hteq ⟨z, hzV⟩).mp hzt
      show z = w.1
      exact congrArg Subtype.val e
end ReciprocityTheory.AnForm.R
