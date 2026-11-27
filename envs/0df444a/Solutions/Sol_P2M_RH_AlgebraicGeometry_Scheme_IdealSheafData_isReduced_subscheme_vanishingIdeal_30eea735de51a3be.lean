-- Prove2me | solution 1 for P2M_RH_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_30eea735de51a3be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:19:29.531798+00:00
-- url     : https://prove2.me/submissions/9b62d35c-8d69-4dcd-a0d4-8fc27c4618c0

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_affineOpens_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}}
private theorem isReduced_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) (h : _root_.IsReduced B) : _root_.IsReduced A := by
  have := h
  exact ⟨fun a ha => e.injective (by simpa using (ha.map (e : A →+* B)).eq_zero)⟩
private theorem isReduced_stalk_of_radical (I : X.IdealSheafData)
    (hrad : ∀ U : X.affineOpens, (I.ideal U).IsRadical) (y : ↥I.subscheme) :
    _root_.IsReduced (I.subscheme.presheaf.stalk y) := by
  obtain ⟨U, hU⟩ := Scheme.exists_affineOpens_mem (I.subschemeι.base y)
  have hUaff : IsAffineOpen (U : X.Opens) := U.2
  have hy : y ∈ I.subschemeι ⁻¹ᵁ (U : X.Opens) := hU
  have hV : IsAffineOpen (I.subschemeι ⁻¹ᵁ (U : X.Opens)) :=
    IsAffineOpen.preimage hUaff I.subschemeι
  have hquot := (Ideal.isRadical_iff_quotient_reduced (I.ideal U)).mp (hrad U)
  have hGamma := isReduced_of_ringEquiv (I.subschemeObjIso U).commRingCatIsoToRingEquiv hquot
  have hTop := isReduced_of_ringEquiv (Scheme.Opens.topIso
    (I.subschemeι ⁻¹ᵁ (U : X.Opens))).commRingCatIsoToRingEquiv hGamma
  have : IsAffine (↑(I.subschemeι ⁻¹ᵁ (U : X.Opens)) : Scheme.{u}) := hV
  have := hTop
  have : IsReduced (↑(I.subschemeι ⁻¹ᵁ (U : X.Opens)) : Scheme.{u}) :=
    isReduced_of_isAffine_isReduced _
  have key : _root_.IsReduced
      ((↑(I.subschemeι ⁻¹ᵁ (U : X.Opens)) : Scheme.{u}).presheaf.stalk
        (⟨y, hy⟩ : ↥(I.subschemeι ⁻¹ᵁ (U : X.Opens)))) :=
    isReduced_stalk_of_isReduced (↑(I.subschemeι ⁻¹ᵁ (U : X.Opens)) : Scheme.{u})
      (⟨y, hy⟩ : ↥(I.subschemeι ⁻¹ᵁ (U : X.Opens)))
  exact isReduced_of_ringEquiv
    (Scheme.Opens.stalkIso (I.subschemeι ⁻¹ᵁ (U : X.Opens))
      (⟨y, hy⟩ : ↥(I.subschemeι ⁻¹ᵁ (U : X.Opens)))).symm.commRingCatIsoToRingEquiv key
end AlgebraicGeometry.Scheme.IdealSheafData
namespace FunctorialResolution.Blowup
end FunctorialResolution.Blowup
namespace AlgebraicGeometry.Scheme.IdealSheafData
end AlgebraicGeometry.Scheme.IdealSheafData
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}}
namespace AlgebraicGeometry.Scheme.IdealSheafData
theorem _root_.solution
    (W : Scheme.{u}) (Z : TopologicalSpace.Closeds W) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  have : ∀ y : ↥((Scheme.IdealSheafData.vanishingIdeal Z).subscheme),
      _root_.IsReduced
        ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme.presheaf.stalk y) := by
    intro y
    refine isReduced_stalk_of_radical _ ?_ y
    intro U
    rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  exact isReduced_of_isReduced_stalk _
end AlgebraicGeometry.Scheme.IdealSheafData
