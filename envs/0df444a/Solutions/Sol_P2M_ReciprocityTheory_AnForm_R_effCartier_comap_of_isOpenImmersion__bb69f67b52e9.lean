-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_R_effCartier_comap_of_isOpenImmersion__bb69f67b52e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:49:59.89811+00:00
-- url     : https://prove2.me/submissions/43f2cb5f-e95e-4541-ade6-2a702c0ae8f2

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB
import Theorems.Thm_ReciprocityTheory_AnForm_R_algebraMap_mem_nonZeroDivisors_of_isLocalization
import Theorems.Thm_ReciprocityTheory_AnForm_R_ringEquiv_mem_nonZeroDivisors

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
theorem _root_.solution {X Y : Scheme.{0}} (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (hI : FinalTheorems.EffCartier I) : FinalTheorems.EffCartier (I.comap f) := by
  intro x
  obtain ⟨U, h, hxU, hh, hU⟩ := hI (f x)
  obtain ⟨r, hrle, hxr⟩ := U.2.exists_basicOpen_le (V := f.opensRange) ⟨f x, ⟨x, rfl⟩⟩ hxU
  have himg : f ''ᵁ (f ⁻¹ᵁ Y.basicOpen r) = Y.basicOpen r := by
    rw [f.image_preimage_eq_opensRange_inf, inf_eq_right.2 hrle]
  have hUX : IsAffineOpen (f ⁻¹ᵁ Y.basicOpen r) := by
    rw [← f.isAffineOpen_iff_of_isOpenImmersion, himg]; exact U.2.basicOpen r
  have hle : f ''ᵁ (f ⁻¹ᵁ Y.basicOpen r) ≤ U.1 := himg.le.trans (Y.basicOpen_le r)
  have hnzd : ∀ (O : Y.Opens) (hO : O = Y.basicOpen r) (hOU : O ≤ U.1),
      Y.presheaf.map (homOfLE hOU).op h ∈ nonZeroDivisors Γ(Y, O) := by
    rintro O rfl hOU
    have := U.2.isLocalization_basicOpen r
    exact algebraMap_mem_nonZeroDivisors_of_isLocalization (Submonoid.powers r) hh
  let e := (f.appIso (f ⁻¹ᵁ Y.basicOpen r)).commRingCatIsoToRingEquiv
  refine ⟨⟨_, hUX⟩, e (Y.presheaf.map (homOfLE hle).op h), hxr, ?_, ?_⟩
  · exact ringEquiv_mem_nonZeroDivisors e (hnzd _ himg hle)
  · rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
    rw [← I.map_ideal (U := ⟨_, (f.isAffineOpen_iff_of_isOpenImmersion).2 hUX⟩) (V := U) hle, hU,
      Ideal.map_span, Set.image_singleton]
    rw [show ((f.appIso (f ⁻¹ᵁ Y.basicOpen r)).inv.hom : _ →+* _) = (e.symm : _ →+* _) from rfl,
      Ideal.comap_coe, Ideal.comap_symm, Ideal.map_span, Set.image_singleton]
    rfl
end ReciprocityTheory.AnForm.R
