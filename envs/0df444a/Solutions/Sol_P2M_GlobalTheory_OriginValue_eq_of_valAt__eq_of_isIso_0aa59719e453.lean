-- Prove2me | solution 1 for P2M_GlobalTheory_OriginValue_eq_of_valAt__eq_of_isIso_0aa59719e453
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:39:47.326266+00:00
-- url     : https://prove2.me/submissions/d02a57fd-0bfe-456d-9501-dc172214432c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenIsValueAtOrigin
import Theorems.Thm_GlobalTheory_top_le_preimage_iff_mem
import Theorems.Thm_P2M_GlobalTheory_valAt__eq_valAt_cd16e0b92c48


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.OriginValue
namespace GlobalTheory.OriginValue
theorem _root_.solution {X : Scheme.{0}} (x : Sp ℂ ⟶ X) [IsIso x] (W : X.Opens) (f g : Γ(X, W))
    (h : ⊤ ≤ x ⁻¹ᵁ W → valAt' x W f = valAt' x W g) : f = g := by
  by_cases hW : ⊤ ≤ x ⁻¹ᵁ W
  · have h1 := h hW
    rw [valAt'_eq_valAt x hW, valAt'_eq_valAt x hW, valAt, valAt] at h1
    have h2 := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).1 h1
    have e : (⊤ : (Sp ℂ).Opens) = x ⁻¹ᵁ W := le_antisymm hW le_top
    have : IsIso (homOfLE hW) := ⟨⟨homOfLE le_top, rfl, rfl⟩⟩
    have : IsIso (x.appLE W ⊤ hW) := by
      unfold Scheme.Hom.appLE
      infer_instance
    exact (ConcreteCategory.bijective_of_isIso (x.appLE W ⊤ hW)).1 h2
  · have hb : W = ⊥ := by
      rw [top_le_preimage_iff_mem] at hW
      refine le_bot_iff.1 fun y hy => ?_
      obtain ⟨q, rfl⟩ := x.surjective y
      have : q = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
      subst this
      exact (hW hy).elim
    subst hb
    exact Subsingleton.elim _ _
end GlobalTheory.OriginValue
