-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.shape_cross
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:45:03.874145+00:00
-- url     : https://prove2.me/submissions/1ea26404-c9f7-4315-a868-780f353a397b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RValue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpandsAtScale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_resTop
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_app_rs_alt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_app_rs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_app_congr_rs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_app_resTop_alt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_rs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable {G : Over (Spec (CommRingCat.of V))}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {Y Y' : Scheme.{0}} (h : Y' ⟶ Y) (e : Y' ⟶ Y') (fl : Y ⟶ Y) (he : e ≫ h = h ≫ fl)
    (c : Fin 2 → Γ(Y', ⊤)) (hce : ∀ i, e.appTop.hom (c i) = c i)
    {Ua Ub O : Y.Opens} {Sa Sb Wa Wb W : Y'.Opens}
    (oa : O ≤ Ua) (ob : O ≤ fl ⁻¹ᵁ Ub) (hWa : Wa ≤ h ⁻¹ᵁ Ua) (hWa' : Wa ≤ Sa) (hWb : Wb ≤ h ⁻¹ᵁ Ub) (hWb' : Wb ≤ Sb)
    (wO : W ≤ h ⁻¹ᵁ O) (wa : W ≤ Wa) (wSa : W ≤ Sa) (wb : W ≤ e ⁻¹ᵁ Wb) (wSb : W ≤ e ⁻¹ᵁ Sb)
    (hunit : ∀ i, IsUnit (resTop W (c i)))
    (σ : Fin 2 → Γ(Y, Ua)) (τ : Fin 2 → Γ(Y, Ub)) (x : Fin 2 → Γ(Y', Sa)) (y : Fin 2 → Γ(Y', Sb))
    (hC : rs oa (σ 0) * rs ob ((fl.app Ub).hom (τ 1)) = rs oa (σ 1) * rs ob ((fl.app Ub).hom (τ 0)))
    (hσ : ∀ i, rs hWa ((h.app Ua).hom (σ i)) = resTop Wa (c i) * rs hWa' (x i))
    (hτ : ∀ i, rs hWb ((h.app Ub).hom (τ i)) = resTop Wb (c i) * rs hWb' (y i)) :
    rs wSa (x 0) * rs wSb ((e.app Sb).hom (y 1)) = rs wSa (x 1) * rs wSb ((e.app Sb).hom (y 0)) := by

  have h1 := congrArg (rs wO) (congrArg (h.app O).hom hC)
  rw [map_mul, map_mul, rs_mul, rs_mul] at h1

  have fσ : ∀ i, rs wO ((h.app O).hom (rs oa (σ i))) = resTop W (c i) * rs wSa (x i) := by
    intro i
    have := congrArg (rs wa) (hσ i)
    rw [rs_mul, rs_resTop, rs_rs, rs_rs] at this
    rw [app_rs_alt h oa wO (wa.trans hWa)]
    exact this
  have fτ : ∀ i, rs wO ((h.app O).hom (rs ob ((fl.app Ub).hom (τ i)))) =
      resTop W (c i) * rs wSb ((e.app Sb).hom (y i)) := by
    intro i
    have w1 : W ≤ h ⁻¹ᵁ (fl ⁻¹ᵁ Ub) := fun p hp => ob (wO hp)
    have w2 : W ≤ (e ≫ h) ⁻¹ᵁ Ub := fun p hp => by
      have := w1 hp
      show p ∈ (e ≫ h) ⁻¹ᵁ Ub
      rw [he]
      exact this
    have w3 : W ≤ e ⁻¹ᵁ (h ⁻¹ᵁ Ub) := w2
    rw [app_rs_alt h ob wO w1, ← comp_app_rs h fl w1 w1, app_congr_rs (h ≫ fl) (e ≫ h) he.symm w1 w2,
      comp_app_rs e h w2 w3, ← app_rs_alt e hWb wb w3, hτ i, map_mul, rs_mul, app_resTop_alt, hce,
      app_rs_alt e hWb' wb wSb]
  rw [fσ, fσ, fτ, fτ] at h1
  obtain ⟨u0, hu0⟩ := hunit 0
  obtain ⟨u1, hu1⟩ := hunit 1
  rw [← hu0, ← hu1] at h1
  have h2 : (↑u0 * ↑u1) * (rs wSa (x 0) * rs wSb ((e.app Sb).hom (y 1))) =
      (↑u0 * ↑u1) * (rs wSa (x 1) * rs wSb ((e.app Sb).hom (y 0))) := by
    linear_combination h1
  exact (Units.mul_right_inj (u0 * u1)).1 (by simpa [Units.val_mul] using h2)
end ReciprocityTheory.ChartRestriction.G.DVR
