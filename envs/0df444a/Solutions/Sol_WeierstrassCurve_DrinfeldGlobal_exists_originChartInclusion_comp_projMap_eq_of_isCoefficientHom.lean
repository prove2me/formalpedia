-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_originChartInclusion_comp_projMap_eq_of_isCoefficientHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/8dafd513-5b10-523b-a879-9f7f9db134a2

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_originChartInclusion_comp_projMap_eq_of_isCoefficientHom

set_option autoImplicit false

universe u

p2m_open "AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_originChartInclusion_comp_projMap_eq_of_isCoefficientHom.WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization"

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "map mk Projective"
namespace DrinfeldGlobal
p2m_export "WeierstrassCurve.DrinfeldGlobal" "base IsCoefficientHom coord coord_mem OriginChartRing originChartι xOverY zOverY"
namespace ChartLift
p2m_open "WeierstrassCurve.DrinfeldGlobal WeierstrassCurve"

open MvPolynomial

theorem main {T T' : Type u} [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T) (f : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    {B : Type u} [CommRing B] :
    ∀ (s' : ProjModelRingCR (W.map f)) (e : φ (coord W 1) = s') (hs' : s' ∈ projModelGradingCR (W.map f) 1)
      (hle : Submonoid.powers (coord W 1) ≤ (Submonoid.powers s').comap φ)
      (χ' : Away (projModelGradingCR (W.map f)) s' →+* B),
      Spec.map (CommRingCat.ofHom χ') ≫ Proj.awayι (projModelGradingCR (W.map f)) s' hs' one_pos ≫ Proj.map φ hφ =
        Spec.map (CommRingCat.ofHom (χ'.comp (HomogeneousLocalization.map φ hle))) ≫ originChartι W := by
  rintro s' rfl hs' hle χ'
  rw [Proj.awayι_comp_map φ hφ one_pos (coord W 1) (coord_mem W 1), ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

end WeierstrassCurve.DrinfeldGlobal.ChartLift

open WeierstrassCurve.DrinfeldGlobal.ChartLift MvPolynomial in
theorem solution
    {T T' : Type u} [CommRing T] [CommRing T'] (W : WeierstrassCurve.Projective T) (f : T →+* T')
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hcoef : IsCoefficientHom W f φ)
    {B : Type u} [CommRing B] (χ' : OriginChartRing (W.map f) →+* B) :
    ∃ χ : OriginChartRing W →+* B,
      Spec.map (CommRingCat.ofHom χ') ≫ originChartι (W.map f) ≫ Proj.map φ hφ =
        Spec.map (CommRingCat.ofHom χ) ≫ originChartι W ∧
      (∀ t : T, χ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
        χ' (fromZeroRingHom (projModelGradingCR (W.map f)) _ (algebraMap T' ((projModelGradingCR (W.map f)) 0) (f t)))) ∧
      χ (xOverY W) = χ' (xOverY (W.map f)) ∧ χ (zOverY W) = χ' (zOverY (W.map f)) := by
  have e : φ (coord W 1) = coord (W.map f) 1 := hcoef.2 1
  have hle : Submonoid.powers (coord W 1) ≤ (Submonoid.powers (coord (W.map f) 1)).comap φ := by
    rintro _ ⟨n, rfl⟩; exact ⟨n, by simp [e]⟩
  let θ : OriginChartRing W →+* OriginChartRing (W.map f) := HomogeneousLocalization.map φ hle
  have h1 := main W f φ hφ (coord (W.map f) 1) e (coord_mem (W.map f) 1) hle χ'

  have hx : θ (xOverY W) = xOverY (W.map f) := by
    refine HomogeneousLocalization.val_injective _ ?_
    simp only [θ, xOverY, HomogeneousLocalization.Away.mk, HomogeneousLocalization.map_mk,
      HomogeneousLocalization.val_mk]
    congr 1
    · exact hcoef.2 0
    · exact Subtype.ext (by simp [e])
  have hz : θ (zOverY W) = zOverY (W.map f) := by
    refine HomogeneousLocalization.val_injective _ ?_
    simp only [θ, zOverY, HomogeneousLocalization.Away.mk, HomogeneousLocalization.map_mk,
      HomogeneousLocalization.val_mk]
    congr 1
    · exact hcoef.2 2
    · exact Subtype.ext (by simp [e])
  have hsc : ∀ t : T, θ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
      fromZeroRingHom (projModelGradingCR (W.map f)) _ (algebraMap T' ((projModelGradingCR (W.map f)) 0) (f t)) := by
    intro t
    refine HomogeneousLocalization.val_injective _ ?_
    simp only [θ, HomogeneousLocalization.fromZeroRingHom, HomogeneousLocalization.map_mk,
      HomogeneousLocalization.val_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    congr 1
    · exact hcoef.1 t
    · exact Subtype.ext (by simp)
  exact ⟨χ'.comp θ, h1, fun t ↦ congrArg χ' (hsc t), congrArg χ' hx, congrArg χ' hz⟩

end S_WeierstrassCurve_DrinfeldGlobal_exists_originChartInclusion_comp_projMap_eq_of_isCoefficientHom
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_originChartInclusion_comp_projMap_eq_of_isCoefficientHom (solution)
