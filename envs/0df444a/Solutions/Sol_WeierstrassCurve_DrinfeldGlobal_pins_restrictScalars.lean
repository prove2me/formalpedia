-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.pins_restrictScalars
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/7f4d3c81-8609-5042-ab91-972ab160f528

import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctorRestrict
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_pins_restrictScalars

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal ModularCurve

theorem solution
    (A₀ : Type u) [CommRing A₀] (A : Type u) [CommRing A] [Algebra A₀ A] (q : ℕ)
    (𝒢₀ : GroupLaws A₀) (h𝒢₀ : 𝒢₀.IsChordTangent) (h𝒢O₀ : 𝒢₀.IsOriginIdentity)
    (𝒯₀ : LevelTransport A₀ 𝒢₀ q) (h𝒯₀ : 𝒯₀.IsSectionTransport)
    (hCO₀ : ∀ (T T' : Type u) [CommRing T] [Algebra A₀ T] [CommRing T'] [Algebra A₀ T'] (f : T →ₐ[A₀] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ) :
    (𝒢₀.restrictScalars A).IsChordTangent ∧ (𝒢₀.restrictScalars A).IsOriginIdentity ∧
    (𝒯₀.restrictScalars A).IsSectionTransport ∧
    (∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ) := by
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro T _ _ W hΔ
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    exact h𝒢₀ T W hΔ
  · intro T _ _ W hΔ
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    exact h𝒢O₀ T W hΔ
  · intro T _ _ C x
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    exact h𝒯₀.1 T C x
  · intro T T' _ _ _ _ f x
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    letI : Algebra A₀ T' := algebraRestrict A₀ A T'
    exact h𝒯₀.2 T T' (algHomRestrict A₀ A f) x
  · intro T T' _ _ _ _ f W
    letI : Algebra A₀ T := algebraRestrict A₀ A T
    letI : Algebra A₀ T' := algebraRestrict A₀ A T'
    exact hCO₀ T T' (algHomRestrict A₀ A f) W

end S_WeierstrassCurve_DrinfeldGlobal_pins_restrictScalars
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_pins_restrictScalars (solution)
