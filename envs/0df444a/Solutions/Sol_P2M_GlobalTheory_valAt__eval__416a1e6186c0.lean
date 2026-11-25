-- Prove2me | solution 1 for P2M_GlobalTheory_valAt__eval__416a1e6186c0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:59:02.669254+00:00
-- url     : https://prove2.me/submissions/12b59b55-5d4b-4530-974e-bebf01070169

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AlgebraMapZeroSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsProjectiveModelPolarisedTorusTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {Y : Over (Sp ℂ)} (x : 𝟙_ (Over (Sp ℂ)) ⟶ Y) {U : Y.left.Opens} (h : ⊤ ≤ x.left ⁻¹ᵁ U) {σ : Type}
    (r : σ → Γ(Y.left, U)) (F : MvPolynomial σ ℂ) :
    valAt' x.left U (MvPolynomial.eval₂ (RingHom.comp (Y.hom.appLE ⊤ U le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) r F) = MvPolynomial.eval (fun c => valAt' x.left U (r c)) F := by
  set ψ : Γ(Y.left, U) →+* ℂ :=
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (x.left.appLE U ⊤ h).hom with hψ
  have hv : ∀ s, valAt' x.left U s = ψ s := fun s => by simp [valAt', valAt, h, ψ]
  have hw : x.left ≫ Y.hom = 𝟙 _ := by simpa using Over.w x
  have key : ∀ (g : Sp ℂ ⟶ Sp ℂ), g = 𝟙 _ → ∀ e (a : Γ(Sp ℂ, ⊤)), (g.appLE ⊤ ⊤ e).hom a = a := by
    rintro g rfl e a
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact congrArg (fun φ => (CommRingCat.Hom.hom φ) a) ((Sp ℂ).presheaf.map_id (Opposite.op ⊤))
  have hc : ψ.comp (RingHom.comp (Y.hom.appLE ⊤ U le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom) = RingHom.id ℂ := by
    have hmor : Y.hom.appLE ⊤ U le_top ≫ x.left.appLE U ⊤ h =
        (x.left ≫ Y.hom).appLE ⊤ ⊤ (fun _ _ => trivial) :=
      Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    ext a
    have h2 := congrArg (fun φ : Γ(Sp ℂ, ⊤) ⟶ Γ(Sp ℂ, ⊤) =>
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (φ.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a))) hmor
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
    have k := key _ hw (fun _ _ => trivial) ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)
    simp only [ψ, RingHom.comp_apply, RingHom.id_apply]
    exact h2.trans ((congrArg (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom k).trans (by simp))
  rw [hv, MvPolynomial.eval₂_comp_left, hc]
  simp only [hv]
  rfl
end GlobalTheory
