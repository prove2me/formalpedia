-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.rigidDataPow_raw_eq_act_of_curve_eq_of_level_eq_of_pair_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/5b9ed166-dfed-5b0b-b30f-f95eb95a2da5

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Theorems.Thm_WeierstrassProjModel_kwZeroSect_comp_projMap_of_isVariableChangeHom
import Theorems.Thm_WeierstrassProjModel_exists_isVariableChangeHom_isIso_projMap
import Theorems.Thm_WeierstrassProjModel_RelativeGroupLaw_exists_isOriginChartSection_iff_one_eq_kwZeroSect
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_rigidDataPow_raw_eq_act_of_curve_eq_of_level_eq_of_pair_eq_one

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

namespace F3SSRigid

variable {A : Type} [CommRing A]

theorem one_val_eq_zeroSect (𝒢 : GroupLaws A) (h𝒢O : 𝒢.IsOriginIdentity)
    {T : Type} [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (hΔ : IsUnit W.Δ) :
    ((𝒢 T W hΔ).one (𝟙 _)).1 = (kwZeroSect T W).1 :=
  (RelativeGroupLaw.exists_isOriginChartSection_iff_one_eq_kwZeroSect W (𝒢 T W hΔ)).mp (h𝒢O T W hΔ)

theorem pair_eq_one_of_comp_eq_zeroSect (𝒢 : GroupLaws A) (h𝒢O : 𝒢.IsOriginIdentity)
    {T : Type} [CommRing T] [Algebra A T]
    (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T)
    (m : projModelCR (C • W) ⟶ projModelCR W) [Mono m]
    (hzC : (kwZeroSect T (C • W)).1 ≫ m = (kwZeroSect T W).1)
    (z : RawDrinfeldPair T) (hc : z.curve = C • W)
    (hPz : z.P.1 ≫ eqToHom (congrArg projModelCR hc) ≫ m = (kwZeroSect T W).1)
    (hQz : z.Q.1 ≫ eqToHom (congrArg projModelCR hc) ≫ m = (kwZeroSect T W).1)
    (hΔ' : IsUnit z.curve.Δ) :
    z.P = (𝒢 T z.curve hΔ').one (𝟙 _) ∧ z.Q = (𝒢 T z.curve hΔ').one (𝟙 _) := by
  obtain ⟨Wz, Pz, Qz⟩ := z
  cases hc
  simp only [eqToHom_refl, Category.id_comp] at hPz hQz
  refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
  · refine ((cancel_mono m).mp (hPz.trans hzC.symm)).trans ?_
    exact (one_val_eq_zeroSect 𝒢 h𝒢O (C • W) hΔ').symm
  · refine ((cancel_mono m).mp (hQz.trans hzC.symm)).trans ?_
    exact (one_val_eq_zeroSect 𝒢 h𝒢O (C • W) hΔ').symm

theorem act_pair_eq_one (𝒢 : GroupLaws A) (h𝒢O : 𝒢.IsOriginIdentity) {q : ℕ}
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    {T : Type} [CommRing T] [Algebra A T]
    (C : WeierstrassCurve.VariableChange T) (x : RawDrinfeldPair T) (hΔ : IsUnit x.curve.Δ)
    (hP : x.P = (𝒢 T x.curve hΔ).one (𝟙 _)) (hQ : x.Q = (𝒢 T x.curve hΔ).one (𝟙 _))
    (hΔ' : IsUnit (𝒯.act C x).curve.Δ) :
    (𝒯.act C x).P = (𝒢 T (𝒯.act C x).curve hΔ').one (𝟙 _) ∧
      (𝒯.act C x).Q = (𝒢 T (𝒯.act C x).curve hΔ').one (𝟙 _) := by
  obtain ⟨hc, hsec⟩ := h𝒯.1 T C x
  obtain ⟨φ, hφ, hvc, hiso, -⟩ := exists_isVariableChangeHom_isIso_projMap x.curve C
  obtain ⟨hP', hQ'⟩ := hsec φ hφ hvc
  have hzW : x.P.1 = (kwZeroSect T x.curve).1 := by
    rw [hP]; exact one_val_eq_zeroSect 𝒢 h𝒢O x.curve hΔ
  have hzWQ : x.Q.1 = (kwZeroSect T x.curve).1 := by
    rw [hQ]; exact one_val_eq_zeroSect 𝒢 h𝒢O x.curve hΔ
  have hzC : (kwZeroSect T (C • x.curve)).1 ≫ Proj.map φ hφ = (kwZeroSect T x.curve).1 :=
    kwZeroSect_comp_projMap_of_isVariableChangeHom x.curve C φ hφ hvc
  haveI : IsIso (Proj.map φ hφ) := hiso
  exact pair_eq_one_of_comp_eq_zeroSect 𝒢 h𝒢O x.curve C (Proj.map φ hφ) hzC (𝒯.act C x) hc
    (hP'.trans hzW) (hQ'.trans hzWQ) hΔ'

theorem rawDrinfeldPair_eq_of_origin (𝒢 : GroupLaws A) {T : Type} [CommRing T] [Algebra A T]
    (y z : RawDrinfeldPair T) (hc : y.curve = z.curve)
    (hy : ∃ hΔ : IsUnit y.curve.Δ,
      y.P = (𝒢 T y.curve hΔ).one (𝟙 _) ∧ y.Q = (𝒢 T y.curve hΔ).one (𝟙 _))
    (hz : ∀ hΔ : IsUnit z.curve.Δ,
      z.P = (𝒢 T z.curve hΔ).one (𝟙 _) ∧ z.Q = (𝒢 T z.curve hΔ).one (𝟙 _)) :
    y = z := by
  obtain ⟨Wy, Py, Qy⟩ := y
  obtain ⟨Wz, Pz, Qz⟩ := z
  cases hc
  obtain ⟨hΔ, h1, h2⟩ := hy
  obtain ⟨h3, h4⟩ := hz hΔ
  dsimp only at h1 h2 h3 h4
  rw [h1, h2, h3, h4]

end F3SSRigid

open F3SSRigid in
theorem solution
    (A : Type) [CommRing A] (ℓ M' q : ℕ)
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (T : Type) [CommRing T] [Algebra A T]
    (x x' : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T) (C : WeierstrassCurve.VariableChange T)

    (hcurve : x'.curve = ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).act C x).curve)
    (htuple : x'.level.1 = ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).act C x).level.1)
    (hkatz : x'.level.2.1 = ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).act C x).level.2.1)

    (hx : ∃ hΔ : IsUnit x.level.2.2.curve.Δ,
      x.level.2.2.P = (𝒢 T x.level.2.2.curve hΔ).one (𝟙 _) ∧ x.level.2.2.Q = (𝒢 T x.level.2.2.curve hΔ).one (𝟙 _))
    (hx' : ∃ hΔ : IsUnit x'.level.2.2.curve.Δ,
      x'.level.2.2.P = (𝒢 T x'.level.2.2.curve hΔ).one (𝟙 _) ∧ x'.level.2.2.Q = (𝒢 T x'.level.2.2.curve hΔ).one (𝟙 _)) :
    x' = (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).act C x := by

  refine ModularCurve.LevelComponent.Raw.ext' hcurve ?_

  refine Prod.ext htuple (Prod.ext hkatz ?_)
  change x'.level.2.2 = 𝒯.act C x.level.2.2

  have hxl : _ ∧ _ ∧ RawDrinfeldPair.IsLevel 𝒢 q x.curve x.level.2.2 := x.isLevel
  have hx'l : _ ∧ _ ∧ RawDrinfeldPair.IsLevel 𝒢 q x'.curve x'.level.2.2 := x'.isLevel
  have hxc : x.level.2.2.curve = x.curve := hxl.2.2.1
  have hx'c : x'.level.2.2.curve = x'.curve := hx'l.2.2.1
  have hcurve' : x'.curve = C • x.curve := hcurve
  obtain ⟨hcz, -⟩ := h𝒯.1 T C x.level.2.2
  obtain ⟨hΔx, hxP, hxQ⟩ := hx
  refine rawDrinfeldPair_eq_of_origin 𝒢 x'.level.2.2 (𝒯.act C x.level.2.2) ?_ hx'
    (fun hΔ' => act_pair_eq_one 𝒢 h𝒢O 𝒯 h𝒯 C x.level.2.2 hΔx hxP hxQ hΔ')
  rw [hx'c, hcurve', hcz, hxc]

#print axioms solution

end S_WeierstrassCurve_DrinfeldGlobal_rigidDataPow_raw_eq_act_of_curve_eq_of_level_eq_of_pair_eq_one
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_rigidDataPow_raw_eq_act_of_curve_eq_of_level_eq_of_pair_eq_one (solution)
