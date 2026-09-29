-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_lawIso_appAdic_originParam_eq_of_variableChange_map_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/be8256bb-b8c2-52d3-81d0-3576c514df1c

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_VariableChangeSeries
import Theorems.Thm_WeierstrassCurve_coeff_one_variableChangeSeries_and_subst_formalGroupLawFixed
import Theorems.Thm_WeierstrassCurve_variableChangeDenom_map_and_variableChangeSeries_map
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_exists_reducesToOrigin_originParam_eq_evalSeries_of_isVariableChangeHom
import Theorems.Thm_FormalGroup_LawHom_exists_comp_appAdic_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_lawIso_appAdic_originParam_eq_of_variableChange_map_eq_one
p2m_attr_erase "instance" "WeierstrassCurve.instIsCommFormalGroup"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero FormalGroup.DrinfeldLevel.mk.sizeOf_spec FormalGroup.DrinfeldLevel.mk.injEq"

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {T : Type u} [CommRing T] [IsLocalRing T] [IsAdicComplete (maximalIdeal T) T]
    {k : Type u} [Field k] (resT : T →+* k) (hsT : Function.Surjective resT) (hkT : RingHom.ker resT = maximalIdeal T)
    (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T) (hC1 : C.map resT = 1)
    (W' : WeierstrassCurve T) (hW' : W' = C • W)
    (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
    (hφ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤
      (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ)
    (hvc : IsVariableChangeHom W C φ)
    (P Q : Section W) (χP χQ : OriginChartRing W →+* T)
    (hP : ReducesToOrigin P χP (maximalIdeal T)) (hQ : ReducesToOrigin Q χQ (maximalIdeal T))
    (P' Q' : Section W') (χP' χQ' : OriginChartRing W' →+* T)
    (hP' : ReducesToOrigin P' χP' (maximalIdeal T)) (hQ' : ReducesToOrigin Q' χQ' (maximalIdeal T))
    (hPP' : P'.1 ≫ eqToHom (congrArg projModelCR hW') ≫ Proj.map φ hφ = P.1)
    (hQQ' : Q'.1 ≫ eqToHom (congrArg projModelCR hW') ≫ Proj.map φ hφ = Q.1)
    (F' : FormalGroup T) (hF' : F'.toPowerSeries = W.formalGroupLawFixed)
    (GT : FormalGroup T) (hGT : GT.toPowerSeries = W'.formalGroupLawFixed)
    (G : FormalGroup T) (ψ : FormalGroup.LawIso GT G)
    (hψ : ∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0)
    (y₀ y₁ : T)
    (hy₀ : ψ.toLawHom.appAdic (maximalIdeal T) (originParam χP') = y₀)
    (hy₁ : ψ.toLawHom.appAdic (maximalIdeal T) (originParam χQ') = y₁) :
    ∃ ψ' : FormalGroup.LawIso F' G,
      (∀ n : ℕ, resT (PowerSeries.coeff n ψ'.series) = if n = 1 then 1 else 0) ∧
      ψ'.toLawHom.appAdic (maximalIdeal T) (originParam χP) = y₀ ∧
      ψ'.toLawHom.appAdic (maximalIdeal T) (originParam χQ) = y₁ := by
  classical
  subst hW'
  simp only [eqToHom_refl, Category.id_comp] at hPP' hQQ'
  have hmem : ∀ x : T, x ∈ maximalIdeal T ↔ resT x = 0 := fun x => by rw [← hkT, RingHom.mem_ker]
  have em : ∀ (S' : Type u) [CommRing S'] (f : T →+* S') (p : PowerSeries T), MvPowerSeries.map f p = PowerSeries.map f p :=
    fun _ _ _ _ => rfl

  have huniq : ∀ (S : Section (C • W)) (a b : OriginChartRing (C • W) →+* T),
      IsOriginChartSection S a → IsOriginChartSection S b → a = b := by
    intro S a b ha hb
    unfold IsOriginChartSection at ha hb
    have h1 : Spec.map (CommRingCat.ofHom a) = Spec.map (CommRingCat.ofHom b) := by
      rw [← cancel_mono (originChartι (C • W)), ← ha, ← hb]
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2

  obtain ⟨χ₁, hχ₁, hz₁⟩ := WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_originParam_eq_evalSeries_of_isVariableChangeHom
    W C φ hφ hvc P χP hP P' hPP'
  obtain ⟨χ₂, hχ₂, hz₂⟩ := WeierstrassCurve.DrinfeldGlobal.exists_reducesToOrigin_originParam_eq_evalSeries_of_isVariableChangeHom
    W C φ hφ hvc Q χQ hQ Q' hQQ'
  have e₁ : χ₁ = χP' := huniq P' χ₁ χP' hχ₁.1 hP'.1
  have e₂ : χ₂ = χQ' := huniq Q' χ₂ χQ' hχ₂.1 hQ'.1

  set s : PowerSeries T := W.variableChangeSeries C with hs
  obtain ⟨hs1, hscomm⟩ := WeierstrassCurve.coeff_one_variableChangeSeries_and_subst_formalGroupLawFixed W C
  let χC : FormalGroup.LawIso F' GT :=
    { series := s
      constantCoeff_series := by rw [hs]; exact WeierstrassCurve.constantCoeff_variableChangeSeries W C
      comm := by
        rw [hF', hGT]
        show PowerSeries.subst W.formalGroupLawFixed s =
          MvPowerSeries.subst ![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) T) s,
            PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) T) s] (C • W).formalGroupLawFixed
        rw [hs]; exact hscomm
      isUnit_coeff_one := by show IsUnit (PowerSeries.coeff 1 s); rw [hs, hs1]; exact Units.isUnit _ }
  have hχCs : χC.series = s := rfl

  have hvc1 : ∀ (V : WeierstrassCurve k), V.variableChangeSeries 1 = PowerSeries.X := by
    intro V
    have hden : V.variableChangeDenom 1 = 1 := by
      unfold WeierstrassCurve.variableChangeDenom
      rw [WeierstrassCurve.VariableChange.one_def]; simp
    unfold WeierstrassCurve.variableChangeSeries
    rw [hden]
    have hinv : PowerSeries.invOfUnit (1 : PowerSeries k) 1 = 1 := by
      have := PowerSeries.mul_invOfUnit (1 : PowerSeries k) 1 (by simp)
      rwa [one_mul] at this
    rw [hinv, WeierstrassCurve.VariableChange.one_def]; simp
  have hsres : PowerSeries.map resT s = PowerSeries.X := by
    rw [hs, ← (WeierstrassCurve.variableChangeDenom_map_and_variableChangeSeries_map W C resT).2, hC1, hvc1]
  have hψres : PowerSeries.map resT ψ.series = PowerSeries.X := by
    ext m; rw [PowerSeries.coeff_map, hψ m, PowerSeries.coeff_X]
  have hss : PowerSeries.HasSubst s := PowerSeries.HasSubst.of_constantCoeff_zero' χC.constantCoeff_series

  obtain ⟨ω, hωs, hωapp⟩ := FormalGroup.LawHom.exists_comp_appAdic_eq χC.toLawHom ψ.toLawHom
  have hωres : PowerSeries.map resT ω.series = PowerSeries.X := by
    rw [hωs, show χC.toLawHom.series = s from rfl, show ψ.toLawHom.series = ψ.series from rfl, ← em,
      PowerSeries.map_subst hss]
    try simp only [em]
    rw [hsres, hψres, PowerSeries.X_subst]
  have hωn : ∀ n : ℕ, resT (PowerSeries.coeff n ω.series) = if n = 1 then 1 else 0 := by
    intro n; rw [← PowerSeries.coeff_map, hωres, PowerSeries.coeff_X]
  have hω1 : IsUnit (PowerSeries.coeff 1 ω.series) := by
    by_contra hu
    have := (hmem _).mp ((IsLocalRing.mem_maximalIdeal _).mpr hu)
    rw [hωn 1, if_pos rfl] at this
    exact one_ne_zero this
  have happC : ∀ z : T, χC.toLawHom.appAdic (maximalIdeal T) z =
      (letI : WithIdeal T := ⟨maximalIdeal T⟩; FormalGroup.evalSeries (W.variableChangeSeries C) z) := fun z => rfl
  refine ⟨⟨ω, hω1⟩, hωn, ?_, ?_⟩
  · show ω.appAdic (maximalIdeal T) (originParam χP) = y₀
    rw [hωapp T (maximalIdeal T) (originParam χP) hP.2.1, happC, ← hz₁, e₁, hy₀]
  · show ω.appAdic (maximalIdeal T) (originParam χQ) = y₁
    rw [hωapp T (maximalIdeal T) (originParam χQ) hQ.2.1, happC, ← hz₂, e₂, hy₁]

end S_WeierstrassCurve_DrinfeldGlobal_exists_lawIso_appAdic_originParam_eq_of_variableChange_map_eq_one
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_lawIso_appAdic_originParam_eq_of_variableChange_map_eq_one (solution)
