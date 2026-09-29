-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.map_ker_eq_span_X_sub_C_originParam
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/6e9421f0-0f28-5189-8efa-cd687a62611f

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_FormalGroup_NSeries
import Theorems.Thm_FormalGroup_exists_ringHom_evalSeries_eq
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_originW_eq_evalSeries_formalW_originParam_of_isOriginChartSection
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_ker_eq_span_of_originChartRing
import Theorems.Thm_FormalGroup_ker_evalSeries_eq_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_map_ker_eq_span_X_sub_C_originParam

set_option autoImplicit false

universe u

p2m_open "AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal P2MW.S_WeierstrassCurve_DrinfeldGlobal_map_ker_eq_span_X_sub_C_originParam.WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization"

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "a₃ a₁ map a₄ a₂ a₆ map_id map_injective formalW formalW_eq DrinfeldGlobal.originW_eq_evalSeries_formalW_originParam_of_isOriginChartSection DrinfeldGlobal.ker_eq_span_of_originChartRing"
namespace DrinfeldGlobal
p2m_export "WeierstrassCurve.DrinfeldGlobal" "Section OriginChartRing xOverY zOverY IsOriginChartSection originParam originW ReducesToOrigin originW_eq_evalSeries_formalW_originParam_of_isOriginChartSection ker_eq_span_of_originChartRing"
namespace GraphIdealImage
p2m_open "WeierstrassCurve.DrinfeldGlobal WeierstrassCurve"

lemma apply_sc_eq {T : Type u} [CommRing T] (W : WeierstrassCurve T) (P : Section W) (χ : OriginChartRing W →+* T)
    (hχ : IsOriginChartSection P χ) (t : T) :
    χ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) = t := by
  have h := P.2
  rw [hχ] at h
  simp only [projModelStrCR, Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp] at h
  have h2 : Spec.map (CommRingCat.ofHom (algebraMap T ((projModelGradingCR W) 0)) ≫
      CommRingCat.ofHom (fromZeroRingHom (projModelGradingCR W) _) ≫ CommRingCat.ofHom χ) =
      Spec.map (𝟙 _) := by rw [Spec.map_id]; exact h
  have h3 := Spec.map_injective h2
  have h4 := congrArg (fun g : CommRingCat.of T ⟶ CommRingCat.of T => g.hom t) h3
  simpa using h4

end WeierstrassCurve.DrinfeldGlobal.GraphIdealImage

open WeierstrassCurve.DrinfeldGlobal.GraphIdealImage in
theorem solution
    {T : Type u} [CommRing T] [IsLocalRing T] [IsAdicComplete (maximalIdeal T) T]
    (W : WeierstrassCurve T) (P : Section W) (χ : OriginChartRing W →+* T)
    (hP : ReducesToOrigin P χ (maximalIdeal T))
    (Φ : OriginChartRing W →+* PowerSeries T)
    (hΦsc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY W) = - PowerSeries.X) (hΦz : Φ (zOverY W) = - W.formalW) :
    (RingHom.ker χ).map Φ = Ideal.span {PowerSeries.X - PowerSeries.C (originParam χ)} := by
  obtain ⟨hsec, hz, hw⟩ := hP
  have hsc : ∀ t : T, χ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) = t :=
    fun t ↦ apply_sc_eq W P χ hsec t
  rw [WeierstrassCurve.DrinfeldGlobal.ker_eq_span_of_originChartRing W χ hsc, Ideal.map_span,
    Set.image_insert_eq, Set.image_singleton, map_sub, map_sub, hΦx, hΦz, hΦsc, hΦsc]

  obtain ⟨e, he, hep⟩ := FormalGroup.exists_ringHom_evalSeries_eq (maximalIdeal T) (originParam χ) hz
  have hker : RingHom.ker e = Ideal.span {PowerSeries.X - PowerSeries.C (originParam χ)} :=
    FormalGroup.ker_evalSeries_eq_span (originParam χ) hz e he
  have hwz : W.formalW - PowerSeries.C (originW χ) ∈ Ideal.span {PowerSeries.X - PowerSeries.C (originParam χ)} := by
    rw [← hker, RingHom.mem_ker, map_sub, ← he,
      ← WeierstrassCurve.DrinfeldGlobal.originW_eq_evalSeries_formalW_originParam_of_isOriginChartSection W P χ hsec hz hw]
    have : e (PowerSeries.C (originW χ)) = originW χ := by
      have := hep (Polynomial.C (originW χ))
      rwa [Polynomial.coe_C, Polynomial.eval_C] at this
    rw [this, sub_self]
  have hzdef : originParam χ = - χ (xOverY W) := rfl
  have hwdef : originW χ = - χ (zOverY W) := rfl
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro f hf
    rcases hf with rfl | rfl
    · have : -PowerSeries.X - PowerSeries.C (χ (xOverY W)) = -(PowerSeries.X - PowerSeries.C (originParam χ)) := by
        rw [hzdef, map_neg]; ring
      rw [this]
      exact Ideal.neg_mem_iff _ |>.mpr (Ideal.subset_span rfl)
    · have : -W.formalW - PowerSeries.C (χ (zOverY W)) = -(W.formalW - PowerSeries.C (originW χ)) := by
        rw [hwdef, map_neg]; ring
      rw [this]
      exact Ideal.neg_mem_iff _ |>.mpr hwz
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have : PowerSeries.X - PowerSeries.C (originParam χ) = -(-PowerSeries.X - PowerSeries.C (χ (xOverY W))) := by
      rw [hzdef, map_neg]; ring
    rw [this]
    exact Ideal.neg_mem_iff _ |>.mpr (Ideal.subset_span (Set.mem_insert _ _))

end S_WeierstrassCurve_DrinfeldGlobal_map_ker_eq_span_X_sub_C_originParam
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_map_ker_eq_span_X_sub_C_originParam (solution)
