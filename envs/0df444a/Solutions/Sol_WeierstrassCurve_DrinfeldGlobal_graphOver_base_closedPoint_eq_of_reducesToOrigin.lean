-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.graphOver_base_closedPoint_eq_of_reducesToOrigin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/2d847fc1-24b9-518f-8b33-bbf753d45f7a

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_ringHom_originChartRing_ext
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_graphOver_base_closedPoint_eq_of_reducesToOrigin

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {T : Type} [CommRing T] [IsLocalRing T] [IsAdicComplete (maximalIdeal T) T] (W : WeierstrassCurve T)
    (s : Section W) (χ : OriginChartRing W →+* T) (hs : ReducesToOrigin s χ (maximalIdeal T))
    (Φ : OriginChartRing W →+* PowerSeries T)
    (hΦsc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY W) = - PowerSeries.X) (hΦz : Φ (zOverY W) = - W.formalW) :
    (graphOver (projModelStrCR W) s.1 s.2).base (IsLocalRing.closedPoint T) =
      (originChartι W ≫ toPullbackId).base
        (⟨Ideal.comap Φ (maximalIdeal (PowerSeries T)), inferInstance⟩ : PrimeSpectrum (OriginChartRing W)) := by
  classical
  obtain ⟨hsec, hz, hw⟩ := hs

  have hgraph : graphOver (projModelStrCR W) s.1 s.2 = s.1 ≫ toPullbackId := by
    apply pullback.hom_ext
    · rw [graphOver_fst, Category.assoc, toPullbackId, pullback.lift_fst, Category.comp_id]
    · rw [graphOver_snd, Category.assoc, toPullbackId, pullback.lift_snd]; exact s.2.symm

  have hsc : ∀ t : T, χ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) = t := by
    have h2 := s.2
    rw [hsec, projModelStrCR, Category.assoc] at h2
    change Spec.map (CommRingCat.ofHom χ) ≫ (Proj.awayι (projModelGradingCR W) (coord W 1) (coord_mem W 1) one_pos ≫
      Proj.toSpecZero (projModelGradingCR W)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap T ((projModelGradingCR W) 0))) = 𝟙 _ at h2
    rw [Proj.awayι_toSpecZero, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_id, Spec.map_inj] at h2
    intro t
    have := congrArg (fun φ : CommRingCat.of T ⟶ CommRingCat.of T => φ.hom t) h2
    simpa using this

  have hΦmax : ∀ f : OriginChartRing W, f ∈ Ideal.comap Φ (maximalIdeal (PowerSeries T)) ↔
      IsLocalRing.residue T (PowerSeries.constantCoeff (Φ f)) = 0 := by
    intro f
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff,
      ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, ← IsLocalRing.ker_residue, RingHom.mem_ker]
  have hχmax : ∀ f : OriginChartRing W, f ∈ Ideal.comap χ (maximalIdeal T) ↔
      IsLocalRing.residue T (χ f) = 0 := by
    intro f
    rw [Ideal.mem_comap, ← IsLocalRing.ker_residue, RingHom.mem_ker]
  have hρ : (IsLocalRing.residue T).comp χ =
      ((IsLocalRing.residue T).comp (PowerSeries.constantCoeff (R := T))).comp Φ := by
    apply WeierstrassCurve.DrinfeldGlobal.ringHom_originChartRing_ext W
    · intro t
      simp only [RingHom.comp_apply]
      rw [hsc, hΦsc, PowerSeries.constantCoeff_C]
    · simp only [RingHom.comp_apply]
      rw [hΦx, map_neg, PowerSeries.constantCoeff_X, neg_zero, map_zero]
      have : χ (xOverY W) = - originParam χ := by rw [originParam, neg_neg]
      rw [this, map_neg, (IsLocalRing.residue_eq_zero_iff _).mpr hz, neg_zero]
    · simp only [RingHom.comp_apply]
      rw [hΦz, map_neg, WeierstrassCurve.constantCoeff_formalW, neg_zero, map_zero]
      have : χ (zOverY W) = - originW χ := by rw [originW, neg_neg]
      rw [this, map_neg, (IsLocalRing.residue_eq_zero_iff _).mpr hw, neg_zero]
  have hprime : Ideal.comap χ (maximalIdeal T) = Ideal.comap Φ (maximalIdeal (PowerSeries T)) := by
    ext f
    rw [hχmax, hΦmax, ← RingHom.comp_apply, hρ]
    rfl

  rw [hgraph, hsec, Category.assoc, Scheme.Hom.comp_base, TopCat.comp_app]
  congr 1
  apply PrimeSpectrum.ext
  change Ideal.comap χ (IsLocalRing.closedPoint T).asIdeal = _
  rw [IsLocalRing.closedPoint]
  exact hprime

end S_WeierstrassCurve_DrinfeldGlobal_graphOver_base_closedPoint_eq_of_reducesToOrigin
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_graphOver_base_closedPoint_eq_of_reducesToOrigin (solution)
