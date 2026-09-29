-- Prove2me | solution 1 for WeierstrassCurve.DrinfeldGlobal.exists_sub_map_mem_maximalIdeal_pow_of_originChart_powerSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/3d5b8983-aec9-56cd-8d03-4724f8bde9b3

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_sub_map_mem_maximalIdeal_pow_of_originChart_powerSeries

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {T : Type} [CommRing T] [IsLocalRing T] (W : WeierstrassCurve T)
    (Φ : OriginChartRing W →+* PowerSeries T)
    (hΦsc : ∀ t : T, Φ (fromZeroRingHom (projModelGradingCR W) _ (algebraMap T ((projModelGradingCR W) 0) t)) =
      PowerSeries.C t)
    (hΦx : Φ (xOverY W) = - PowerSeries.X) (hΦz : Φ (zOverY W) = - W.formalW)
    (n : ℕ) (b : PowerSeries T) :
    ∃ a : OriginChartRing W, b - Φ a ∈ maximalIdeal (PowerSeries T) ^ n := by
  classical

  let sc : T →+* OriginChartRing W :=
    (fromZeroRingHom (projModelGradingCR W) _).comp (algebraMap T ((projModelGradingCR W) 0))
  let ψ : Polynomial T →+* OriginChartRing W := Polynomial.eval₂RingHom sc (-(xOverY W))
  have hΦψ : Φ.comp ψ = Polynomial.coeToPowerSeries.ringHom := by
    apply Polynomial.ringHom_ext'
    · refine RingHom.ext fun t => ?_
      simp only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C]
      rw [show ψ (Polynomial.C t) = sc t by simp [ψ]]
      exact hΦsc t
    · simp only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
      rw [show ψ Polynomial.X = -(xOverY W) by simp [ψ], map_neg, hΦx, neg_neg]
  refine ⟨ψ (PowerSeries.trunc n b), ?_⟩
  have hΦa : Φ (ψ (PowerSeries.trunc n b)) = (PowerSeries.trunc n b : PowerSeries T) := by
    rw [← RingHom.comp_apply, hΦψ, Polynomial.coeToPowerSeries.ringHom_apply]
  rw [hΦa]

  have hdvd : (PowerSeries.X : PowerSeries T) ^ n ∣ b - (PowerSeries.trunc n b : PowerSeries T) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hm, sub_self]
  obtain ⟨c, hc⟩ := hdvd
  rw [hc]
  have hX : (PowerSeries.X : PowerSeries T) ∈ maximalIdeal (PowerSeries T) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff,
      PowerSeries.constantCoeff_X]
    exact not_isUnit_zero
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hX n)

end S_WeierstrassCurve_DrinfeldGlobal_exists_sub_map_mem_maximalIdeal_pow_of_originChart_powerSeries
end P2MW
export P2MW.S_WeierstrassCurve_DrinfeldGlobal_exists_sub_map_mem_maximalIdeal_pow_of_originChart_powerSeries (solution)
