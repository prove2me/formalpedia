-- Prove2me | solution 1 for WeierstrassProjModel.kw_lrSixU_addZ_ne_zero_ychartR
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/a5fbedd6-853e-5f02-8d17-7773f05ad7e9

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_isDomain_chart_of_isElliptic
import Theorems.Thm_WeierstrassProjModel_kw_lrChart_gen_ne_zero
import Theorems.Thm_WeierstrassProjModel_kw_lrSixU_addZ_ychartR_partialEval
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_kw_lrSixU_addZ_ne_zero_ychartR

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

theorem solution [IsDomain R] [IsNoetherianRing R] [W.IsElliptic] (i : Fin 3) :
    kw_lrSixU W i 1 (.inl 2) ≠ 0 := by
  haveI : IsDomain (𝒜 i) := isDomain_chart_of_isElliptic W i
  obtain ⟨φ, hφ⟩ := kw_lrSixU_addZ_ychartR_partialEval W i
  intro h
  have h0 : (kw_lrChart_gen W i 2) ^ 2 = 0 := by
    calc (kw_lrChart_gen W i 2) ^ 2 = φ (kw_lrSixU W i 1 (.inl 2)) := hφ.symm
      _ = φ 0 := by rw [h]
      _ = 0 := map_zero φ
  exact kw_lrChart_gen_ne_zero W i 2 (pow_eq_zero_iff (two_ne_zero) |>.mp h0)

end

end S_WeierstrassProjModel_kw_lrSixU_addZ_ne_zero_ychartR
end P2MW
export P2MW.S_WeierstrassProjModel_kw_lrSixU_addZ_ne_zero_ychartR (solution)
