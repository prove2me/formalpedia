-- Prove2me | solution 1 for WeierstrassProjModel.kwYChartEval_gen_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/22ebe469-1a89-57be-ba33-56ae8eb9d9fc

import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassProjModel_kwYChartEval_gen_eq

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option linter.unusedSimpArgs false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable (R : Type u) [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal

theorem solution (m : Fin 3) :
    kwYChartEval R W (kw_lrChart_gen W 1 m) = ![(0:R), 1, 0] m := by

  rw [kwYChartEval, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
      kw_lrChart_gen_val, Localization.mk_eq_mk', IsLocalization.Away.lift,
      IsLocalization.lift_mk'_spec]

  show kwYEvalRingHom R W (mk₃ (X m : MvPolynomial (Fin 3) R))
     = kwYEvalRingHom R W (mk₃ (X 1 : MvPolynomial (Fin 3) R)) * ![(0:R),1,0] m
  rw [kwYEvalRingHom_mk_X1 R W, one_mul]

  show (MvPolynomial.eval ![(0:R),1,0]) (X m) = ![(0:R),1,0] m
  exact MvPolynomial.eval_X _

end

end S_WeierstrassProjModel_kwYChartEval_gen_eq
end P2MW
export P2MW.S_WeierstrassProjModel_kwYChartEval_gen_eq (solution)
