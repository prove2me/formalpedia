-- Prove2me | solution 1 for PI.LPI.plInj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:03:16.100046+00:00
-- url     : https://prove2.me/submissions/92b3c74f-60e6-482f-97f3-2149fa5ec839

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_PrVTmulEqTmulApply
import Theorems.Thm_PI_LPI_coord_prV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct
noncomputable section
open PI PI.LPI
namespace PI.LPI
theorem _root_.solution : PLInj := by
  intro F E _ _ _ _ _ z hz
  let b := Module.finBasis F E
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  rw [map_zero]
  refine Finsupp.ext fun i => FiniteAdeleRing.ext F fun v => ?_
  rw [← coord_prV b v z i, hz v, map_zero]
  rfl
end PI.LPI
