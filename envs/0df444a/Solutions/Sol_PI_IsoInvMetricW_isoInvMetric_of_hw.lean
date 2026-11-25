-- Prove2me | solution 1 for PI.IsoInvMetricW.isoInvMetric_of_hw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:16:07.121291+00:00
-- url     : https://prove2.me/submissions/54494698-7b18-4b36-846d-c5be8b1fa625

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_SymmetricMeasureL2NormEqResolutionL2
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_HvScalar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_QuotientRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_HermitianVectorMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_IsoInvMetricOfHw
import Theorems.Thm_P2M_PI_IsoInvMetricW_norm1__aba47395eaf4
import Theorems.Thm_PI_IsoInvMetricW_gen_of
import Theorems.Thm_PI_IsoInvMetricW_hermitian_vector_map
import Theorems.Thm_PI_IsoInvMetricW_hvCols_of
import Theorems.Thm_PI_IsoInvMetricW_invK_of
import Theorems.Thm_PI_IsoInvMetricW_isoInvMetric_of
import Theorems.Thm_PI_IsoInvMetricW_metric_mul
import Theorems.Thm_PI_IsoInvMetricW_quotient_rank
import Theorems.Thm_PI_IsoInvMetricW_stab_of
import Theorems.Thm_PI_IsoInvMetricW_unit_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.IsoInvMetricW
namespace PI.IsoInvMetricW
theorem _root_.solution (hW : HW) : PI.IsoInvMetric.IsoInvMetric :=
  isoInvMetric_of (unit_of metric_mul) (invK_of metric_mul) (stab_of hermitian_vector_map)
    (hvCols_of hermitian_vector_map) norm1' (gen_of quotient_rank hermitian_vector_map) hW
end PI.IsoInvMetricW
