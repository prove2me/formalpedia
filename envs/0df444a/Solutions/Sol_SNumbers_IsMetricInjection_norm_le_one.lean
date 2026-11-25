-- Prove2me | solution 1 for SNumbers.IsMetricInjection.norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:57:52.34878+00:00
-- url     : https://prove2.me/submissions/dc61402c-e35d-4c9b-83f9-0ed3277f3a74

module
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_Injectivity

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
namespace SNumbers
namespace IsMetricInjection
theorem _root_.solution {J : Y →L[𝕜] Z} (hJ : IsMetricInjection J) :
    ‖J‖ ≤ 1 :=
  J.opNorm_le_bound zero_le_one fun y => by rw [hJ y, one_mul]
end IsMetricInjection
end SNumbers
