-- Prove2me | solution 1 for P2M_GlobalTheory_DiscUniformisation____ne_zero_6e8e510ab80d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:35.144809+00:00
-- url     : https://prove2.me/submissions/eec98936-a6d8-47f0-88f9-eddeb5bf2f69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TendstoCoeffZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm MatrixGroups EisensteinSeries Filter Topology
open GlobalTheory GlobalTheory.DiscUniformisation
namespace GlobalTheory.DiscUniformisation
theorem _root_.solution (L : PeriodPair) : L.ω₂ ≠ 0 := by
  simpa using L.indep.ne_zero 1
end GlobalTheory.DiscUniformisation
