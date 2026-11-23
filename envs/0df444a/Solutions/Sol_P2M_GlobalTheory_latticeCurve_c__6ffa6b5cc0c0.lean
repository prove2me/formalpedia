-- Prove2me | solution 1 for P2M_GlobalTheory_latticeCurve_c__6ffa6b5cc0c0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:03.626699+00:00
-- url     : https://prove2.me/submissions/d8233761-b7a6-4efc-b6ea-7a54f5e6dae5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm MatrixGroups Filter EisensteinSeries
open scoped Real Topology
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (L : PeriodPair) : (latticeCurve L).c₄ = 12 * L.g₂ := by
  simp only [latticeCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring
end GlobalTheory
