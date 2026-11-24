-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockData_chartPow_ne_zero_0ca6bf248649
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:49.051742+00:00
-- url     : https://prove2.me/submissions/eb996a33-e2a6-4876-88af-deb561ba6241

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ChartPowNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.AddBlockData
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n} (D : AddBlockData P)
namespace GroundTheory.Heights₂.Heights.AddBlockData
theorem _root_.solution {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (a : ι → ℤ) :
    P.chartPow c a ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ fun h ↦ hc k ((P.mkF_eq_zero_iff _).mp h)
end GroundTheory.Heights₂.Heights.AddBlockData
