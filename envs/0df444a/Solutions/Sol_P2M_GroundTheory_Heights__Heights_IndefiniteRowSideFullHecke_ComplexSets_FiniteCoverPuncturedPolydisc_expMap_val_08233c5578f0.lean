-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteCoverPuncturedPolydisc_expMap_val_08233c5578f0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:10.757189+00:00
-- url     : https://prove2.me/submissions/62818de4-9134-4539-bd03-3a36bf1bdad4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteCoverPuncturedPolydisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteCoverPuncturedPolydisc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Filter Topology Complex
open scoped Real
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteCoverPuncturedPolydisc
variable {e : ℕ}
variable {c : Fin (e + 1) → ℂ} {r : ℝ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteCoverPuncturedPolydisc
theorem _root_.solution (hc : c 0 = 0) {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) (u : strip c ρ) :
    ((expMap hc hρ hρr u : _) : Fin (e + 1) → ℂ) = Function.update u.1 0 (exp (u.1 0)) := rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteCoverPuncturedPolydisc
