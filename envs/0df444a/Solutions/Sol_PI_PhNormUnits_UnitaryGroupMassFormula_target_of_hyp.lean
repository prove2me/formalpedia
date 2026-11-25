-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.target_of_hyp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:04:28.032325+00:00
-- url     : https://prove2.me/submissions/d6f2336b-c8cb-4a1b-9781-37477fb6456e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open PI PI.PhNormUnits PI.PhNormUnits.UnitaryGroupMassFormula
open PI.PhNormUnits
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution (h : ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])),
    Hyp p l ex ph S → ∀ α ∈ S, NormRel p l ex ph α) : Target := by
  intro p _ l ex ph S h0 hX h2 hS2 hswap hadd hmul hint_r hadd2 htr hnm hdec hdef hunit α hα
  exact h p l ex ph S
    ⟨h0, hX, h2, hS2, hswap, hadd, hmul, hint_r, hadd2, htr, hnm, hdec, hdef, hunit⟩ α hα
end PI.PhNormUnits.UnitaryGroupMassFormula
