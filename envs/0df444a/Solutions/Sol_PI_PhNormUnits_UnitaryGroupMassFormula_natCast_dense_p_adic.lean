-- Prove2me | solution 1 for PI.PhNormUnits.UnitaryGroupMassFormula.natCast_dense_p_adic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:08:42.276598+00:00
-- url     : https://prove2.me/submissions/3142a2d5-fe67-44b9-8b95-f33de511975d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_Development
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerBis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_NormUnitsSubstitution
import Theorems.Thm_PI_PhNormUnits_UnitaryGroupMassFormula_PAdicPowerSeriesCoefficients_continuous_zc

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
open PAdicPowerSeriesCoefficients
namespace PI.PhNormUnits.UnitaryGroupMassFormula
theorem _root_.solution : NatDense := by
  intro p _ n
  have hn : n ∈ closure (Set.range (Nat.cast : ℕ → ℤ_[p])) := PadicInt.denseRange_natCast n
  obtain ⟨x, hx, hlim⟩ := mem_closure_iff_seq_limit.1 hn
  choose u hu using hx
  refine ⟨u, ?_⟩
  have e : (fun k => ((u k : ℕ) : ℂ_[p])) = fun k => zc (x k) := by
    funext k
    rw [← hu k]
    simp [zc]
  rw [e]
  exact (continuous_zc.tendsto n).comp hlim
end PI.PhNormUnits.UnitaryGroupMassFormula
