-- Prove2me | solution 1 for PI.FglPhSplit.Wk.rho_PhOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:00:29.742816+00:00
-- url     : https://prove2.me/submissions/d4a72f50-56e3-411b-90bf-721f6a5041e3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_AddPreservesExpCongruence
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Theorems.Thm_PI_FglPhSplit_Wk_rho_psubst
import Theorems.Thm_PI_FglPhSplit_Wk_rho_X
import Theorems.Thm_PI_FglPhSplit_Wk_cc_psubst
import Theorems.Thm_PI_FglPhSplit_Wk_rho_lin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglPhSplit PI.FglPhSplit.Wk
open PI.FglPhSplit
variable {K : Type} [Field K]
variable {ι ι' : Type} [Fintype ι]
variable (g : Dat K) (hex0 : PowerSeries.constantCoeff g.ex = 0)
  (hl0 : PowerSeries.constantCoeff g.l = 0)
include hex0 hl0
namespace PI.FglPhSplit.Wk
theorem _root_.solution {κ : Type} [Fintype κ] (b : ι ⊕ ι → κ → K × K) :
    rho (ι' := ι') (g.PhOn b) = g.PhV b (fun e => MvPowerSeries.X (Sum.inl e)) := by
  unfold Dat.PhOn Dat.PhV
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hX : ∀ e : ι ⊕ ι, MvPowerSeries.constantCoeff (MvPowerSeries.X e : MvPowerSeries (ι ⊕ ι) K) = 0 :=
    fun e => MvPowerSeries.constantCoeff_X e
  have hlin : MvPowerSeries.constantCoeff
      (g.lin (fun e => (b e k).1) (fun e => (MvPowerSeries.X e : MvPowerSeries (ι ⊕ ι) K))) = 0 := by
    unfold Dat.lin Dat.pt Dat.lg
    refine cc_psubst _ hex0 ?_
    rw [map_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [map_mul, cc_psubst _ hl0 (hX j), mul_zero]
  unfold Dat.phAt
  rw [rho_psubst _ hlin, rho_lin g hex0 hl0 _ _ hX]
  simp only [rho_X]
end PI.FglPhSplit.Wk
