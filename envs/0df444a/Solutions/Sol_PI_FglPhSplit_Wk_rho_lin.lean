-- Prove2me | solution 1 for PI.FglPhSplit.Wk.rho_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:46:37.265786+00:00
-- url     : https://prove2.me/submissions/02f8db2a-4973-4fe3-932d-9c8042f34539

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_AddPreservesExpCongruence
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Theorems.Thm_PI_FglPhSplit_Wk_rho_psubst
import Theorems.Thm_PI_FglPhSplit_Wk_rho_C
import Theorems.Thm_PI_FglPhSplit_Wk_cc_psubst

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
theorem _root_.solution {κ' : Type} [Fintype κ'] (c : κ' → K) (w : κ' → MvPowerSeries (ι ⊕ ι) K)
    (hw : ∀ j, MvPowerSeries.constantCoeff (w j) = 0) :
    rho (ι' := ι') (g.lin c w) = g.lin c (fun j => rho (w j)) := by
  unfold Dat.lin Dat.pt Dat.lg
  have hs : ∀ (σ : Type) (v : κ' → MvPowerSeries σ K), (∀ j, MvPowerSeries.constantCoeff (v j) = 0) →
      MvPowerSeries.constantCoeff (∑ j, MvPowerSeries.C (c j) * PowerSeries.subst (v j) g.l) = 0 := by
    intro σ v hv
    rw [map_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [map_mul, cc_psubst _ hl0 (hv j), mul_zero]
  have e : rho (ι' := ι') (∑ j, MvPowerSeries.C (c j) * PowerSeries.subst (w j) g.l) =
      ∑ j, MvPowerSeries.C (c j) * PowerSeries.subst (rho (ι' := ι') (w j)) g.l := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul, rho_C, rho_psubst _ (hw j)]
  rw [rho_psubst _ (hs _ w hw), e]
end PI.FglPhSplit.Wk
