-- Prove2me | solution 1 for PI.BeDiagZp.OpsW.substOps_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:38:57.26481+00:00
-- url     : https://prove2.me/submissions/4cd958e0-802c-4bbf-8e20-661b2b70066e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOpsHolds
import Theorems.Thm_PI_BeDiagZp_OpsW_psubst_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.BeDiagZp PI.BeDiagZp.OpsW
variable {p : ℕ} [Fact p.Prime]
namespace PI.BeDiagZp.OpsW
theorem _root_.solution : SubstOps := by
  intro p _ l ex ph hex hl σ τ _ s hs0
  have hs : MvPowerSeries.HasSubst s := MvPowerSeries.hasSubst_of_constantCoeff_zero hs0
  have cc : ∀ a : MvPowerSeries σ ℂ_[p], MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.constantCoeff (MvPowerSeries.subst s a) = 0 :=
    fun a ha => MvPowerSeries.constantCoeff_subst_eq_zero hs hs0 ha
  refine ⟨fun i => MvPowerSeries.subst_X hs i, fun c a => ?_, fun a b => MvPowerSeries.subst_add hs a b,
    fun a b ha hb => ?_⟩
  · rw [MvPowerSeries.subst_mul hs, MvPowerSeries.subst_C]
  · have hla : MvPowerSeries.constantCoeff (PowerSeries.subst a l) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero ha l hl
    have hlb : MvPowerSeries.constantCoeff (PowerSeries.subst b l) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero hb l hl
    have hab : MvPowerSeries.constantCoeff (add l ex a b) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero (by rw [map_add, hla, hlb, add_zero]) ex hex
    have hadd : MvPowerSeries.subst s (add l ex a b) =
        add l ex (MvPowerSeries.subst s a) (MvPowerSeries.subst s b) := by
      unfold add
      rw [psubst_comm hs _ (by rw [map_add, hla, hlb, add_zero]) ex, MvPowerSeries.subst_add hs,
        psubst_comm hs a ha l, psubst_comm hs b hb l]
    refine ⟨cc a ha, hadd, fun c => ?_, psubst_comm hs a ha ph, ?_⟩
    · unfold mulBy
      rw [psubst_comm hs _ (by rw [map_mul, hla, mul_zero]) ex, MvPowerSeries.subst_mul hs,
        MvPowerSeries.subst_C, psubst_comm hs a ha l]
    · unfold be phAt
      rw [MvPowerSeries.subst_sub hs, MvPowerSeries.subst_sub hs, psubst_comm hs _ hab ph,
        psubst_comm hs a ha ph, psubst_comm hs b hb ph, hadd]
end PI.BeDiagZp.OpsW
