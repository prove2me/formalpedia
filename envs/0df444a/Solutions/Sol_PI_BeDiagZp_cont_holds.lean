-- Prove2me | solution 1 for PI.BeDiagZp.cont_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:50:22.500297+00:00
-- url     : https://prove2.me/submissions/54c58a91-06b6-4ffe-b244-83b1ed8bdb7e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_ConstantCoeffSubstEqZero
import Theorems.Thm_PI_BeDiagZp_ContPf_cc_const
import Theorems.Thm_PI_BeDiagZp_ContPf_cc_C
import Theorems.Thm_PI_BeDiagZp_ContPf_cc_add
import Theorems.Thm_PI_BeDiagZp_ContPf_cc_sub
import Theorems.Thm_PI_BeDiagZp_ContPf_cc_mul
import Theorems.Thm_PI_BeDiagZp_ContPf_cc_subst
import Theorems.Thm_PI_BeDiagZp_ContPf_cc_expMv
import Theorems.Thm_PI_BeDiagZp_ContPf_constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution
import Theorems.Thm_PI_BeDiagZp_ContPf_zc_continuous
import Theorems.Thm_PI_BeDiagZp_ContPf_zc_natCast

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
open PI PI.BeDiagZp
open ContPf
namespace PI.BeDiagZp
theorem _root_.solution : Cont := by
  intro p _ l ex ph hex hl hN n
  let u : MvPowerSeries Unit ℂ_[p] := Xv ()
  have hu : MvPowerSeries.constantCoeff u = 0 := by simp [u, Xv]
  have hlu : MvPowerSeries.constantCoeff (PowerSeries.subst u l) = 0 := constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution u hu l hl
  have hM0 : ∀ c : ℂ_[p], MvPowerSeries.constantCoeff (mulBy l ex c u) = 0 := by
    intro c
    apply constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution _ _ ex hex
    simp [hlu]
  have hM : CC fun c : ℂ_[p] => mulBy l ex c u := by
    apply cc_subst ex (fun c => by simp [hlu]) (cc_mul cc_C (cc_const _))
  have hA0 : ∀ c : ℂ_[p], MvPowerSeries.constantCoeff (add l ex u (mulBy l ex c u)) = 0 := by
    intro c
    apply constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution _ _ ex hex
    simp [hlu, constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution _ (hM0 c) l hl]
  have hA : CC fun c : ℂ_[p] => add l ex u (mulBy l ex c u) := by
    apply cc_subst ex (fun c => by simp [hlu, constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution _ (hM0 c) l hl])
    exact cc_add (cc_const _) (cc_subst l hM0 hM)
  have hB : CC fun c : ℂ_[p] => be l ex ph u (mulBy l ex c u) := by
    unfold be phAt
    exact cc_sub (cc_sub (cc_subst ph hA0 hA) (cc_const _)) (cc_subst ph hM0 hM)
  have hF : CC fun c : ℂ_[p] =>
      be l ex ph u (mulBy l ex c u) - MvPowerSeries.C c * be l ex ph u u :=
    cc_sub hB (cc_mul cc_C (cc_const _))
  have hE := cc_expMv hF
  have hcl : IsClosed {c : ℂ_[p] | Simeq (be l ex ph u (mulBy l ex c u))
      (MvPowerSeries.C c * be l ex ph u u)} := by
    simp only [Simeq, IntegralMv, IsIntP, Set.ofPred_and, Set.ofPred_forall]
    refine IsClosed.inter (isClosed_eq ?_ continuous_const)
      (isClosed_iInter fun α => isClosed_le (continuous_norm.comp (hE α)) continuous_const)
    exact (hF 0).congr fun c => MvPowerSeries.coeff_zero_eq_constantCoeff_apply _
  have hcl' := hcl.preimage zc_continuous
  refine PadicInt.denseRange_natCast.induction_on n hcl' ?_
  intro k
  show Simeq _ _
  rw [zc_natCast]
  exact hN k
end PI.BeDiagZp
