-- Prove2me | solution 1 for PI.FglChordFactor.Wk.flog_iW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:15:19.983377+00:00
-- url     : https://prove2.me/submissions/3185484d-d20a-4158-9885-faa2162d4f42

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglChordFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DXEqDerivative
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DvCoeffMulEqZeroOfLtOrder
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_NormDeltaWc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_SubstPairSecondVariable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupChords_DerivativeFlog
import Theorems.Thm_P2M_PI_FglChordFactor_Wk_wq_const__1de777e7fcd2
import Theorems.Thm_PI_FglChordFactor_Wk_D_const
import Theorems.Thm_PI_FglChordFactor_Wk_iW_mul_D
import Theorems.Thm_PI_FglChordFactor_Wk_iW_const
import Theorems.Thm_PI_FglChordFactor_Wk_hasSubst_iW
import Theorems.Thm_PI_FglChordFactor_Wk_wq_iW
import Theorems.Thm_P2M_PI_FglChordFactor_Wk_derivative_flog__91738686ceb7
import Theorems.Thm_PI_FglChordFactor_Wk_flog_const
import Theorems.Thm_PI_FglChordFactor_Wk_omega_mul
import Theorems.Thm_PI_FglChordFactor_Wk_deriv_ext
import Theorems.Thm_PI_AddIntG_Wk_inv_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_pderiv_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Classical
namespace PI.FglChordFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS inv_mem_SerS)
variable {p : ℕ} [Fact p.Prime]
private theorem derivative_subst_eq_subst_derivative_mul (a f : PowerSeries ℂ_[p]) (ha : PowerSeries.HasSubst a) :
    PowerSeries.derivative ℂ_[p] (PowerSeries.subst a f) =
      PowerSeries.subst a (PowerSeries.derivative ℂ_[p] f) * PowerSeries.derivative ℂ_[p] a := by
  have hpd : ∀ g : PowerSeries ℂ_[p], MvPowerSeries.pderiv ℂ_[p] () g = PowerSeries.derivative ℂ_[p] g := by
    intro g
    refine PowerSeries.ext fun n => ?_
    rw [PowerSeries.coeff_derivative]
    show MvPowerSeries.coeff (Finsupp.single () n) (MvPowerSeries.pderiv ℂ_[p] () g) = _
    rw [MvPowerSeries.coeff_pderiv, ← Finsupp.single_add, Finsupp.single_eq_same]
    rfl
  have := PI.AddIntG.Wk.pderiv_subst (σ := Unit) ha f ()
  rw [hpd, hpd] at this
  exact this
end PI.FglChordFactor.Wk
end
end

set_option autoImplicit false
noncomputable section
open Classical
open PI PI.FglChordFactor PI.FglChordFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS inv_mem_SerS)
variable {p : ℕ} [Fact p.Prime]
namespace PI.FglChordFactor.Wk
theorem _root_.solution {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    PowerSeries.subst (iW W wq) (flog W wq) = -flog W wq := by
  have hs := hasSubst_iW W wq
  have hφ : ∀ f : PowerSeries ℂ_[p], PowerSeries.subst (iW W wq) f = PowerSeries.substAlgHom hs f := fun f => by
    rw [PowerSeries.coe_substAlgHom]
  have hX : PowerSeries.substAlgHom hs (PowerSeries.X : PowerSeries ℂ_[p]) = iW W wq := by
    rw [← hφ, PowerSeries.subst_X hs]
  apply deriv_ext
  · have hwi := wq_iW h
    have e := iW_mul_D W wq
    have hD0 : Dser W wq = 1 - (cP W.a₁ * PowerSeries.X + cP W.a₃ * PowerSeries.X ^ 3 * wq) := rfl
    have hom := omega_mul h
    have hom' := congrArg (PowerSeries.substAlgHom hs) hom
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, AlgHom.commutes, hX] at hom'
    simp only [← hφ] at hom'
    rw [hwi] at hom'
    have hcw := derivative_subst_eq_subst_derivative_mul (iW W wq) wq hs
    rw [hwi] at hcw
    have hdwD : PowerSeries.derivative ℂ_[p] (wq * Dser W wq ^ 2) =
        PowerSeries.derivative ℂ_[p] wq * Dser W wq ^ 2 +
          wq * (2 * Dser W wq * PowerSeries.derivative ℂ_[p] (Dser W wq)) := by
      rw [pow_two, Derivation.leibniz, Derivation.leibniz]
      simp only [smul_eq_mul]
      ring
    have e2 := congrArg (PowerSeries.derivative ℂ_[p]) e
    rw [Derivation.leibniz, map_neg, PowerSeries.derivative_X] at e2
    simp only [smul_eq_mul] at e2
    have hDM : Dser W wq * (wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X +
        algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq - 2)) ≠ 0 := by
      intro h0
      have h00 := congrArg PowerSeries.constantCoeff h0
      have h2 : PowerSeries.constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := map_ofNat _ 2
      simp [D_const, wq_const' h, h2] at h00
    rw [derivative_subst_eq_subst_derivative_mul (iW W wq) (flog W wq) hs, derivative_flog', map_neg, derivative_flog']
    have key : (PowerSeries.subst (iW W wq) (omegaW W wq) * PowerSeries.derivative ℂ_[p] (iW W wq) +
        omegaW W wq) * (Dser W wq * (wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X +
        algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq - 2))) = 0 := by
      linear_combination Dser W wq * hom + PowerSeries.derivative ℂ_[p] (iW W wq) * hom'
        - PowerSeries.derivative ℂ_[p] (iW W wq) * PowerSeries.subst (iW W wq) (omegaW W wq) * wq *
          Dser W wq * (cP W.a₁ + cP W.a₃ * wq * ((iW W wq * Dser W wq) ^ 2 -
            iW W wq * Dser W wq * PowerSeries.X + PowerSeries.X ^ 2)) * e
        - PowerSeries.derivative ℂ_[p] wq * Dser W wq * e
        + 2 * PowerSeries.derivative ℂ_[p] (iW W wq) * PowerSeries.subst (iW W wq) (omegaW W wq) * wq *
          Dser W wq * hD0
        - 2 * wq * Dser W wq * e2 + iW W wq * (hcw - hdwD)
    have h3 := (mul_eq_zero.1 key).resolve_right hDM
    linear_combination h3
  · obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.2 (flog_const W wq)
    rw [map_neg, flog_const, neg_zero, hg, hφ, map_mul, hX, map_mul, iW_const, zero_mul]
end PI.FglChordFactor.Wk
