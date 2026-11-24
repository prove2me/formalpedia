-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_C_jetAdjoint__bce2b7401698
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:48:23.621234+00:00
-- url     : https://prove2.me/submissions/7d87e8a3-f0df-493f-a3a5-ff8ea009f2ff

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntPSDerivativeOfLG
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_cc_derivative_log
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_jet_eq_cc
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_cc_pderiv_Q
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_addDefect_eq
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_fmul_one
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_pderiv
import Theorems.Thm_P2M_Formalism_L2_Th1_C_expIntegralDeriv__70ca0e7dcf2b


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open JetSubstitutionLemmas
namespace Formalism.L2.Th1.C
theorem _root_.solution : JetAdj := by
  intro K _ _ R l linv ph a b h hph hA
  have hX : ∀ j : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X j : MvPowerSeries (Fin 2) K) = 0 :=
    fun j => MvPowerSeries.constantCoeff_X j
  have hXpt : ∀ j : Fin 2, IsPt R (MvPowerSeries.X j : MvPowerSeries (Fin 2) K) := by
    intro j
    refine ⟨hX j, fun n => ?_⟩
    rw [MvPowerSeries.coeff_X]
    split_ifs
    · exact one_mem R
    · exact zero_mem R
  have hC := hA (Fin 2) (MvPowerSeries.X 0) (MvPowerSeries.X 1) (hXpt 0) (hXpt 1)
  have hI := IntegralMvPolynomialLemmas.intMv_pderiv (expIntegralDeriv' K R (Fin 2) _ hC 1) 0 0
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at hI
  have e1 := addDefect_eq h ph a 1
  rw [fmul_one h (hX 1)] at e1
  have e2 := addDefect_eq h ph 1 b
  rw [fmul_one h (hX 0)] at e2
  have hl1 := cc_derivative_log h
  rw [e1, e2] at hI
  simp only [map_sub, cc_pderiv_Q h.1 hl1] at hI
  have hj : jet l ph 2 = PowerSeries.constantCoeff
      (PowerSeries.derivative K (PowerSeries.derivative K (PowerSeries.subst linv ph))) := by
    rw [jet_eq_cc h]
    rfl
  rw [hj]
  convert hI using 1
  ring
end Formalism.L2.Th1.C
