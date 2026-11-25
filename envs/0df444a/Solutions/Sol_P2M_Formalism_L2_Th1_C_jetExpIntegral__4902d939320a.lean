-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_C_jetExpIntegral__4902d939320a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:51:21.957044+00:00
-- url     : https://prove2.me/submissions/38c6a1e0-e2b8-4d6c-9d3c-9a531c3a0e1a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_JetExpShape
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_IntPSDerivativeOfLG
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_intPS_derivative
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_intPS_Dinv
import Theorems.Thm_Formalism_L2_Th1_C_JetSubstitutionLemmas_intPS_derivative_of_LG

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
theorem _root_.solution : JetLG := by
  intro K _ _ R l f hl hf i hi
  have h1 : IntPS R (Dinv l f) := intPS_Dinv hl (intPS_derivative_of_LG hf)
  have h2 : ∀ n : ℕ, IntPS R ((Dinv l)^[n] (Dinv l f)) := by
    intro n
    induction n with
    | zero => exact h1
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact intPS_Dinv hl (intPS_derivative ih)
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  unfold jet
  rw [Function.iterate_succ_apply]
  have := h2 n 0
  rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
end Formalism.L2.Th1.C
