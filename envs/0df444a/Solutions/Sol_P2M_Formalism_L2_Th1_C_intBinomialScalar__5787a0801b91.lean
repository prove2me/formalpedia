-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_C_intBinomialScalar__5787a0801b91
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:51:18.645839+00:00
-- url     : https://prove2.me/submissions/c86888fe-aba1-4532-8dd5-d9f2672e3c72

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffSubstBinomSeries
import Theorems.Thm_Formalism_L2_Th1_C_binom_zero
import Theorems.Thm_Formalism_L2_Th1_C_binom_pascal
import Theorems.Thm_Formalism_L2_Th1_C_binom_zero_succ

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
variable {K : Type} [Field K] [CharZero K] {σ : Type}
namespace Formalism.L2.Th1.C
theorem _root_.solution : IntBinomScalar := by
  intro K _ _ R n k
  induction k generalizing n with
  | zero => rw [binom_zero]; exact R.one_mem
  | succ k ih =>
    induction n using Int.induction_on with
    | zero => rw [Int.cast_zero, binom_zero_succ]; exact R.zero_mem
    | succ m hm =>
      have h := binom_pascal ((m : ℤ) : K) k
      have e : (((m : ℤ) + 1 : ℤ) : K) = ((m : ℤ) : K) + 1 := by push_cast; ring
      rw [e, h]
      exact R.add_mem hm (ih _)
    | pred m hm =>
      have h := binom_pascal (((-(m : ℤ) - 1 : ℤ)) : K) k
      have e : (((-(m : ℤ) - 1 : ℤ)) : K) + 1 = ((-(m : ℤ) : ℤ) : K) := by push_cast; ring
      rw [e] at h
      have h2 : binom (((-(m : ℤ) - 1 : ℤ)) : K) (k + 1) =
          binom ((-(m : ℤ) : ℤ) : K) (k + 1) - binom (((-(m : ℤ) - 1 : ℤ)) : K) k := by
        rw [h]; ring
      rw [h2]
      exact R.sub_mem hm (ih _)
end Formalism.L2.Th1.C
