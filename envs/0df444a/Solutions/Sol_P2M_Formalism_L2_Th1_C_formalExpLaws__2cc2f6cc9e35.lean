-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_C_formalExpLaws__2cc2f6cc9e35
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:51:18.121814+00:00
-- url     : https://prove2.me/submissions/4e0df63a-4a61-4608-8307-9eae977434a4

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Theorems.Thm_Formalism_L2_Th1_C_mvExp_zero
import Theorems.Thm_Formalism_L2_Th1_C_constantCoeff_mvExp
import Theorems.Thm_Formalism_L2_Th1_C_mvExp_add
import Theorems.Thm_Formalism_L2_Th1_C_mvExp_inj

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
theorem _root_.solution : MvExpLaws := by
  intro K _ _ σ
  exact ⟨mvExp_zero, fun f hf => constantCoeff_mvExp hf, fun f g hf hg => mvExp_add hf hg,
    fun f g hf hg h => mvExp_inj hf hg h⟩
end Formalism.L2.Th1.C
