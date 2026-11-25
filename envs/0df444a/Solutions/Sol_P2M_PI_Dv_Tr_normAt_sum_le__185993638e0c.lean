-- Prove2me | solution 1 for P2M_PI_Dv_Tr_normAt_sum_le__185993638e0c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:57:18.914853+00:00
-- url     : https://prove2.me/submissions/de006a09-219a-4acf-9c6b-694659cd3808

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_NormAtAddLe
import Theorems.Thm_P2M_PI_Dv_Tr_normAt_add_le__63c19bcf108d
import Theorems.Thm_P2M_PI_Dv_Tr_normAt_zero__9806172384b3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv Module NumberField
variable {K : Type} [Field K] [NumberField K] [StarRing K] {V ι : Type} [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
namespace PI.Dv.Tr
theorem _root_.solution {α : Type} (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (s : Finset α) (f : α → V) :
    Formalism.HermitianLatticesTheory.normAt b X v (∑ i ∈ s, f i) ≤ ∑ i ∈ s, Formalism.HermitianLatticesTheory.normAt b X v (f i) := by
  exact Finset.le_sum_of_subadditive (Formalism.HermitianLatticesTheory.normAt b X v) (normAt_zero' b X v).le (normAt_add_le' b X v) s f
end PI.Dv.Tr
