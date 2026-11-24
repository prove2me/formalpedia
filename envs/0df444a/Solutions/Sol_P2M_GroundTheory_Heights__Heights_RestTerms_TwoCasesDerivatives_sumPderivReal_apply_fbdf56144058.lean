-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_TwoCasesDerivatives_sumPderivReal_apply_fbdf56144058
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:11.725256+00:00
-- url     : https://prove2.me/submissions/f4dda15e-9254-4964-b637-c331b6fc787a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_SumPderivRealApply
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_C_43a59c7a9997
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_X_6be993a34174
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_C_43a59c7a9997
attribute [local simp] P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_X_6be993a34174



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.TwoCasesDerivatives
open MvPolynomial Finset
noncomputable section
variable (f j k : ℕ)
namespace GroundTheory.Heights₂.Heights.RestTerms.TwoCasesDerivatives
theorem _root_.solution {ι : Type*} (τ : Fin f) (s : Finset ι) (g : ι → Fin (j + k))
    (P : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    sumPderivReal f j k τ s g P = ∑ l ∈ s, pderiv (τ, g l) P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sumPderivReal]
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, ← ih]
    simp [sumPderivReal, Finset.sum_insert hb]
end GroundTheory.Heights₂.Heights.RestTerms.TwoCasesDerivatives
