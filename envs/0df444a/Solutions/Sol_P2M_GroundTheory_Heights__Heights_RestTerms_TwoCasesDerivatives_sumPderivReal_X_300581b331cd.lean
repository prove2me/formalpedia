-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_TwoCasesDerivatives_sumPderivReal_X_300581b331cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:13:08.501803+00:00
-- url     : https://prove2.me/submissions/51377585-0f07-41b2-a65b-10d8b0da4fc7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_SumPderivRealApply
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_TwoCasesDerivatives_sumPderivReal_apply_fbdf56144058
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
    (σ : Fin f) (i : Fin (j + k)) :
    sumPderivReal f j k τ s g (X (σ, i)) =
      ∑ l ∈ s, if σ = τ ∧ i = g l then (1 : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) else 0 := by
  classical
  rw [sumPderivReal_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [pderiv_X, Pi.single_apply]
  simp only [Prod.mk.injEq]
end GroundTheory.Heights₂.Heights.RestTerms.TwoCasesDerivatives
