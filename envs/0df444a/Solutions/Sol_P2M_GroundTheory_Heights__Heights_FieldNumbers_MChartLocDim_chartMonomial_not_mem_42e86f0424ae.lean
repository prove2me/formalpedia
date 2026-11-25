-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartLocDim_chartMonomial_not_mem_42e86f0424ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:57:30.847423+00:00
-- url     : https://prove2.me/submissions/7e4c02c2-122a-4b99-a421-ffb3b24f8128

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMChartLocDim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.MChartLocDim
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.MChartLocDim
theorem _root_.solution (Q : Ideal (MRing ι F)) [Q.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ Q) (b : K → ℕ) : chartMonomial u b ∉ Q := by
  unfold chartMonomial
  rw [Ideal.IsPrime.prod_mem_iff]
  rintro ⟨k, -, hk⟩
  exact hu k (Ideal.IsPrime.mem_of_pow_mem inferInstance _ hk)
end GroundTheory.Heights₂.Heights.FieldNumbers.MChartLocDim
