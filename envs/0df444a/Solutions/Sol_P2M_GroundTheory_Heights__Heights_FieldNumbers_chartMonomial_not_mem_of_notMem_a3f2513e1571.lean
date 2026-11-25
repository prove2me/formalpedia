-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMonomial_not_mem_of_notMem_a3f2513e1571
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:08:28.217809+00:00
-- url     : https://prove2.me/submissions/ba633045-57af-4b96-bfa1-8edf63f9e88b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsNoetherIntegralClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_LocalIntegralClosureChart

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
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (W : Ideal (MRing ι F)) [W.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ W) (b : K → ℕ) : chartMonomial u b ∉ W :=
  (Submonoid.prod_mem _ fun k _ => Submonoid.pow_mem _ (hu k) _ : chartMonomial u b ∈ W.primeCompl)
end GroundTheory.Heights₂.Heights.FieldNumbers
