-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMonomial_isMultiHomog_f53a5f857a85
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:08:22.56491+00:00
-- url     : https://prove2.me/submissions/eafb0023-58fd-4129-b9e8-1e3ba107ff6e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMChartHomog
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_pow


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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (u : ∀ k, ι k) (c : K → ℕ) :
    IsMultiHomog (chartMonomial u c : MRing ι F) c := by
  show IsWeightedHomogeneous (blockWeight ι) (∏ k, (X ⟨k, u k⟩ : MRing ι F) ^ c k) c
  have h := IsWeightedHomogeneous.prod (R := F) Finset.univ
    (fun k => (X ⟨k, u k⟩ : MRing ι F) ^ c k) (fun k => c k • blockWeight ι ⟨k, u k⟩)
    (w := blockWeight ι) (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) ⟨k, u k⟩).pow (c k))
  convert h using 1
  funext j
  simp [blockWeight, Finset.sum_apply, Pi.single_apply]
end GroundTheory.Heights₂.Heights.FieldNumbers
