-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_finsuppProd_chartVar_6986d97a9298
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:09:25.906264+00:00
-- url     : https://prove2.me/submissions/f26637a2-3c91-49e2-b4b7-40876a3c4a74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMChartHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_chartMonomial_add_e11f6d6b4fb2

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
theorem _root_.solution (u : ∀ k, ι k) (e : (Σ k, ι k) →₀ ℕ) :
    (e.prod fun v n => (X ⟨v.1, u v.1⟩ : MRing ι F) ^ n) =
      chartMonomial u (Finsupp.weight (blockWeight ι) e) := by
  induction e using Finsupp.induction_linear with
  | zero => simp [chartMonomial]
  | add f g hf hg =>
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), hf, hg, map_add,
      chartMonomial_add]
  | single v n =>
    rw [Finsupp.prod_single_index (by simp), Finsupp.weight_single]
    simp only [chartMonomial]
    rw [Finset.prod_eq_single v.1]
    · simp [blockWeight]
    · intro k _ hk
      simp [blockWeight, hk]
    · simp
end GroundTheory.Heights₂.Heights.FieldNumbers
