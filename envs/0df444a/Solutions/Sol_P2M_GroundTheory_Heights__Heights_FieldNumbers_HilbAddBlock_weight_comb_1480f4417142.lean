-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_weight_comb_1480f4417142
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:53:08.282926+00:00
-- url     : https://prove2.me/submissions/5246584a-d9e5-4f27-a82f-e382d01d41d6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbAddBlock
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.HilbAddBlock
variable {K : Type} [DecidableEq K] {ι : K → Type} {N : ℕ}
variable {F : Type u} [Field F]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.HilbAddBlock
theorem _root_.solution (d : (Σ k, ι k) →₀ ℕ) (a : Fin (N + 1) →₀ ℕ) :
    Finsupp.weight (blockWeight (addBlock ι N)) (comb d a) =
      fun o => Option.elim o (∑ j, a j) (Finsupp.weight (blockWeight ι) d) := by
  have hw : ∀ {α : Type} (f : α → (Σ o, addBlock ι N o)) (x : α →₀ ℕ),
      Finsupp.weight (blockWeight (addBlock ι N)) (Finsupp.mapDomain f x) =
        Finsupp.weight (blockWeight (addBlock ι N) ∘ f) x := by
    intro α f x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [Finsupp.mapDomain_add, map_add, map_add, hx, hy]
    | single v n => rw [Finsupp.mapDomain_single, Finsupp.weight_single, Finsupp.weight_single]; rfl
  rw [comb, map_add, hw, hw]
  ext o
  cases o with
  | none =>
    simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, blockWeight, addBlockIncl, newVar]
    exact Finset.sum_subset (Finset.subset_univ _) fun j _ hj => Finsupp.notMem_support_iff.mp hj
  | some k =>
    simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, blockWeight, Pi.single_apply,
      addBlockIncl, newVar]
end GroundTheory.Heights₂.Heights.FieldNumbers.HilbAddBlock
