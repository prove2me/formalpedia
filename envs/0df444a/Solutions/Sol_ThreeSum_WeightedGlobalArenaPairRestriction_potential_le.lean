-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPairRestriction.potential_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:08:25.8272+00:00
-- url     : https://prove2.me/submissions/26b7b4ec-513a-4246-8445-f1913979e62b

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceSetup
import Definitions.Def_Submission_Weighted_Global_TernaryNativeTensorScore
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairRestriction
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPairRestriction_embed_injective

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPairRestriction
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaSourceSetup
open WeightedGlobalNativePairMoments WeightedGlobalNativeTensorScore
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
variable {p m F r : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : WeightedGlobalGoodOutputCatalog.Output m)
    (I : Input) (nB nC : ℕ) (fB fC : ℕ→ℕ)
    (hB : ∀ i<nB, fB i<I.nB) (hC : ∀ i<nC, fC i<I.nC)
include hB hC
namespace ThreeSum.WeightedGlobalArenaPairRestriction
theorem _root_.solution (K J : ℕ) (L R : ℕ→ℕ→ℤ)
    (hfB : ∀ a<nB, ∀ b<nB, fB a=fB b→a=b)
    (hfC : ∀ a<nC, ∀ b<nC, fC a=fC b→a=b) :
    pairedPotential (small (r := r) maps τ cap Q I nB nC fB fC) K J
      (fun i => L (fB i)) (fun i => R (fC i))≤
      pairedPotential (full (r := r) maps τ cap Q I) K J L R := by
  unfold pairedPotential
  apply sum_le_sum
  intro i hi
  let e := embed (r := r) maps τ cap Q I nB nC fB fC hB hC (i := i.val)
  let lift := fun x : Fin K→Pair (small (r := r) maps τ cap Q I nB nC fB fC) i.val => fun k => e (x k)
  have hinj : Function.Injective lift := by
    intro a b hab
    funext k
    exact embed_injective (r := r) maps τ cap Q I nB nC fB fC hB hC hfB hfC i.val (congrFun hab k)
  let weight := fun x : Fin K→Pair (full (r := r) maps τ cap Q I) i.val =>
    TernaryPairedPotential.rowWeight (Sum.elim
      (fun k => originalLeft (full (r := r) maps τ cap Q I) J L i.val (x k))
      (fun k => originalRight (full (r := r) maps τ cap Q I) J R i.val (x k)))
  change (∑ x, weight (lift x))≤∑ x, weight x
  calc
    _ = ∑ x∈(univ : Finset (Fin K→Pair (small (r := r) maps τ cap Q I nB nC fB fC) i.val)).image lift, weight x := by
      rw [sum_image]
      exact fun a ha b hb h => hinj h
    _ ≤ _ := sum_le_sum_of_subset (subset_univ _)
end ThreeSum.WeightedGlobalArenaPairRestriction
