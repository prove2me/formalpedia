-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LocalGraphMass_tsum_frameFibreCount_le_2c51850231c5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:02:59.519645+00:00
-- url     : https://prove2.me/submissions/6b68b6e2-8914-4b86-9457-79a0e76da2b7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalGraphMass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Function
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LocalGraphMass
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.LocalGraphMass
theorem _root_.solution (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) {A : Set (EuclideanSpace ℂ (Fin n))} (As : ℕ → Set (EuclideanSpace ℂ (Fin n)))
    (hsub : ∀ k, As k ⊆ A) (hdisj : Pairwise (Disjoint on As)) (x : I → ℂ) :
    ∑' k, frameFibreCount b I (As k) x ≤ frameFibreCount b I A x := by
  have hfin : ∀ s : Finset ℕ,
      ∑ k ∈ s, frameFibreCount b I (As k) x = frameFibreCount b I (⋃ k ∈ s, As k) x := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [frameFibreCount]
    | insert k s hk ih =>
      rw [Finset.sum_insert hk, ih, Finset.set_biUnion_insert]
      simp only [frameFibreCount]
      rw [← ENat.toENNReal_add, ← Set.encard_union_eq]
      · congr 2
        ext z
        simp only [Set.mem_union, Set.mem_ofPred_eq]
        tauto
      · refine Set.disjoint_of_subset (Set.sep_subset _ _) (Set.sep_subset _ _) ?_
        refine Set.disjoint_iUnion₂_right.2 fun j hj => hdisj ?_
        rintro rfl
        exact hk hj
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  rw [hfin s]
  simp only [frameFibreCount]
  refine ENat.toENNReal_le.2 (Set.encard_le_encard fun z hz => ⟨?_, hz.2⟩)
  exact Set.iUnion₂_subset (fun k _ => hsub k) hz.1
end GroundTheory.Heights₂.Heights.LocalGraphMass
