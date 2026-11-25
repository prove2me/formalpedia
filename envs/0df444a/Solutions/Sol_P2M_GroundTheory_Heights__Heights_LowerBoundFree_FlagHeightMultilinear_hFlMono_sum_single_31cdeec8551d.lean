-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_hFlMono_sum_single_31cdeec8551d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:09:33.285614+00:00
-- url     : https://prove2.me/submissions/6f4f1a8a-00c8-4651-b9de-575cf6fbbba6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsFlagGrassSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmAExpand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PHFlProdLinear
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_exists_perm_toList_5fa71000ffc8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear
variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear
theorem _root_.solution (II : IntersectionSystem) (hII : IsIntersectionSystem II)
    (hP : IsArithVar (PFl Ψ N) (dimFl Ψ N + 1)) (r : Fin (dimFl Ψ N + 1) → Ψ × Fin N) :
    hFlMono Ψ N II (∑ i, Finsupp.single (r i) 1) =
      II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (dimFl Ψ N + 1) (fun i => xLine Ψ N (r i)) := by
  have hdeg : (∑ i, Finsupp.single (r i) (1 : ℕ)).degree = dimFl Ψ N + 1 := by
    rw [map_sum]
    simp [Finsupp.degree_single]
  have hm : Finsupp.toMultiset (∑ i, Finsupp.single (r i) (1 : ℕ)) = Multiset.map r Finset.univ.val := by
    rw [Finsupp.toMultiset_sum]
    simp only [Finsupp.toMultiset_single, one_smul]
    rw [Finset.sum_eq_multiset_sum]
    have e : (fun i => ({r i} : Multiset (Ψ × Fin N))) = (fun p => {p}) ∘ r := rfl
    rw [e, ← Multiset.map_map, Multiset.sum_map_singleton]
  obtain ⟨σ, hσ⟩ := exists_perm_toList r
  have hML : monoLines Ψ N (∑ i, Finsupp.single (r i) 1) (dimFl Ψ N + 1) = (fun i => xLine Ψ N (r i)) ∘ σ := by
    funext k
    have hk : (k : ℕ) < (Multiset.map r Finset.univ.val).toList.length := by
      have := k.2
      simp [Multiset.length_toList]
      omega
    unfold monoLines
    rw [hm, dif_pos hk, hσ k hk]
    rfl
  unfold hFlMono
  rw [if_pos hdeg, hML]
  exact (hII (FlBlock Ψ N) (FlIdx Ψ N)).1 _ _ _ σ hP fun j => isSmoothHerm_fsHerm _
end GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear
