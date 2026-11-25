-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_FlagHeightMultilinear_hFl_sum_monomial_5ea69ff34fc7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:36:44.646848+00:00
-- url     : https://prove2.me/submissions/a81b85e4-5359-4a1b-a44d-74ae8b49f193

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsFlagGrassSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmAExpand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PHFlProdLinear

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
theorem _root_.solution (II : IntersectionSystem) {β : Type} (s : Finset β) (m : β → (Ψ × Fin N) →₀ ℕ)
    (a : β → ℚ) :
    hFl Ψ N II (∑ b ∈ s, monomial (m b) (a b)) = ∑ b ∈ s, (a b : ℝ) * hFlMono Ψ N II (m b) := by
  classical
  have hsub : ∀ (F : RootPoly Ψ N) (S : Finset ((Ψ × Fin N) →₀ ℕ)), F.support ⊆ S →
      hFl Ψ N II F = ∑ m ∈ S, ((coeff m F : ℚ) : ℝ) * hFlMono Ψ N II m := by
    intro F S hS
    unfold hFl
    exact Finset.sum_subset hS fun m _ hm => by rw [notMem_support_iff.mp hm]; simp
  have hadd : ∀ F G : RootPoly Ψ N, hFl Ψ N II (F + G) = hFl Ψ N II F + hFl Ψ N II G := by
    intro F G
    rw [hsub (F + G) (F.support ∪ G.support) support_add,
      hsub F (F.support ∪ G.support) Finset.subset_union_left,
      hsub G (F.support ∪ G.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [coeff_add]
    push_cast
    ring
  have hmono : ∀ (m : (Ψ × Fin N) →₀ ℕ) (a : ℚ), hFl Ψ N II (monomial m a) = (a : ℝ) * hFlMono Ψ N II m := by
    intro m a
    rw [hsub _ {m} support_monomial_subset, Finset.sum_singleton, coeff_monomial, if_pos rfl]
  induction s using Finset.induction_on with
  | empty => simp [hsub 0 ∅ (by simp)]
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, hadd, hmono, ih]
end GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear
