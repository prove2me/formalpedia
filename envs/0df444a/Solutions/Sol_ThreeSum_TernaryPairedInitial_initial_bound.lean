-- Prove2me | solution 1 for ThreeSum.TernaryPairedInitial.initial_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:24:33.175911+00:00
-- url     : https://prove2.me/submissions/8c261550-4461-4776-b648-1c22b38f1269

import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Definitions.Def_Submission_ThreeSum_TernaryPairedInitial
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_mapEdge_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_output_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_reindex_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_swapEdge_swapEdge
import Theorems.Thm_ThreeSum_TernaryPairedPotential_minorWeight_le
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.mapEdge_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.output_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.reindex_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.swapEdge_swapEdge



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedInitial
open Finset Matrix TernaryPairedPotential
open scoped BigOperators
namespace ThreeSum.TernaryPairedInitial
theorem _root_.solution {P G : Type*} [Fintype P] [Fintype G]
    (K Λ b : ℕ) (A : G → (Fin K → P) → Matrix (Fin (2*K)) (Fin Λ) ℤ)
    (hA : ∀ g e i j, (A g e i j).natAbs≤b) :
    (∑ g : G, ∑ e : Fin K → P, minorWeight (A g e)) ≤
      Fintype.card G*Fintype.card P^K*Λ^(2*K)*((2*K).factorial*b^(2*K))^2 := by
  calc
    _ ≤ ∑ _g : G, ∑ _e : Fin K → P, Λ^(2*K)*((2*K).factorial*b^(2*K))^2 := by
      apply sum_le_sum
      intro g hg
      exact sum_le_sum fun e he => minorWeight_le (A g e) b (hA g e)
    _ = _ := by simp; ring
end ThreeSum.TernaryPairedInitial
