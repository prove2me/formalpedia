-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_SpreadBundleNbhd_proof_23c503d58767
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:05:06.656808+00:00
-- url     : https://prove2.me/submissions/0d8d6ab1-f4e4-460d-902b-67c17b2557b3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadNbhd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadStep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSpreadBundleNbhd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_SpreadsOn_toNbhd_7b57d76b6882
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_spreadNbhd_of_isEmpty_9b72b381a6b7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
variable {X : Scheme.{0}}
namespace GroundTheory.Heights₂.Heights.Model
namespace SpreadBundleNbhd
theorem _root_.solution (h₁ : SpreadLocal.Statement) (h₂ : SpreadStep.Statement) :
    SpreadBundleNbhd.Statement := by
  intro X f _ _ p E hE
  classical
  rcases isEmpty_or_nonempty (baseChange f (ZLoc p)) with hX | hne
  · exact spreadNbhd_of_isEmpty f (ZLoc p) E
  obtain ⟨x₀⟩ := hne
  choose Wx hxW hWx using h₁ X f p E hE
  have hcov : Set.univ ⊆ ⋃ x, ((baseChangeMap f (ZLoc p) ⁻¹ᵁ Wx x :
      (baseChange f (ZLoc p)).Opens) : Set (baseChange f (ZLoc p))) :=
    fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩
  have hc : IsCompact (Set.univ : Set (baseChange f (ZLoc p))) := isCompact_univ
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover _ (fun x => (baseChangeMap f (ZLoc p) ⁻¹ᵁ Wx x).isOpen) hcov
  have key : ∀ s : Finset (baseChange f (ZLoc p)), ∃ W : X.Opens,
      (∀ x ∈ s, baseChangeMap f (ZLoc p) ⁻¹ᵁ Wx x ≤ baseChangeMap f (ZLoc p) ⁻¹ᵁ W) ∧
        SpreadsOn f (ZLoc p) E W := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨Wx x₀, fun x hx => absurd hx (Finset.notMem_empty x), hWx x₀⟩
    | insert a s ha ih =>
      obtain ⟨W, hW, hEW⟩ := ih
      obtain ⟨W', hW', hEW'⟩ := h₂ X f p E (Wx a) W (hWx a) hEW
      refine ⟨W', fun x hx => ?_, hEW'⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact le_sup_left.trans hW'
      · exact (hW x hx).trans (le_sup_right.trans hW')
  obtain ⟨W, hW, hEW⟩ := key t
  obtain ⟨hW', E', hE', hiso⟩ := hEW.toNbhd f (ZLoc p) (fun y _ => by
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact hW x hx hy)
  exact ⟨W, hW', E', hE', hiso⟩
end SpreadBundleNbhd
end GroundTheory.Heights₂.Heights.Model
