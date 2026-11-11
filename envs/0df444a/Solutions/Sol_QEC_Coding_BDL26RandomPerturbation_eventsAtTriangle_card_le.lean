-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.eventsAtTriangle_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T22:18:22.515271+00:00
-- url     : https://prove2.me/submissions/137efd85-f313-4194-b16b-b640acfcb3f8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_DependencyCounts
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    (K M : ℕ) (a : Triangle P) (hpool : (localPool P J K a).card ≤ M) :
    (eventsAtTriangle P J K a).card ≤ M^3 := by
  classical
  have hc : (eventsAtTriangle P J K a).card ≤ ((localPool P J K a).powersetCard 3).card := by
    apply Finset.card_le_card_of_injOn (fun e : Event P J K => e.val.erase a)
    · intro e he
      have ha : a ∈ e.val := (Finset.mem_filter.mp he).2
      apply Finset.mem_powersetCard.mpr
      constructor
      · intro b hb
        have heb : b ∈ e.val := Finset.mem_of_mem_erase hb
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,e.property.2.2 a ha b heb⟩
      · rw [Finset.card_erase_of_mem ha,e.property.1]
    · intro e he f hf hef
      have hea : a ∈ e.val := (Finset.mem_filter.mp he).2
      have hfa : a ∈ f.val := (Finset.mem_filter.mp hf).2
      apply Subtype.ext
      calc
        e.val = insert a (e.val.erase a) := (Finset.insert_erase hea).symm
        _ = insert a (f.val.erase a) := congrArg (insert a) hef
        _ = f.val := Finset.insert_erase hfa
  rw [Finset.card_powersetCard] at hc
  exact hc.trans ((Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hpool 3))
end QEC.Coding.BDL26RandomPerturbation
