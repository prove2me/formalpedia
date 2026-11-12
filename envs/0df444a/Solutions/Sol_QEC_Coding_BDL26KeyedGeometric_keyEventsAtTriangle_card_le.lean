-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.keyEventsAtTriangle_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:39:01.392866+00:00
-- url     : https://prove2.me/submissions/41c68fa0-62fc-472c-823a-fa7c5e9706bc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricEvents
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_DependencyCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricCounts
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory ProbabilityTheory
namespace QEC.Coding.BDL26KeyedGeometric
theorem _root_.solution (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (K M : ℕ) (a : Triangle P) (hpool : (localPool P J K a).card ≤ M) :
    (keyEventsAtTriangle P key hk J K a).card ≤ M^3 := by
  classical
  have hc : (keyEventsAtTriangle P key hk J K a).card ≤ ((localPool P J K a).powersetCard 3).card := by
    apply Finset.card_le_card_of_injOn (fun e : KeyEvent P key hk J K => e.val.erase a)
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
end QEC.Coding.BDL26KeyedGeometric
