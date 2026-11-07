-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.exists_balanced_punctures
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:50:15.909505+00:00
-- url     : https://prove2.me/submissions/02d1a7e5-a9d5-4606-958c-e18ec7da6147

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_TensorPuncture

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]
namespace QEC.Coding.QuantumTanner
theorem _root_.solution
    (badA : Finset A) (badB : Finset B) (p : Nat)
    (hCard : Fintype.card A = Fintype.card B)
    (hA : badA.card ≤ p) (hB : badB.card ≤ p) (hp : p ≤ Fintype.card A) :
    ∃ removedA : Finset A, ∃ removedB : Finset B,
      badA ⊆ removedA ∧ badB ⊆ removedB ∧
      removedA.card = removedB.card ∧ removedA.card ≤ p := by
  let m := max badA.card badB.card
  have hm : m ≤ p := max_le hA hB
  obtain ⟨removedA, hContainsA, hSizeA⟩ :=
    Finset.exists_superset_card_eq (le_max_left badA.card badB.card) (hm.trans hp)
  obtain ⟨removedB, hContainsB, hSizeB⟩ :=
    Finset.exists_superset_card_eq (le_max_right badA.card badB.card)
      (hm.trans (hp.trans_eq hCard))
  exact ⟨removedA, removedB, hContainsA, hContainsB,
    hSizeA.trans hSizeB.symm, hSizeA.le.trans hm⟩
end QEC.Coding.QuantumTanner
