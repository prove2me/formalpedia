-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.potts_row_set_properties
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:22:59.975125+00:00
-- url     : https://prove2.me/submissions/bc0a8d98-5803-4534-b602-86c9b7f32f66

import Definitions.Def_ZeroFreeRRG_Hardcore_PottsRowChain
import Mathlib
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution {V : Type} [Fintype V] (q : ℕ) (G : SimpleGraph V) (β : ℂ)
    (W : Sym2 V → Fin q → Fin q → ℂ) (hW : ∀ e i j, W e i j = W e j i)
    (hseg : pottsSegmentWeights q G β W) (F : Finset (Sym2 V)) (a b : Fin q) :
    let W' := pottsReplaceRows W F a b
    (∀ e i j, W' e i j = W' e j i) ∧ pottsSegmentWeights q G β W' ∧
      (∀ e ∉ F, ∀ i j, W' e i j = W e i j) ∧
      (∀ e ∈ F, ∀ j, W' e a j = W e b j) := by
  classical
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · intro e i j
    by_cases he : e∈F
    · by_cases hi : i=a <;> by_cases hj : j=a <;> simp [pottsReplaceRows,he,hi,hj,hW]
    · simp [pottsReplaceRows,he,hW]
  · intro e he i j
    by_cases h : e∈F
    · by_cases hi : i=a
      · simpa [pottsReplaceRows,h,hi] using hseg e he b j
      · by_cases hj : j=a
        · simpa [pottsReplaceRows,h,hi,hj] using hseg e he b i
        · simpa [pottsReplaceRows,h,hi,hj] using hseg e he i j
    · simpa [pottsReplaceRows,h] using hseg e he i j
  · intro e he i j
    simp [pottsReplaceRows,he]
  · intro e he j
    simp [pottsReplaceRows,he]
