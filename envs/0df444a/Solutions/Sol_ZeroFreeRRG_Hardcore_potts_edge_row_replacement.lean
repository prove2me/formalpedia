-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.potts_edge_row_replacement
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:21:34.861375+00:00
-- url     : https://prove2.me/submissions/93937ccf-b345-42a9-a757-19c4b6fef789

import Definitions.Def_ZeroFreeRRG_Hardcore_PottsSegment
import Mathlib
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem solution {V : Type} [Fintype V] (q : ℕ) (G : SimpleGraph V) (β : ℂ)
    (W : Sym2 V → Fin q → Fin q → ℂ) (hW : ∀ e i j, W e i j = W e j i)
    (hseg : pottsSegmentWeights q G β W) (e₀ : Sym2 V) (a b : Fin q) :
    ∃ W' : Sym2 V → Fin q → Fin q → ℂ,
      (∀ e i j, W' e i j = W' e j i) ∧ pottsSegmentWeights q G β W' ∧
      (∀ e ≠ e₀, ∀ i j, W' e i j = W e i j) ∧
      (∀ j, W' e₀ a j = W e₀ b j) := by
  classical
  let W' := fun e i j => if e=e₀ then
    if i=a then W e b j else if j=a then W e b i else W e i j
    else W e i j
  refine ⟨W',?_,?_,?_,?_⟩
  · intro e i j
    by_cases he : e=e₀
    · by_cases hi : i=a <;> by_cases hj : j=a <;> simp [W',he,hi,hj,hW]
    · simp [W',he,hW]
  · intro e he i j
    by_cases h : e=e₀
    · by_cases hi : i=a
      · simpa [W',h,hi] using hseg e he b j
      · by_cases hj : j=a
        · simpa [W',h,hi,hj] using hseg e he b i
        · simpa [W',h,hi,hj] using hseg e he i j
    · simpa [W',h] using hseg e he i j
  · intro e he i j
    simp [W',he]
  · intro j
    simp [W']
