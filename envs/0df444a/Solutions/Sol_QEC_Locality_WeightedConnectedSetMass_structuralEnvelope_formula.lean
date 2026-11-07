-- Prove2me | solution 1 for QEC.Locality.WeightedConnectedSetMass.structuralEnvelope_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:53:22.565805+00:00
-- url     : https://prove2.me/submissions/0dc9322a-9523-4bca-a639-79cd047edf6b

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality QEC.Locality.WeightedConnectedSetMass
open Classical ConnectedSetCounting
open scoped BigOperators Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
namespace QEC.Locality.WeightedConnectedSetMass
theorem _root_.solution (A b : ℝ) (c L U : ℕ) :
    structuralEnvelope A b c L U =
      b*geometric A (max 1 L) (min (U+1-max 1 L) (c+1-max 1 L)) +
      A^c*geometric (A*b) (max (max 1 L) (c+1)-c)
        (U+1-max (max 1 L) (c+1)) := by
  let l := max 1 L
  let h := max l (c+1)
  have hp : (Finset.range (U+1-l)).filter (fun j => l+j≤c) =
      Finset.range (min (U+1-l) (c+1-l)) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  have ht : (Finset.range (U+1-l)).filter (fun j => c<l+j) =
      (Finset.range (U+1-h)).image (fun j => h-l+j) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_image]
    constructor
    · rintro ⟨hj,hc⟩
      exact ⟨j-(h-l),by dsimp [h] at *; omega,by dsimp [h] at *; omega⟩
    · rintro ⟨k,hk,rfl⟩; dsimp [h] at *; omega
  unfold structuralEnvelope
  change (∑ j ∈ (Finset.range (U+1-l)).filter (fun j => l+j≤c), b*A^(l+j)) +
    (∑ j ∈ (Finset.range (U+1-l)).filter (fun j => c<l+j), A^c*(A*b)^(l+j-c)) = _
  rw [hp,ht,Finset.sum_image]
  · have hexps : ∀ j : ℕ, l+(h-l+j)-c=(h-c)+j := by
      intro j
      dsimp [h]
      omega
    simp_rw [hexps]
    simp only [geometric,Finset.mul_sum]
    rfl
  · intro i hi j hj he
    change h-l+i = h-l+j at he
    exact Nat.add_left_cancel he
end QEC.Locality.WeightedConnectedSetMass
