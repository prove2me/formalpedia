-- Prove2me | solution 1 for QEC.Locality.WeightedConnectedSetMass.structuralEnvelope_above
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:47:58.539929+00:00
-- url     : https://prove2.me/submissions/b63e17c4-323d-48d9-8b4c-c7a1a2a76f98

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
theorem _root_.solution (A b : ℝ) (c L U : ℕ) (hL : c<L) (hpos : 1≤L) :
    structuralEnvelope A b c L U = A^c*geometric (A*b) (L-c) (U+1-L) := by
  have hl : max 1 L=L := max_eq_right hpos
  unfold structuralEnvelope geometric
  simp only [hl]
  have hf : (Finset.range (U+1-L)).filter (fun j => L+j≤c) = ∅ := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_range,Finset.notMem_empty,iff_false]
    omega
  have ht : (Finset.range (U+1-L)).filter (fun j => c<L+j) = Finset.range (U+1-L) := by
    ext j; simp; omega
  rw [hf,ht,Finset.sum_empty,zero_add,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hexp : L+j-c=(L-c)+j := by omega
  rw [hexp]
end QEC.Locality.WeightedConnectedSetMass
