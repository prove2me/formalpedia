-- Prove2me | solution 1 for QEC.Locality.WeightedConnectedSetMass.interval_eq_positive_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:46:03.375887+00:00
-- url     : https://prove2.me/submissions/efd34937-2508-40ca-af77-445b1282a035

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
theorem _root_.solution (f : ℕ → ℝ) (L U : ℕ) :
    interval f L U=∑ m ∈ Finset.Icc (max 1 L) U, f m := by
  have he : Finset.Icc (max 1 L) U =
      (Finset.range (U+1-max 1 L)).image (fun j => max 1 L+j) := by
    ext m
    simp only [Finset.mem_Icc,Finset.mem_image,Finset.mem_range]
    constructor
    · rintro ⟨hl,hu⟩
      exact ⟨m-max 1 L,by omega,by omega⟩
    · rintro ⟨j,hj,rfl⟩; omega
  rw [he,Finset.sum_image]
  · rfl
  · intro i hi j hj h
    change max 1 L+i = max 1 L+j at h
    exact Nat.add_left_cancel h
end QEC.Locality.WeightedConnectedSetMass
