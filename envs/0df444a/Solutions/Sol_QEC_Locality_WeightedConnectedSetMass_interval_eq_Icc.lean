-- Prove2me | solution 1 for QEC.Locality.WeightedConnectedSetMass.interval_eq_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:52:41.782562+00:00
-- url     : https://prove2.me/submissions/3ba28af2-862e-4e73-be3f-5a68572b40ed

import Definitions.Def_QEC_Locality_Graph_ConnectedSetCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_interval_eq_positive_Icc

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality QEC.Locality.WeightedConnectedSetMass
open Classical ConnectedSetCounting
open scoped BigOperators Classical
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
namespace QEC.Locality.WeightedConnectedSetMass
theorem _root_.solution (f : ℕ → ℝ) (hf : f 0=0) (L U : ℕ) :
    interval f L U=∑ m ∈ Finset.Icc L U, f m := by
  rw [interval_eq_positive_Icc]
  apply Finset.sum_subset
  · intro m hm
    have h := Finset.mem_Icc.mp hm
    exact Finset.mem_Icc.mpr ⟨by omega,h.2⟩
  · intro m hm hn
    have h := Finset.mem_Icc.mp hm
    have he : m=0 := by
      simp only [Finset.mem_Icc,not_and_or,not_le] at hn
      omega
    simpa only [he] using hf
end QEC.Locality.WeightedConnectedSetMass
