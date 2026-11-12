-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleColors.lookup_failure_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:18:34.974551+00:00
-- url     : https://prove2.me/submissions/c06cfb3b-3935-4824-a1d3-84ed1edd3a09

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeSupportMetadata
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_lookup_actual
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_lookup_missing
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_triangle_labels


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleColors
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPerturbation BDL26BoundedValence
open G
noncomputable section
open scoped Classical
namespace QEC.Coding.BDL26NativeTriangleColors
theorem _root_.solution (S : OddScale) (n : ℕ) (c : Code) :
    (colorOfCodeQ S n c).value=none ↔ ¬∃t : Triangle (P S n),encode S n t=c := by
  constructor
  · intro h ⟨t,ht⟩
    rw [←ht,lookup_actual] at h
    cases h
  · intro h
    apply lookup_missing S n c
    intro hc
    exact h ((BDL26NativePresentationGenerator.triangle_labels S n c).mp hc)
end QEC.Coding.BDL26NativeTriangleColors
