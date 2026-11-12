-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleKeys.keyOfCode_success
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:04:19.504202+00:00
-- url     : https://prove2.me/submissions/41124425-77dd-4da4-97e2-f08f909b71fd

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_encode_injective
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_keyOfCode_value
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_keyOfCode_original
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_triangle_labels
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section
namespace QEC.Coding.BDL26NativeTriangleKeys
theorem _root_.solution (S : OddScale) (n : ℕ) (c : Code) (k : ℕ) :
    (keyOfCodeQ S n c).1=some k ↔
      ∃!t : Triangle (P S n),encode S n t=c ∧ (nativeTriangleIndex S n t).val=k := by
  constructor
  · intro h
    rw [keyOfCode_value] at h
    split at h
    · rename_i hc
      rcases (BDL26NativePresentationGenerator.triangle_labels S n c).mp hc with ⟨t,ht⟩
      have hk : 2*c.owner+c.copy=k := Option.some.inj h
      refine ⟨t,⟨ht,?_⟩,?_⟩
      · rw [←ht] at hk; exact hk
      · intro u hu; exact encode_injective S n (hu.1.trans ht.symm)
    · contradiction
  · rintro ⟨t,⟨rfl,rfl⟩,_⟩
    exact keyOfCode_original S n t
end QEC.Coding.BDL26NativeTriangleKeys
