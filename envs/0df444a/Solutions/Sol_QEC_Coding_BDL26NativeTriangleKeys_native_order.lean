-- Prove2me | solution 1 for QEC.Coding.BDL26NativeTriangleKeys.native_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:05:21.570567+00:00
-- url     : https://prove2.me/submissions/91dd8abd-519e-4443-8a12-8ca6e735908a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleKeys

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeTriangleKeys
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26DecodingGraph
noncomputable section
namespace QEC.Coding.BDL26NativeTriangleKeys
theorem _root_.solution (S : OddScale) (n : ℕ) :
    (∀a b,nativeLE S n a b ∨ nativeLE S n b a) ∧
      (∀a b c,nativeLE S n a b → nativeLE S n b c → nativeLE S n a c) ∧
      (∀a b,nativeLE S n a b → nativeLE S n b a → a=b) := by
  refine ⟨fun a b => le_total _ _,fun a b c hab hbc => le_trans hab hbc,?_⟩
  intro a b hab hba
  apply (nativeTriangleIndex S n).injective
  exact Fin.ext (le_antisymm hab hba)
end QEC.Coding.BDL26NativeTriangleKeys
