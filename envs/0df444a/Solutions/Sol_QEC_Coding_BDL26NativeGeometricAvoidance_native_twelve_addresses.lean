-- Prove2me | solution 1 for QEC.Coding.BDL26NativeGeometricAvoidance.native_twelve_addresses
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:27:31.34531+00:00
-- url     : https://prove2.me/submissions/c7bd4d7b-14f1-4e7e-9700-69dac9f911af

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricLegacy
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricAvoidance
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_keyEvent_addresses_injective
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_keySupport_card_eq_twelve
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_nativeKey_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeGeometricAvoidance
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26FiniteAlternatingCore BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26KeyedGeometric
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory
namespace QEC.Coding.BDL26NativeGeometricAvoidance
theorem _root_.solution (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) (e : NativeEvent S n J r) :
    (NativeSupport S n J r e).card = 12 ∧
      Function.Injective (fun s : (a : e.val) × Fin 3 =>
        triangleVertex (Presentation S n) s.1.val s.2) :=
  ⟨keySupport_card_eq_twelve _ _ (BDL26NativeTriangleColors.nativeKey_injective S n) J r e,
    keyEvent_addresses_injective _ _ (BDL26NativeTriangleColors.nativeKey_injective S n) J r e⟩
end QEC.Coding.BDL26NativeGeometricAvoidance
