-- Prove2me | solution 1 for QEC.Coding.BDL26NativeGeometricAvoidance.native_joint_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:27:34.613548+00:00
-- url     : https://prove2.me/submissions/0463eeb1-195c-4b79-8f8d-8836ec9dab62

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricLegacy
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricAvoidance
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_keyEvent_joint_law
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
    (J : Vertex (Presentation S n) → Space) (r : ℝ) (e : NativeEvent S n J r)
    (ν : Vertex (Presentation S n) → Measure Space) [∀ v, IsProbabilityMeasure (ν v)] :
    (Measure.pi ν).map (fun w (a : e.val) i => w (triangleVertex (Presentation S n) a.val i)) =
      Measure.pi (fun a : e.val =>
        Measure.pi (fun i => ν (triangleVertex (Presentation S n) a.val i))) :=
  keyEvent_joint_law _ _ (BDL26NativeTriangleColors.nativeKey_injective S n) J r e ν
end QEC.Coding.BDL26NativeGeometricAvoidance
