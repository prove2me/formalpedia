-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.legacy_global_event
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:51:19.278319+00:00
-- url     : https://prove2.me/submissions/a5569785-8b08-4374-8fc4-0bd5a8ede14d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricAvoidance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricLegacy
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangleKey_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory
namespace QEC.Coding.BDL26KeyedGeometric
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r l : ℝ) (K : ℕ) (e : KeyEvent P (triangleKey P) (triangleKey_injective P) J r) :
    localEvent (X := fun _ : Vertex P => Space)
      (keySupport P (triangleKey P) (triangleKey_injective P) J r)
      (keyBad P (triangleKey P) (triangleKey_injective P) J r l K) e =
      localEvent (X := fun _ : Vertex P => Space)
        (eventSupport P J r) (eventBad P J r l K) (legacyEventEquiv P J r e) := rfl
end QEC.Coding.BDL26KeyedGeometric
