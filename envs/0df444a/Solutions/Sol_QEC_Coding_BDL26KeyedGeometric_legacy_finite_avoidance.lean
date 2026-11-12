-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.legacy_finite_avoidance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T02:25:31.509928+00:00
-- url     : https://prove2.me/submissions/1836057b-395a-4bc6-8199-4c91f9af8044

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricAvoidance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricLegacy
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_legacy_global_event
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
    (r l : ℝ) (K : ℕ)
    (s : Finset (KeyEvent P (triangleKey P) (triangleKey_injective P) J r)) :
    avoid (localEvent (X := fun _ : Vertex P => Space)
      (keySupport P (triangleKey P) (triangleKey_injective P) J r)
      (keyBad P (triangleKey P) (triangleKey_injective P) J r l K)) s =
      avoid (localEvent (X := fun _ : Vertex P => Space)
        (eventSupport P J r) (eventBad P J r l K))
        (s.image (legacyEventEquiv P J r)) := by
  classical
  ext w
  constructor
  · intro hw f hf
    rcases Finset.mem_image.mp hf with ⟨e,he,rfl⟩
    rw [← legacy_global_event P J r l K e]
    exact hw e he
  · intro hw e he
    rw [legacy_global_event P J r l K e]
    exact hw _ (Finset.mem_image.mpr ⟨e,he,rfl⟩)
end QEC.Coding.BDL26KeyedGeometric
