-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.keyGood_geometry_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:00:48.103013+00:00
-- url     : https://prove2.me/submissions/7fcfd801-fd72-4b0a-a156-53e34a11435a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricProbability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodAssignments
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricAvoidance
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_key_avoidance_triangle_density
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_geometricSupport_incoming_geometry
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_perturbationOddScale_bounds


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory ProbabilityTheory
namespace QEC.Coding.BDL26KeyedGeometric
theorem _root_.solution (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) {L : ℝ}
    (p : GeometricParameters L) (hJ : IsBoundedDensityLocalMap P J p.t)
    (hv : BoundedValence P) (w : Vertex P → Space) (hw : w ∈ KeyGood P key hk J p) :
    IncomingFaceGeometry P (perturbationOddScale p) (perturbedMap P J p.lambda w)
      (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
    ∀ z, ((familyHits (oldTriangleImage P (perturbedMap P J p.lambda w))
      (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound := by
  refine ⟨geometricSupport_incoming_geometry P J p hJ (perturbationOddScale p)
    (perturbationOddScale_bounds p).1.le w hw.1,?_⟩
  intro z
  exact key_avoidance_triangle_density P key hk J w p hJ hv (fun v => (hw.1 v).1.le)
    (fun e => hw.2 e (Finset.mem_univ e)) z
end QEC.Coding.BDL26KeyedGeometric
