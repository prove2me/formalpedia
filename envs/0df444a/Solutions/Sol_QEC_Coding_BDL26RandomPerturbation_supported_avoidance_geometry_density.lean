-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.supported_avoidance_geometry_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:26:24.997638+00:00
-- url     : https://prove2.me/submissions/d4996fe1-b197-477e-8ea4-161bd3032227

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_perturbationOddScale_bounds
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_avoidance_triangle_density
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_geometricSupport_incoming_geometry


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L) (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P)
    (w : Vertex P → Space) (hw : w ∈ geometricSupport P p ∩ geometricAvoidance P J p) :
    IncomingFaceGeometry P (perturbationOddScale p) (perturbedMap P J p.lambda w)
      (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
    ∀ z, ((familyHits (oldTriangleImage P (perturbedMap P J p.lambda w))
      (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound := by
  refine ⟨geometricSupport_incoming_geometry P J p hJ (perturbationOddScale p)
    (perturbationOddScale_bounds p).1.le w hw.1,?_⟩
  intro z
  exact avoidance_triangle_density P J w p hJ hv (fun v => (hw.1 v).1.le)
    (fun e => hw.2 e (Finset.mem_univ e)) z
end QEC.Coding.BDL26RandomPerturbation
