-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.randomized_embedding_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:55:42.975383+00:00
-- url     : https://prove2.me/submissions/756310c8-cf0e-478f-b32c-6481238f6029

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_geometric_output_geometry_density_ae
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_perturbationEmbeddingOutput
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_capCutoff_bounds
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_geometricParameters_nonempty
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_geometric_expected_operations_le_qubits
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_supported_avoidance_positive


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (densityLower : ℝ) :
    ∃ p : GeometricParameters densityLower,
      (0 : ℝ) < triangleDensityBound ∧ (triangleDensityBound : ℝ) < p.t ∧
      ∀ (P : TannerSquarePresentation) (A : TannerSquareAdmissible P) (J : Vertex P → Space),
        IsBoundedDensityLocalMap P J p.t → BoundedValence P →
        letI (v : Vertex P) := vertexLaw_probability P
          ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
        0 < (geometricLaw P p).real (geometricSupport P p ∩ geometricAvoidance P J p) ∧
        Measurable (perturbationEmbeddingOutput P J p) ∧
        (∀ᵐ T ∂tableLaw (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m)),
          Halts (eventSupport P J (anchorRadius p.m))
            (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T ∧
          IncomingFaceGeometry P (perturbationOddScale p)
            (perturbedMap P J p.lambda (geometricOutput P J p T))
            (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
          ∀ z, ((familyHits (oldTriangleImage P
            (perturbedMap P J p.lambda (geometricOutput P J p T)))
              (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound) ∧
        (∫⁻ T, actualExecutionCost P J (by positivity : (0 : ℝ) ≤ anchorRadius p.m)
          p.lambda ((6*p.m+2)*p.lambda) T
          ∂tableLaw (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))) ≤
            (operationConstant ((6*p.m+2)*p.lambda)*(65*Fintype.card P.Q+1)^10 : ℕ) := by
  obtain ⟨p⟩ := geometricParameters_nonempty densityLower
  refine ⟨p,by norm_num [triangleDensityBound],p.triangle_density,?_⟩
  intro P A J hJ hv
  letI (v : Vertex P) := vertexLaw_probability P
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
  exact ⟨supported_avoidance_positive P J p hJ hv,measurable_perturbationEmbeddingOutput P J p,
    geometric_output_geometry_density_ae P J p hJ hv,
    geometric_expected_operations_le_qubits P J A p hJ hv⟩
end QEC.Coding.BDL26RandomPerturbation
