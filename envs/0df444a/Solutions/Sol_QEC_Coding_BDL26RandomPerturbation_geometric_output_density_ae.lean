-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.geometric_output_density_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:53:10.820197+00:00
-- url     : https://prove2.me/submissions/7caa6998-595c-41e9-9244-bf8ca7867277

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventPriority
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FullEventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodAssignments
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_geometric_execution_good_ae
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_avoidance_triangle_density
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_capCutoff_bounds


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P) :
    letI (v : Vertex P) := vertexLaw_probability P
      ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
    ∀ᵐ T ∂tableLaw (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m)),
      ∀ z, ((familyHits (oldTriangleImage P
        (perturbedMap P J p.lambda (geometricOutput P J p T)))
          (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound := by
  letI (v : Vertex P) := vertexLaw_probability P
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
  filter_upwards [geometric_execution_good_ae P J p hJ hv] with T hT
  intro z
  exact avoidance_triangle_density P J _ p hJ hv (fun v => (hT.2.1 v).1.le)
    (fun e => hT.2.2 e (Finset.mem_univ e)) z
end QEC.Coding.BDL26RandomPerturbation
