-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.actual_event_criterion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T23:11:54.330211+00:00
-- url     : https://prove2.me/submissions/46b7c8dd-4bdd-46f3-8e97-ca23d70163db

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ConcreteParameters
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalLemmaApplication
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_GeometricParameters_probability_ratio
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_capCutoff_bounds
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_event_degree_le_of_density
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_event_probability_real_decay
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_uniform_lll_criterion
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    {densityLower : ℝ} (p : GeometricParameters densityLower)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P)
    (e : Event P J (anchorRadius p.m)) :
    (Measure.pi (vertexLaw P ((6*p.m : ℕ)* (p.lambda : ℝ)) (capCutoff p.m))).real
      (localEvent (eventSupport P J (anchorRadius p.m))
        (eventBad P J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) e) ≤
      lllWeight (dependencyBound p.M)*
        ∏ _j ∈ (supportGraph (eventSupport P J (anchorRadius p.m))).neighborFinset e,
          (1-lllWeight (dependencyBound p.M)) := by
  have hc := capCutoff_bounds p.m_two
  have ha : 0 < 6*p.m := by
    have hm := p.m_two
    omega
  have hb := event_probability_real_decay P J (anchorRadius p.m) (6*p.m) p.lambda
    ha p.lambda_one e hc.1 hc.2
  apply uniform_lll_criterion (dependencyBound p.M) _
    (event_degree_le_of_density P J (anchorRadius p.m) p.M p.t hJ hv p.pool e)
  exact hb.trans p.probability_ratio
end QEC.Coding.BDL26RandomPerturbation
