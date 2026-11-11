-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.supported_avoidance_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:20:33.090774+00:00
-- url     : https://prove2.me/submissions/7ea8a788-9e64-4b3c-8aaf-ff0e2d1beab4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_AvoidanceDensity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodAssignments
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_geometricSupport_ae
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_actual_avoidance_positive


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P) :
    0 < (geometricLaw P p).real (geometricSupport P p ∩ geometricAvoidance P J p) := by
  have he := Measure.measure_inter_eq_of_ae (s := geometricAvoidance P J p) (geometricSupport_ae P p)
  change 0 < ((geometricLaw P p) (geometricSupport P p ∩ geometricAvoidance P J p)).toReal
  rw [he]
  exact actual_avoidance_positive P J p hJ hv
end QEC.Coding.BDL26RandomPerturbation
