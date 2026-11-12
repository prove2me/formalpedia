-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.key_supported_avoidance_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:34:57.94741+00:00
-- url     : https://prove2.me/submissions/763a78ab-1ef8-427a-bfd0-bb39b928f0d6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricProbability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodAssignments
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricAvoidance
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_key_actual_avoidance_positive
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_geometricSupport_ae


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory ProbabilityTheory
namespace QEC.Coding.BDL26KeyedGeometric
theorem _root_.solution (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P) :
    0 < (geometricLaw P p).real (geometricSupport P p ∩ KeyAvoid P key hk J p) := by
  have he := Measure.measure_inter_eq_of_ae (s := KeyAvoid P key hk J p) (geometricSupport_ae P p)
  change 0 < ((geometricLaw P p) (geometricSupport P p ∩ KeyAvoid P key hk J p)).toReal
  rw [he]
  exact key_actual_avoidance_positive P key hk J p hJ hv
end QEC.Coding.BDL26KeyedGeometric
