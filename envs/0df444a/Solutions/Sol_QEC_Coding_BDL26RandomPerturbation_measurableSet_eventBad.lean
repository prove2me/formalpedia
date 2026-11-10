-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.measurableSet_eventBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T03:00:46.179513+00:00
-- url     : https://prove2.me/submissions/3e3d7c1b-9727-426b-a186-01fa03cb8dac

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingGeometry
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_measurableSet_triangleHit


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (e : Event P J radius) :
    MeasurableSet (eventBad P J radius lambda K e) := by
  apply MeasurableSet.iUnion
  intro g
  apply MeasurableSet.iInter
  intro a
  exact (measurableSet_triangleHit _ _ _).preimage (by fun_prop)
end QEC.Coding.BDL26RandomPerturbation
