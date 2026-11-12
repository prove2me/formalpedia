-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.events_have_dependency_graph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:50:59.644006+00:00
-- url     : https://prove2.me/submissions/43911c91-efad-4ad6-ba0f-ef9862313b72

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingGeometry
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurableSet_eventBad
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_product_hasDependencyGraph


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (ν : Vertex P → Measure Space)
    [∀ v, IsProbabilityMeasure (ν v)] :
    HasDependencyGraph (Measure.pi ν)
      (localEvent (eventSupport P J radius) (eventBad P J radius lambda K))
      (supportGraph (eventSupport P J radius)) := by
  classical
  exact product_hasDependencyGraph ν (eventSupport P J radius)
    (eventBad P J radius lambda K) (measurableSet_eventBad P J radius lambda K)
end QEC.Coding.BDL26RandomPerturbation
