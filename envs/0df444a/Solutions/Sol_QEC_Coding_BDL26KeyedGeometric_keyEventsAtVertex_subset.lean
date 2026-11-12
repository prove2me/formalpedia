-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometric.keyEventsAtVertex_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:40:07.321383+00:00
-- url     : https://prove2.me/submissions/39961aa6-bae0-4267-b9fc-fc88ad7a36a2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricEvents
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_DependencyCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricCounts

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
    (K : ℕ) (v : Vertex P) :
    keyEventsAtVertex P key hk J K v ⊆ (incidentTriangles P v).biUnion (keyEventsAtTriangle P key hk J K) := by
  classical
  intro e he
  have hv : v ∈ keySupport P key hk J K e := (Finset.mem_filter.mp he).2
  obtain ⟨a,ha,hva⟩ := Finset.mem_biUnion.mp hv
  exact Finset.mem_biUnion.mpr ⟨a,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hva⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩⟩
end QEC.Coding.BDL26KeyedGeometric
