-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.eventsAtVertex_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T22:20:21.487456+00:00
-- url     : https://prove2.me/submissions/c0d75831-e634-41fc-8f46-64521be14b0e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LocalCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_DependencyCounts

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    (K : ℕ) (v : Vertex P) :
    eventsAtVertex P J K v ⊆ (incidentTriangles P v).biUnion (eventsAtTriangle P J K) := by
  classical
  intro e he
  have hv : v ∈ eventSupport P J K e := (Finset.mem_filter.mp he).2
  obtain ⟨a,ha,hva⟩ := Finset.mem_biUnion.mp hv
  exact Finset.mem_biUnion.mpr ⟨a,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hva⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩⟩
end QEC.Coding.BDL26RandomPerturbation
