-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.assignment_cap_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T22:03:49.12459+00:00
-- url     : https://prove2.me/submissions/32de47ed-70b5-4b12-b795-ff7223f5733d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Coloring
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_TriangleHit
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Sampling
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_table_cap_support

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) {R c : ℝ} (hR : 0 < R)
    (hc : c < 1) :
    letI (v : Vertex P) := vertexLaw_probability P R hc v
    ∀ᵐ T ∂tableLaw (vertexLaw P R c), ∀ n : Vertex P → ℕ, ∀ v : Vertex P,
      assignment T n v ∈ displacementCap R (vertexAxis P v) c := by
  letI (v : Vertex P) := vertexLaw_probability P R hc v
  filter_upwards [table_cap_support P hR hc] with T hT
  intro n v
  exact hT (v,n v)
end QEC.Coding.BDL26RandomPerturbation
