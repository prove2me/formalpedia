-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMult_weightedHomogeneousComponent_mem_of_isMultiHomogIdeal_91ec1ac4e335
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:39:54.364712+00:00
-- url     : https://prove2.me/submissions/cee1cb85-e58f-42fc-8a1b-f1c7b618eded

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMult
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMultLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitChartMult
variable {ι : Type} {n : ι → ℕ}
variable (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
variable [Fintype ι] [DecidableEq ι]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace GroundTheory.Heights₂.Heights.OrbitChartMult
theorem _root_.solution
    {V : Ideal (MvPolynomial (Coord n) ℤ)} (hV : Geo.IsMultiHomogIdeal (ι := blockIdx n) V)
    {v : MvPolynomial (Coord n) ℤ} (hv : v ∈ V) (e : ι → ℕ) :
    weightedHomogeneousComponent (coordDeg n) e v ∈ V := by
  obtain ⟨S, hS, rfl⟩ := hV
  have hh : (Ideal.span S).IsHomogeneous (weightedHomogeneousSubmodule ℤ (coordDeg n)) :=
    Ideal.homogeneous_span _ S fun f hf ↦ by
      obtain ⟨a, ha⟩ := hS f hf
      exact ⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ((geoMultiHomog_iff f a).mp ha)⟩
  exact weightedHomogeneousComponent_mem_of_mem ℤ (coordDeg n) hh hv e
end GroundTheory.Heights₂.Heights.OrbitChartMult
