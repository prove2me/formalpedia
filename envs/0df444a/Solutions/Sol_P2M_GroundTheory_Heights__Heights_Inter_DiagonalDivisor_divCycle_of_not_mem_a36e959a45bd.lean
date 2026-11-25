-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalDivisor_divCycle_of_not_mem_a36e959a45bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:57:42.572282+00:00
-- url     : https://prove2.me/submissions/5d50c431-77ea-46be-b7c1-2a158188282a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagDiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalDivisor
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalDivisor
theorem _root_.solution {P W : Ideal (MRing ι)} {s : MRing ι} (hW : W ∉ divSupp P s) :
    divCycle P s W = 0 := by
  unfold divCycle
  simp [Finsupp.ofSupportFinite_coe, hW]
end GroundTheory.Heights₂.Heights.Inter.DiagonalDivisor
