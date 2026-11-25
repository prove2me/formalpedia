-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_mem_divSupp_of_mem_40c415dfdd3f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:19:58.199513+00:00
-- url     : https://prove2.me/submissions/73e3b28f-a6ae-4e2d-9569-ff9ce5c76c94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_mem_minimalPrimes_of_mem_e470b56afc04

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {P W : Ideal (MRing ι)} [P.IsPrime] {s t : MRing ι}
    (hW : W ∈ divSupp P s) (htP : t ∉ P) (htW : t ∈ W) : W ∈ divSupp P t :=
  ⟨mem_minimalPrimes_of_mem hW.1 htP htW, hW.2⟩
end GroundTheory.Heights₂.Heights.Inter
