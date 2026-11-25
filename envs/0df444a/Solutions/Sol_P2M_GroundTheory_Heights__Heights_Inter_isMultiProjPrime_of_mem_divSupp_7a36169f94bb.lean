-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_isMultiProjPrime_of_mem_divSupp_7a36169f94bb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:58:51.12226+00:00
-- url     : https://prove2.me/submissions/636037cc-326e-437e-878f-ca53dfccc66e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsWellDefined
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PWellDefined
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_cyc_isMultiHomogIdeal_of_mem_minimalPrimes


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
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} (hP : IsMultiProjPrime P) {u : MRing ι} {b : K → ℕ} (hu : IsMultiHomog u b)
    {W : Ideal (MRing ι)} (hW : W ∈ divSupp P u) : IsMultiProjPrime W :=
  ⟨hW.1.isPrime, ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isMultiHomogIdeal_of_mem_minimalPrimes hP.2.1 hu hW.1, hW.2⟩
end GroundTheory.Heights₂.Heights.Inter
