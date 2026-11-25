-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointsBilinear_mixedDisc_update_sum_ae519e6d25de
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:47:22.21335+00:00
-- url     : https://prove2.me/submissions/640613d8-c123-48c0-9eb0-43ccb56b45c5

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsBilinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsBilinear
import Theorems.Thm_ReciprocityTheory_AnForm_A_exists_multilinearMap_eq_mdisc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
open GroundTheory.Heights₂.Heights.PointsBilinear
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.PointsBilinear
theorem _root_.solution {D : ℕ} {T : Type} [Fintype T] (A : Fin D → Matrix (Fin D) (Fin D) ℂ)
    (k : Fin D) (B : T → Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (Function.update A k (∑ t, B t)) = ∑ t, mixedDisc (Function.update A k (B t)) := by
  obtain ⟨M, hM⟩ := ReciprocityTheory.AnForm.A.exists_multilinearMap_eq_mdisc (D := D)
  have e : ∀ C, mixedDisc (Function.update A k C) = M.toLinearMap A k C := fun C => by
    rw [MultilinearMap.toLinearMap_apply, hM]
    rfl
  simp only [e, map_sum]
end GroundTheory.Heights₂.Heights.PointsBilinear
