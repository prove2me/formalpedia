-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PullbackDegreeCount_ncard_pullW_eq_558ce03dd39e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:37:01.487864+00:00
-- url     : https://prove2.me/submissions/f89f10db-316f-4935-bb4c-4d1c253e205b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartRankAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PtsOver
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NormSegreSameOrbit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PullbackDegreeCount_sameOrbit_self_09533dc2b7ba
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PullbackDegreeCount_sameOrbit_comp_960e4212d0ab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PullbackDegreeCount_sameOrbit_flip_fd7e872fb3d7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PullbackDegreeCount_normSegre_sameOrbit_b77e8e882eac

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.Inter.PullbackDegreeCount
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
omit [Fintype K']
namespace GroundTheory.Heights₂.Heights.Inter.PullbackDegreeCount
theorem _root_.solution {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {P' J' : Ideal (MRing ι')} {n : ℕ} (R : AnLogRes P' J' n) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (w : ((k : K) → ι k) → ℂ)
    (hB : ∀ z' ∈ mcPts P', z' ∈ mcPts J' →
      (Ψ (segre fun p => z' (v p)) 0)⁻¹ • segre (fun p => z' (v p)) ≠ w) :
    {x | pullW R v Ψ x = w}.ncard = (ptsOver P' v Ψ w).ncard := by
  refine Set.ncard_congr (fun x _ => {z'' | SameOrbit z'' (R.lift x x)}) ?_ ?_ ?_
  · intro x hx
    exact ⟨R.lift x x, R.mem x x (R.mem_U x), rfl, hx⟩
  · intro x x' hx hx' h
    have hxB : R.lift x x ∉ mcPts J' := fun hJ => hB _ (R.mem x x (R.mem_U x)) hJ hx
    have hmem : R.lift x x ∈ {z'' | SameOrbit z'' (R.lift x' x')} := h ▸ sameOrbit_self _
    exact R.inj x x' hxB hmem
  · rintro O ⟨z', hz', rfl, hw⟩
    have hzB : z' ∉ mcPts J' := fun hJ => hB z' hz' hJ hw
    obtain ⟨x, hx⟩ := R.surj z' hz' hzB
    refine ⟨x, ?_, ?_⟩
    · show (Ψ (segre fun p => R.lift x x (v p)) 0)⁻¹ • segre (fun p => R.lift x x (v p)) = w
      rw [← hw]
      exact normSegre_sameOrbit hv Ψ hx
    · ext z''
      exact ⟨fun h => sameOrbit_comp h hx, fun h => sameOrbit_comp h (sameOrbit_flip hx)⟩
end GroundTheory.Heights₂.Heights.Inter.PullbackDegreeCount
