-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_pullQ_eq_local_fc4719124d2a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:36:10.44386+00:00
-- url     : https://prove2.me/submissions/2b0ec455-c820-486c-8edf-62f55a3f49b2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PullWMemFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PullBad
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_HasStrictFDerivAtEquiv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_segre_of_sameOrbit_b6140a3065b0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_pullPt_sameOrbit_d61c506d0e99
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
  Topology Filter Set
open GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {P' J' : Ideal (MRing ι')} {n : ℕ} (R : AnLogRes P' J' n) {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
namespace GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds
theorem _root_.solution (hv : IsBlockMap κ v) (Φ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    {x z : R.X} (hz : z ∈ R.U x) :
    pullQ R v Φ z = fun i => Φ (segre (fun p => R.lift x z (v p))) i.succ /
      Φ (segre (fun p => R.lift x z (v p))) 0 := by
  obtain ⟨μ, hμ, hseg⟩ := segre_of_sameOrbit (pullPt_sameOrbit R hv hz)
  funext i
  simp only [pullQ, hseg, map_smul, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hμ
end GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds
