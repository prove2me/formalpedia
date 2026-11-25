-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_isOpen_chart_ne_ce897c4f4dc7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:28:53.663559+00:00
-- url     : https://prove2.me/submissions/763c09b5-a4e6-4ad3-b925-518bcfecd1d4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PullWMemFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PullBad
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_HasStrictFDerivAtEquiv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pullbackPushforward_holds_eval_lift_eq_zero_iff_a992e61efe8a
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_analyticAt_lift_chart


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
  Topology Filter Set
open GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {P' J' : Ideal (MRing ι')} {n : ℕ} (R : AnLogRes P' J' n) {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
namespace GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds
theorem _root_.solution {f : MRing ι'} {a : K' → ℕ} (hf : IsMultiHomog f a) (j : Fin R.A.n) :
    IsOpen ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' {x | eval (R.lift x x) (map (Int.castRingHom ℂ) f) ≠ 0}) := by
  rw [isOpen_iff_mem_nhds]
  rintro u1 ⟨hu1, h1⟩
  set x1 := (R.A.chart j).symm u1
  have hV : (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x1 ∈ 𝓝 u1 :=
    ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x1)).mem_nhds ⟨hu1, R.mem_U x1⟩
  have hcont : ContinuousAt (fun u => eval (R.lift x1 ((R.A.chart j).symm u))
      (map (Int.castRingHom ℂ) f)) u1 :=
    (MvPolynomial.continuous_eval _).continuousAt.comp
      (analyticAt_lift_chart R x1 j ⟨hu1, R.mem_U x1⟩).continuousAt
  have hne : eval (R.lift x1 ((R.A.chart j).symm u1)) (map (Int.castRingHom ℂ) f) ≠ 0 := h1
  filter_upwards [hV, hcont.eventually_ne hne] with u hu hne'
  exact ⟨hu.1, fun h => hne' ((eval_lift_eq_zero_iff R hf hu.2).mp h)⟩
end GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds
