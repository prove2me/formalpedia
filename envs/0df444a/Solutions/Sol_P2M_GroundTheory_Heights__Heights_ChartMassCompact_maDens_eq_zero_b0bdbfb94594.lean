-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMassCompact_maDens_eq_zero_b0bdbfb94594
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:24:56.6535+00:00
-- url     : https://prove2.me/submissions/a14ab865-8574-40c4-adb0-5b0216e1b63f

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMassCompact_mdisc_coord_zero_b76457691cde
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMassCompact_hessC_eq_zero_of_eventuallyEq_589be8fe8118

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMassCompact
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartMassCompact
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : IsSheetAt J A x s)
    (ψ : Fin d → (Fin n → ℂ) → ℝ) (i : Fin d) (hx : x ∉ tsupport (ψ i)) :
    ReciprocityTheory.AnForm.maDens (fun k => ψ k ∘ s) (A *ᵥ x) = 0 := by
  obtain ⟨U, hU, hxU, hsd, hsx, -⟩ := hs
  have hcont : ContinuousAt s (A *ᵥ x) := (hsd.differentiableAt (hU.mem_nhds hxU)).continuousAt
  have hev : (ψ i ∘ s) =ᶠ[𝓝 (A *ᵥ x)] 0 := by
    have hnhds : (tsupport (ψ i))ᶜ ∈ 𝓝 (s (A *ᵥ x)) := by
      rw [hsx]
      exact (isClosed_tsupport _).isOpen_compl.mem_nhds hx
    filter_upwards [hcont.preimage_mem_nhds hnhds] with y hy
    show ψ i (s y) = 0
    exact image_eq_zero_of_notMem_tsupport hy
  unfold ReciprocityTheory.AnForm.maDens
  rw [mdisc_coord_zero _ i (hessC_eq_zero_of_eventuallyEq hev)]
  simp
end GroundTheory.Heights₂.Heights.ChartMassCompact
