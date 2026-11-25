-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.hasDerivAt_realLine_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:26:34.463132+00:00
-- url     : https://prove2.me/submissions/98500f8e-d477-43ad-92a4-f1ae20aa8215

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_real_smul_smul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_deriv_slice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω)
    (hF : DifferentiableOn ℂ F Ω) {z : V n} (hz : z ∈ Ω) (e : V n) (μ : ℂ) :
    HasDerivAt (fun t : ℝ => fderiv ℂ F (z + t • (μ • e)) e) (complexLineSecondDeriv F z e * μ) 0 := by
  have hU : IsOpen {l : ℂ | z + l • e ∈ Ω} := hΩ.preimage (by fun_prop)
  have h0 : (0 : ℂ) ∈ {l : ℂ | z + l • e ∈ Ω} := by simpa using hz
  have hg : DifferentiableOn ℂ (fun l : ℂ => F (z + l • e)) {l : ℂ | z + l • e ∈ Ω} :=
    hF.comp (by fun_prop) (fun l hl => hl)
  have hg' := hg.deriv hU

  have hder : HasDerivAt (deriv fun l : ℂ => F (z + l • e)) (complexLineSecondDeriv F z e) (((0 : ℝ) : ℂ) * μ) := by
    have h1 := ((hg' 0 h0).differentiableAt (hU.mem_nhds h0)).hasDerivAt
    simpa [complexLineSecondDeriv] using h1
  have hc : HasDerivAt (fun t : ℝ => (t : ℂ) * μ) μ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const μ
  have hcomp := hder.comp (0 : ℝ) hc
  refine hcomp.congr_of_eventuallyEq ?_
  have h0' : ((0 : ℝ) : ℂ) * μ ∈ {l : ℂ | z + l • e ∈ Ω} := by simpa using hz
  filter_upwards [hc.continuousAt.preimage_mem_nhds (hU.mem_nhds h0')] with t ht
  show fderiv ℂ F (z + t • (μ • e)) e = deriv (fun l : ℂ => F (z + l • e)) ((t : ℂ) * μ)
  rw [real_smul_smul]
  exact (deriv_slice hΩ hF ht).symm
end ReciprocityTheory.L2DbarEstimates.C
