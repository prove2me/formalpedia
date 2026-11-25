-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.Moll.eq_A
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:20:38.951722+00:00
-- url     : https://prove2.me/submissions/4cd71096-79a4-4ca2-8231-df2c4b7a99dd

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ExpCombine
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_StepB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_StepC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousCexpIp
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_step_a
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_step_b
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_step_c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D PositivityTheory.Rg.Sw.WR.D.Moll
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
variable {n : ℕ} {X : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
set_option maxHeartbeats 1000000
namespace PositivityTheory.Rg.Sw.WR.D.Moll
theorem _root_.solution (Ψ : X → ℂ) (qq : X → E n) (hΨ : Integrable Ψ μ) (hqq : Measurable qq) (t : ℝ) (ht : t ≠ 0)
    (ψ : E n → ℂ) (hψc : Continuous ψ) (hψi : Integrable ψ) (ε : ℝ) (hε : 0 < ε) :
    ∫ β, ψ β * ((((|t| / (2 * Real.pi)) ^ (n ^ 2) : ℝ) : ℂ) *
        ∫ y, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * gam ε y *
          Complex.exp (-(Complex.I * t * ip β y))) =
      ∫ x, Ψ x * mM ψ (|t| / (2 * Real.sqrt ε)) (qq x) ∂μ := by
  have ha : ∀ β : E n, ∫ y, (∫ x, Ψ x * Complex.exp (Complex.I * t * ip y (qq x)) ∂μ) * gam ε y *
      Complex.exp (-(Complex.I * t * ip β y)) = ∫ x, Ψ x * kr ε t (qq x - β) ∂μ :=
    fun β => step_a Ψ qq hΨ hqq t ε hε β
  simp_rw [ha]
  rw [step_b Ψ qq hΨ hqq t ε hε ψ hψc hψi]
  congr 1
  funext x
  rw [step_c ψ t ε ht hε (qq x)]
end PositivityTheory.Rg.Sw.WR.D.Moll
