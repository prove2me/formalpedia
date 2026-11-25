-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.Moll.tendsto_mM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:51:10.551821+00:00
-- url     : https://prove2.me/submissions/e4b181e9-4280-4b3c-ad0b-40342d0f87f2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollIdA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollId
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_continuous_gK
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_gK_nonneg
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_integrable_gK
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_integral_gK


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
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.D.Moll
theorem _root_.solution (ψ : E n → ℂ) (B : ℝ) (hB : ∀ x, ‖ψ x‖ ≤ B) (hψ : Continuous ψ) (l : ℕ → ℝ)
    (hl : Tendsto (fun k => (l k)⁻¹) atTop (𝓝 0)) (w : E n) :
    Tendsto (fun k => mM ψ (l k) w) atTop (𝓝 (ψ w)) := by
  have hlim : ψ w = ∫ v, ψ (w - (0 : ℝ) • v) * (gK (n := n) v : ℂ) := by
    simp only [zero_smul, sub_zero]
    rw [integral_const_mul, integral_complex_ofReal, integral_gK, Complex.ofReal_one, mul_one]
  rw [hlim]
  unfold mM
  refine tendsto_integral_of_dominated_convergence (fun v => B * gK (n := n) v) ?_ (integrable_gK.const_mul B) ?_ ?_
  · intro k
    exact ((by fun_prop : Continuous fun v : E n => ψ (w - (l k)⁻¹ • v)).mul
      (Complex.continuous_ofReal.comp continuous_gK)).aestronglyMeasurable
  · intro k; refine Eventually.of_forall fun v => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gK_nonneg v)]
    exact mul_le_mul_of_nonneg_right (hB _) (gK_nonneg v)
  · refine Eventually.of_forall fun v => ?_
    refine Tendsto.mul ?_ tendsto_const_nhds
    exact (hψ.tendsto _).comp (tendsto_const_nhds.sub (hl.smul_const v))
end PositivityTheory.Rg.Sw.WR.D.Moll
