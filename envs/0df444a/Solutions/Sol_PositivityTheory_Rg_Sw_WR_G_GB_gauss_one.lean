-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.GB.gauss_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:52:15.430329+00:00
-- url     : https://prove2.me/submissions/0a9d5c97-2134-4a02-a78a-c8652a68e0a7

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBaseA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G PositivityTheory.Rg.Sw.WR.G.GB
namespace PositivityTheory.Rg.Sw.WR.G.GB
theorem _root_.solution (w : ℂ) (hw : 0 < w.re) :
    ∫ z : ℂ, cexp (-(w * ((‖z‖ ^ 2 : ℝ) : ℂ))) = (Real.pi : ℂ) / w := by
  have h := Complex.volume_preserving_equiv_real_prod.symm
  rw [← h.integral_comp' (g := fun z : ℂ => cexp (-(w * ((‖z‖ ^ 2 : ℝ) : ℂ))))]
  have e : ∀ p : ℝ × ℝ, cexp (-(w * ((‖measurableEquivRealProd.symm p‖ ^ 2 : ℝ) : ℂ))) =
      cexp (-w * (p.1 : ℂ) ^ 2) * cexp (-w * (p.2 : ℂ) ^ 2) := by
    intro p
    rw [← Complex.exp_add]
    congr 1
    rw [measurableEquivRealProd_symm_apply, Complex.sq_norm, Complex.normSq_apply]
    push_cast
    ring
  simp_rw [e]
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    integral_prod_mul (fun x : ℝ => cexp (-w * (x : ℂ) ^ 2)) (fun x : ℝ => cexp (-w * (x : ℂ) ^ 2)),
    integral_gaussian_complex hw]
  have hne : (Real.pi : ℂ) / w ≠ 0 := by
    have : w ≠ 0 := by intro h0; rw [h0] at hw; simp at hw
    exact div_ne_zero (by exact_mod_cast Real.pi_ne_zero) this
  rw [← Complex.cpow_add _ _ hne]
  norm_num
end PositivityTheory.Rg.Sw.WR.G.GB
