-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.dirC_FP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:51:38.965659+00:00
-- url     : https://prove2.me/submissions/6948e181-339e-4bb9-a426-1d1d9797c1ae

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivFA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvXI
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvX
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivF
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_fderiv_FP_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_integrable_Fi_mul

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ}
namespace PositivityTheory.Rg.Sw.WR.D
theorem _root_.solution (hI : IntG) (hq : Continuous (qX (n := n) ε)) (hc : 0 < c) (P : PX m n)
    (v : Fin n → Fin n → ℂ) (y : E n) :
    dirC (FP ε c t P) v y =
      ∫ x, Fi ε c t P y x * (Complex.I * t) * ∑ a, ∑ b, v a b * (qX ε x a b : ℂ) := by
  unfold dirC
  rw [fderiv_FP_apply hI hq hc, fderiv_FP_apply hI hq hc, ← integral_const_mul,
    ← integral_add (integrable_Fi_mul hI hq hc P y _) ((integrable_Fi_mul hI hq hc P y _).const_mul _)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have e : ∀ a b, v a b = ((v a b).re : ℂ) + Complex.I * ((v a b).im : ℂ) := fun a b => by
    rw [mul_comm]; exact (Complex.re_add_im (v a b)).symm
  simp only [ip, Complex.ofReal_sum, Complex.ofReal_mul]
  conv_rhs => rw [show (∑ a, ∑ b, v a b * (qX ε x a b : ℂ)) =
    ∑ a, ∑ b, (((v a b).re : ℂ) + Complex.I * ((v a b).im : ℂ)) * (qX ε x a b : ℂ) from
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [← e]]
  simp only [add_mul, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  ring_nf
end PositivityTheory.Rg.Sw.WR.D
