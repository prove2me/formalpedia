-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.GM.integ_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:16:07.794035+00:00
-- url     : https://prove2.me/submissions/35ae7495-9cb3-43af-b665-3140120d6bfb

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussM
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GM_norm_phase
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GM_continuous_evX

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
open PositivityTheory.Rg.Sw.WR.G.GM
namespace PositivityTheory.Rg.Sw.WR.G.GM
theorem _root_.solution (hI : IntegP) {ε : Fin m → Bool} {c t : ℝ} (hc : 0 < c) {b : Matrix (Fin n) (Fin n) ℂ}
    (hb : b.IsHermitian) (P : PX m n) :
    Integrable fun x => evX P x * gs c x * Complex.exp (Complex.I * t * (b * gramX ε x).trace) := by
  refine (hI m n c hc P).mono ?_ (Filter.Eventually.of_forall fun x => ?_)
  · refine (hI m n c hc P).aestronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_)
    refine Complex.continuous_exp.comp (continuous_const.mul ?_)
    refine (continuous_const.matrix_mul ?_).matrix_trace
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact continuous_evX _
  · rw [norm_mul, norm_phase hb, mul_one]
end PositivityTheory.Rg.Sw.WR.G.GM
