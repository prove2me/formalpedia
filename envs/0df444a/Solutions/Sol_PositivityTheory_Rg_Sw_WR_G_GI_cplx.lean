-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.GI.cplx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:59:59.897053+00:00
-- url     : https://prove2.me/submissions/4f4c2fb3-8256-4e64-8271-32c4b95d9e42

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_NormMono
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GI_abs_pow_exp
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GI_add_pow_le

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G PositivityTheory.Rg.Sw.WR.G.GI
open PositivityTheory.Rg.Sw
namespace PositivityTheory.Rg.Sw.WR.G.GI
theorem _root_.solution (c : ℝ) (hc : 0 < c) (k : ℕ) :
    Integrable fun z : ℂ => ‖z‖ ^ k * Real.exp (-c * ‖z‖ ^ 2) := by
  have hP : Integrable (fun p : ℝ × ℝ => (2 : ℝ) ^ k * ((|p.1| ^ k * Real.exp (-c * p.1 ^ 2)) *
      Real.exp (-c * p.2 ^ 2) + Real.exp (-c * p.1 ^ 2) * (|p.2| ^ k * Real.exp (-c * p.2 ^ 2)))) := by
    refine Integrable.const_mul (Integrable.add ?_ ?_) _
    · exact (abs_pow_exp c hc k).mul_prod (integrable_exp_neg_mul_sq hc)
    · exact (integrable_exp_neg_mul_sq hc).mul_prod (abs_pow_exp c hc k)
  have hC : Integrable (fun z : ℂ => (2 : ℝ) ^ k * ((|z.re| ^ k * Real.exp (-c * z.re ^ 2)) *
      Real.exp (-c * z.im ^ 2) + Real.exp (-c * z.re ^ 2) * (|z.im| ^ k * Real.exp (-c * z.im ^ 2)))) := by
    have := (Complex.volume_preserving_equiv_real_prod.integrable_comp_emb
      Complex.measurableEquivRealProd.measurableEmbedding).mpr hP
    simpa [Function.comp_def, Complex.measurableEquivRealProd] using this
  refine hC.mono' (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
  have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have he : Real.exp (-c * ‖z‖ ^ 2) = Real.exp (-c * z.re ^ 2) * Real.exp (-c * z.im ^ 2) := by
    rw [hz, ← Real.exp_add]; ring_nf
  have h1 : ‖z‖ ^ k ≤ 2 ^ k * (|z.re| ^ k + |z.im| ^ k) :=
    (pow_le_pow_left₀ (norm_nonneg z) (Complex.norm_le_abs_re_add_abs_im z) k).trans
      (add_pow_le _ _ (abs_nonneg _) (abs_nonneg _) k)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), he]
  have e1 := Real.exp_pos (-c * z.re ^ 2)
  have e2 := Real.exp_pos (-c * z.im ^ 2)
  calc ‖z‖ ^ k * (Real.exp (-c * z.re ^ 2) * Real.exp (-c * z.im ^ 2))
      ≤ 2 ^ k * (|z.re| ^ k + |z.im| ^ k) * (Real.exp (-c * z.re ^ 2) * Real.exp (-c * z.im ^ 2)) := by
        gcongr
    _ = _ := by ring
end PositivityTheory.Rg.Sw.WR.G.GI
