-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_tensQ_pluck_84a22b3e2f66
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:45:16.373621+00:00
-- url     : https://prove2.me/submissions/0fce5ccf-1627-41af-a550-35ff9b939c26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PXiMetric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_kron_pair_244dde65b244
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_hermG_swap_34994cfc3a37

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
open scoped ComplexOrder
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
variable {κ : Type} [Fintype κ]
namespace GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
theorem _root_.solution {G : Matrix κ κ ℂ} (hG : G.IsHermitian) (a b : κ → ℂ) :
    tensQ G (fun p => a p.1 * b p.2 - a p.2 * b p.1) =
      2 * ((hermG G a a).re * (hermG G b b).re - ‖hermG G a b‖ ^ 2) := by
  have hs : (fun p : κ × κ => a p.1 * b p.2 - a p.2 * b p.1) =
      (fun p => a p.1 * b p.2) - (fun p => b p.1 * a p.2) := by
    funext p
    simp only [Pi.sub_apply]
    ring
  have hA : (hermG G a a).im = 0 := Complex.conj_eq_iff_im.1 (hermG_swap hG a a).symm
  have hB : (hermG G b b).im = 0 := Complex.conj_eq_iff_im.1 (hermG_swap hG b b).symm
  rw [tensQ, hs, star_sub, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, kron_pair, kron_pair,
    kron_pair, kron_pair, hermG_swap hG a b]
  simp only [Complex.sub_re, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, hA, hB,
    Complex.sq_norm, Complex.normSq_apply]
  ring
end GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
