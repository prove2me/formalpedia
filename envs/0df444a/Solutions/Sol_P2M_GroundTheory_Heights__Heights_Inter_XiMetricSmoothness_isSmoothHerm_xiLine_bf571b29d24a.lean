-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_isSmoothHerm_xiLine_bf571b29d24a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:27.647133+00:00
-- url     : https://prove2.me/submissions/3d5b82f0-805f-4acd-8d04-52e3739dfda1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PXiMetric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiff_dnorm_1d46eff272bd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiff_ypow_adbb8a5939c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiffOn_hv_c131b75442aa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiffOn_numF_252bdfbfa77d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_XiMetricSmoothness_contDiffOn_remR_a4c875064d53

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
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {G : YPt ι ν κ → Matrix κ κ ℂ} {N : ℕ}
  {F : ι → ν → κ → κ → MRing (T.yyIdx ι ν κ)} {q : ℕ} {r : Fin q → MRing (T.yyIdx ι ν κ)} {b : Fin q → T.YBlk → ℕ}
namespace GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
theorem _root_.solution (hG : IsEEMetric G)
    (hF : ∀ i l k m, IsMultiHomog (F i l k m) (Pi.single T.YBlk.base (N + 3)))
    (hr : ∀ j, IsMultiHomog (r j) (b j)) (hrl : ∀ j, b j .line = 0)
    (hcov : ∀ w : YPt ι ν κ, (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → (∀ j, evC (r j) w = 0) → ∃ i l k m, evC (F i l k m) w ≠ 0) :
    IsSmoothHerm (xiLine hG hF hr hrl hcov) := by
  unfold IsSmoothHerm
  show ContDiffOn ℝ _ (xiH G N F r b) (goodY ι ν κ)
  unfold xiH
  have hrat : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ratio G N F r b) (goodY ι ν κ) := by
    unfold ratio
    refine ((contDiffOn_numF hG F).add (contDiffOn_remR N r b)).div
      (contDiffOn_const.mul ((contDiff_ypow N).mul contDiff_dnorm).contDiffOn) fun w hw => ?_
    exact (mul_pos two_pos (mul_pos (ypow_pos hw N) (dnorm_pos hw))).ne'
  exact (hrat.sqrt fun w hw => (ratio_pos hG hcov hw).ne').div (contDiffOn_hv hG) fun w hw => (hv_pos hw hG.1).ne'
end GroundTheory.Heights₂.Heights.Inter.XiMetricSmoothness
