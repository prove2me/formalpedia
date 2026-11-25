-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MaDensLeibniz_hessC_sq_half_d7954601c4d4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:56.018387+00:00
-- url     : https://prove2.me/submissions/06574138-3ce0-4d45-88b1-aded4853bea2

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLeibniz
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLeibniz_exists_open_contDiffOn_a9d9b6239b52
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLeibniz_contDiffAt_cplx_f7ca67113b6f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLeibniz_dzb_cplx_sq_half_cccea07f6850
import Theorems.Thm_ReciprocityTheory_AnForm_A_differentiableAt_dzb
import Theorems.Thm_ReciprocityTheory_AnForm_A_dz_congr
import Theorems.Thm_ReciprocityTheory_AnForm_A_dz_mul
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessCDz_thm


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
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.MaDensLeibniz
variable {D : ℕ}
namespace GroundTheory.Heights₂.Heights.MaDensLeibniz
theorem _root_.solution (f : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hf : ContDiffAt ℝ 2 f z) :
    hessC (fun y => f y ^ 2 / 2) z = (f z : ℂ) • hessC f z + gradMat f f z := by
  obtain ⟨U, hU, hzU, hfU, -⟩ := exists_open_contDiffOn f f z hf hf
  ext j k
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hessCDz_thm D _ U hU ((hfU.pow 2).div_const 2) z hzU j k, hessCDz_thm D f U hU hfU z hzU j k]
  have hev : dzb k (cplx fun y => f y ^ 2 / 2) =ᶠ[𝓝 z] fun y => cplx f y * dzb k (cplx f) y := by
    filter_upwards [hU.mem_nhds hzU] with y hy
    exact dzb_cplx_sq_half k f y ((hfU.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
  have hF := (contDiffAt_cplx hf).differentiableAt (n := 2) (by norm_num)
  have hF' := differentiableAt_dzb (j := k) (contDiffAt_cplx hf)
  rw [dz_congr hev, dz_mul hF hF']
  simp only [gradMat, cplx]
  ring
end GroundTheory.Heights₂.Heights.MaDensLeibniz
