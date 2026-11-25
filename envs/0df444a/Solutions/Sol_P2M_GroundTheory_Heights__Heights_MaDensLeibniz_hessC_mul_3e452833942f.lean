-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MaDensLeibniz_hessC_mul_3e452833942f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:11:42.88883+00:00
-- url     : https://prove2.me/submissions/addb3cff-12af-4bdf-9338-6976c5e0e8ee

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLeibniz
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLeibniz_exists_open_contDiffOn_a9d9b6239b52
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLeibniz_contDiffAt_cplx_f7ca67113b6f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLeibniz_dzb_cplx_mul_0e331d7f37e7
import Theorems.Thm_ReciprocityTheory_AnForm_A_differentiableAt_dzb
import Theorems.Thm_ReciprocityTheory_AnForm_A_dz_add
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
theorem _root_.solution (f g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hf : ContDiffAt ℝ 2 f z)
    (hg : ContDiffAt ℝ 2 g z) :
    hessC (fun y => f y * g y) z =
      (f z : ℂ) • hessC g z + (g z : ℂ) • hessC f z + gradMat f g z + gradMat g f z := by
  obtain ⟨U, hU, hzU, hfU, hgU⟩ := exists_open_contDiffOn f g z hf hg
  ext j k
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hessCDz_thm D _ U hU (hfU.mul hgU) z hzU j k, hessCDz_thm D f U hU hfU z hzU j k,
    hessCDz_thm D g U hU hgU z hzU j k]
  have hev : dzb k (cplx fun y => f y * g y) =ᶠ[𝓝 z]
      fun y => cplx f y * dzb k (cplx g) y + cplx g y * dzb k (cplx f) y := by
    filter_upwards [hU.mem_nhds hzU] with y hy
    exact dzb_cplx_mul k f g y ((hfU.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
      ((hgU.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
  have hF := (contDiffAt_cplx hf).differentiableAt (n := 2) (by norm_num)
  have hG := (contDiffAt_cplx hg).differentiableAt (n := 2) (by norm_num)
  have hF' := differentiableAt_dzb (j := k) (contDiffAt_cplx hf)
  have hG' := differentiableAt_dzb (j := k) (contDiffAt_cplx hg)
  rw [dz_congr hev, dz_add (hF.fun_mul hG') (hG.fun_mul hF'), dz_mul hF hG', dz_mul hG hF']
  simp only [gradMat, cplx]
  ring
end GroundTheory.Heights₂.Heights.MaDensLeibniz
