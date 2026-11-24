-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MaDensChain_hessC_comp_real_1b578ed93f88
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:22.893877+00:00
-- url     : https://prove2.me/submissions/cf6ac2dd-f8a3-477e-bada-d4b071b5d6e8

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaDensChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLeibniz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensChain
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensChain_dz_cplx_comp_aa626fd8a6ad
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensChain_dzb_cplx_comp_3ae6bb027eab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLeibniz_contDiffAt_cplx_f7ca67113b6f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensLeibniz_exists_open_contDiffOn_a9d9b6239b52
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
open GroundTheory.Heights₂.Heights.MaDensChain
variable {D : ℕ}
namespace GroundTheory.Heights₂.Heights.MaDensChain
theorem _root_.solution (F : ℝ → ℝ) (g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hF : ContDiff ℝ 2 F)
    (hg : ContDiffAt ℝ 2 g z) :
    hessC (F ∘ g) z = ((deriv F (g z) : ℝ) : ℂ) • hessC g z + ((deriv (deriv F) (g z) : ℝ) : ℂ) • gradMat g g z := by
  obtain ⟨U, hU, hzU, hgU, -⟩ := MaDensLeibniz.exists_open_contDiffOn g g z hg hg
  have hF1 : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hF' : Differentiable ℝ (deriv F) :=
    (hF.deriv' (n := 1)).differentiable (by norm_num)
  ext j k
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hessCDz_thm D _ U hU (hF.comp_contDiffOn hgU) z hzU j k, hessCDz_thm D g U hU hgU z hzU j k]
  have hev : dzb k (cplx (F ∘ g)) =ᶠ[𝓝 z] fun y => cplx (deriv F ∘ g) y * dzb k (cplx g) y := by
    filter_upwards [hU.mem_nhds hzU] with y hy
    exact dzb_cplx_comp k F g y (hF1 _)
      ((hgU.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
  have hgd : DifferentiableAt ℝ g z := hg.differentiableAt (by norm_num)
  have hA : DifferentiableAt ℝ (cplx (deriv F ∘ g)) z := by
    have h : cplx (deriv F ∘ g) = fun y => Complex.ofRealCLM ((deriv F ∘ g) y) := by
      funext y; simp [cplx]
    rw [h]
    exact Complex.ofRealCLM.differentiableAt.comp z ((hF' _).comp z hgd)
  have hB := differentiableAt_dzb (j := k) (MaDensLeibniz.contDiffAt_cplx hg)
  rw [dz_congr hev, dz_mul hA hB, dz_cplx_comp j (deriv F) g z (hF' _) hgd]
  simp only [gradMat, cplx, Function.comp_apply]
  ring
end GroundTheory.Heights₂.Heights.MaDensChain
