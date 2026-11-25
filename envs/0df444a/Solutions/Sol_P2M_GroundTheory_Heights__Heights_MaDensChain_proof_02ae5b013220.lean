-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MaDensChain_proof_02ae5b013220
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:05:27.612939+00:00
-- url     : https://prove2.me/submissions/e2247e7c-0f99-4662-a5cf-1e9a02061575

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaDensChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLeibniz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensChain
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensChain_hessC_comp_real_1b578ed93f88
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensChain_gradMat_comp_e702841e1d36
import Theorems.Thm_ReciprocityTheory_AnForm_A_maDens_cons_eq
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_cons_smul_add
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_cons_smul_fst


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
theorem _root_.solution : MaDensChain.Statement := by
  intro D φ F g z hF hg
  have hF1 : DifferentiableAt ℝ F (g z) := (hF.differentiable (by norm_num)) _
  constructor
  · rw [maDens_cons_eq, maDens_cons_eq, hessC_comp_real F g z hF hg]
    unfold gradDens
    rw [mdisc_cons_smul_add]
    simp only [Complex.add_re, Complex.re_ofReal_mul]
    ring
  · unfold gradDens
    rw [gradMat_comp F g z hF1 (hg.differentiableAt (by norm_num)), mdisc_cons_smul_fst]
    simp only [Complex.re_ofReal_mul]
    ring
end GroundTheory.Heights₂.Heights.MaDensChain
