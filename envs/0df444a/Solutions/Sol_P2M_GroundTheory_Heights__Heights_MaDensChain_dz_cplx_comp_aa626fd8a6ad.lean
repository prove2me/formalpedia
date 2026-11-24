-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MaDensChain_dz_cplx_comp_aa626fd8a6ad
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:15.295265+00:00
-- url     : https://prove2.me/submissions/85da45b0-133e-4d2a-876e-d073e5452768

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaDensChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLeibniz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensChain
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MaDensChain_fderiv_comp_real_7cfce8fb8fcd
import Theorems.Thm_ReciprocityTheory_AnForm_A_dz_cplx


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
theorem _root_.solution (j : Fin D) (h : ℝ → ℝ) (g : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hh : DifferentiableAt ℝ h (g y)) (hg : DifferentiableAt ℝ g y) :
    dz j (cplx (h ∘ g)) y = ((deriv h (g y) : ℝ) : ℂ) * dz j (cplx g) y := by
  rw [dz_cplx, dz_cplx, fderiv_comp_real h g y hh hg]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring
end GroundTheory.Heights₂.Heights.MaDensChain
