-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_fderiv_fderiv_phi_0e0a76ba56ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:40:12.446819+00:00
-- url     : https://prove2.me/submissions/f71f40ed-9cc8-4681-9cbd-55db657d340b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_FubiniLevi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_reInner_comm_1e6caf871f47
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_reInner_self_1b2324488aab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_continuous_sqSum_68d304758819
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_hasFDerivAt_sqSum_43e986969273
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_hasFDerivAt_phi_3584397ba630
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_contDiffAt_phi_ce22939b8b91

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
variable {J : Type} [Fintype J]
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
theorem _root_.solution {z : J → ℂ} (hz : sqSum z ≠ 0) (u : J → ℂ) :
    fderiv ℝ (fderiv ℝ phi) z u u =
      sqSum u / sqSum z - 2 * reInner z u ^ 2 / sqSum z ^ 2 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ phi) z :=
    ((contDiffAt_phi hz (n := 2)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have h1 : fderiv ℝ (fderiv ℝ phi) z u u = fderiv ℝ (fun z' => fderiv ℝ phi z' u) z u := by
    rw [fderiv_clm_apply hd (differentiableAt_const u)]
    simp
  have hopen : IsOpen {z' : J → ℂ | sqSum z' ≠ 0} := isOpen_ne_fun continuous_sqSum continuous_const
  have heq : (fun z' => fderiv ℝ phi z' u) =ᶠ[𝓝 z]
      fun z' => reInner u z' * ((fun x : ℝ => x⁻¹) ∘ sqSum) z' := by
    filter_upwards [hopen.mem_nhds hz] with z' hz'
    rw [(hasFDerivAt_phi hz').fderiv]
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, Function.comp_apply,
      reInner_comm z' u]
    ring
  have hinv := (hasFDerivAt_inv hz).comp z (hasFDerivAt_sqSum z)
  have hG := (reInner u).hasFDerivAt.mul hinv
  rw [h1, heq.fderiv_eq]
  rw [show (fun z' => reInner u z' * ((fun x : ℝ => x⁻¹) ∘ sqSum) z') =
    (⇑(reInner u) * ((fun x : ℝ => x⁻¹) ∘ sqSum)) from rfl, hG.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    smul_eq_mul, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, reInner_self, reInner_comm u z]
  field_simp
  ring
end GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
