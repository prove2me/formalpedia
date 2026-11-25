-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_norm_muFrameAt_3455c7dba5aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:47:11.190938+00:00
-- url     : https://prove2.me/submissions/daf0446e-fde7-42a4-8790-24c5d57f1109

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Values
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Weights
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_LineMu
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_valAt_line_zero_f73d453d84a3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_fb_zero_one_753582a8fa2a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_u_mul_fb_bbea5193f5c1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_fb_one_one_ne_2b6f4d840908
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_frame_first_basis_vector_d14efe5c20b0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_frame_value_daf6e30e5d32
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_gramAt_line_6c50ef986e6e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_quotNormSq_line_f2898b3301f1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_frame_d_ce0ea87b4550
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_exists_isValueAt_of_pow_mul_mem_aa197e5832ee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_mul_d91c22cfe178
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_one_841979791225
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_valAt_eq_31bc992f98c6


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix ComplexConjugate
variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])
variable {II hII}
variable {z : (Σ _ : Unit, Fin 2) → ℂ} (d : MuFrameAt (lineHodge II hII) z)
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line
theorem _root_.solution : d.norm = 1 := by
  have hzc : z ⟨(), d.c ()⟩ ≠ 0 := d.inDom.1 ()
  have hzP : z ∈ mcPts (mCoordIdeal yLine) := mem_mcPts_line.2 ⟨d.c (), hzc⟩
  have hf := d.inDom.2
  have hfr := frame_d d
  obtain ⟨v00, h00⟩ := frame_value hfr hzc hf 0 0
  obtain ⟨v11, h11⟩ := frame_value hfr hzc hf 1 1
  obtain ⟨nu, hnu⟩ := d.unit.2.1
  obtain ⟨vu, hu⟩ := exists_isValueAt_of_pow_mul_mem hzP (segreCoord_line_ne_zero (d.c ())) (fun _ => hzc) hf hnu
  have hu11 : vu * v11 = 1 := by
    have := isValueAt_mul hu h11
    rw [u_mul_fb d] at this
    exact isValueAt_one hzP this

  have hv00 : v00 ≠ 0 := by
    obtain ⟨a, ha, he⟩ := frame_first_basis_vector hfr
    have e1 := congrFun he 1
    have e0 := congrFun he 0
    simp only [Pi.single_apply, Fin.sum_univ_two, Finset.sum_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, fb_zero_one d] at e1 e0
    change (0 : Ω) = a 0 * 0 + a 1 * fb d 1 1 at e1
    have ha1 : a 1 = 0 := by
      rw [mul_zero, zero_add] at e1
      exact (mul_eq_zero.1 e1.symm).resolve_right (fb_one_one_ne d)
    change (1 : Ω) = a 0 * fb d 0 0 + a 1 * fb d 1 0 at e0
    rw [ha1, zero_mul, add_zero] at e0
    obtain ⟨na, hna⟩ := ha 0
    obtain ⟨va, hva⟩ := exists_isValueAt_of_pow_mul_mem hzP (segreCoord_line_ne_zero (d.c ()))
      (fun _ => hzc) hf hna
    have := isValueAt_mul hva h00
    rw [← e0] at this
    have h1 := isValueAt_one hzP this
    intro h
    rw [h, mul_zero] at h1
    exact zero_ne_one h1
  have hS10 : valAt yLine (fb d 0 1) z = 0 := by rw [fb_zero_one d]; exact valAt_line_zero
  have hS00 : valAt yLine (fb d 0 0) z = v00 := valAt_eq hzP h00
  have hS11 : valAt yLine (fb d 1 1) z = v11 := valAt_eq hzP h11
  have hU : valAt yLine d.u z = vu := valAt_eq hzP hu
  show ‖valAt yLine d.u z‖ * (∏ k : Unit, ‖z ⟨k, d.c k⟩‖ ^ (0 : Unit → ℤ) k) *
    ∏ _τ : Unit, Real.sqrt (quotNormSq (show 1 ≤ 2 by decide) (gramAt lineMetric (fb d) z)) = 1
  rw [gramAt_line ⟨d.c (), hzc⟩, quotNormSq_line _ (by simpa using hS10) (by simpa [hS00] using hv00)]
  simp only [Pi.zero_apply, zpow_zero, Finset.prod_const_one, mul_one, Finset.univ_unique,
    Finset.prod_singleton, Matrix.of_apply]
  rw [Real.sqrt_sq (norm_nonneg _), hU, hS11, ← norm_mul, hu11, norm_one]
end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
