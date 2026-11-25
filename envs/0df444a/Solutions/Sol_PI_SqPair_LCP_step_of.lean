-- Prove2me | solution 1 for PI.SqPair.LCP.step_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:34:15.709686+00:00
-- url     : https://prove2.me/submissions/4d4889f3-469c-4929-a747-8f13689619ff

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_StepGlue
import Theorems.Thm_PI_SqPair_LCP_sg_hf_add_left
import Theorems.Thm_PI_SqPair_LCP_sg_hf_add_right
import Theorems.Thm_PI_SqPair_LCP_sg_hf_smul_left
import Theorems.Thm_PI_SqPair_LCP_sg_hf_smul_right
import Theorems.Thm_PI_SqPair_LCP_sg_hf_star

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LCP
namespace PI.SqPair.LCP
theorem _root_.solution (h5 : Select) (h8 : Plane) (h6 : Split) : Step := by
  intro R _ _ R₀ _ ϖ hin κ _ _ A A' h k hP hnb
  haveI := hin.dom
  obtain ⟨a, x, y, ha0, hak, hxy, ⟨c, hc⟩, ⟨v, hv⟩, ⟨w, hw⟩⟩ := h5 R R₀ ϖ hin (Fin 2 ⊕ κ) A A' h k hP hnb
  have hA : Aᴴ = A := hP.1.1
  have hsϖ : star ϖ = ϖ := (hin.fix ϖ).1 hin.pi_mem
  have hyx : hf A y x = 1 := by rw [← sg_hf_star hA x y, hxy, star_one]
  have hpow0 : ϖ ^ (2 * a) ≠ 0 := pow_ne_zero _ hin.pi_ne
  have hcR : c ∈ R₀ := by
    rw [hin.fix]
    have h1 := sg_hf_star hA x x
    rw [hc, star_mul, star_pow, hsϖ] at h1
    exact mul_left_cancel₀ hpow0 (by rw [mul_comm, h1])
  have hβR : hf A y y ∈ R₀ := (hin.fix _).2 (sg_hf_star hA y y)
  have hϖm : (⟨ϖ, hin.pi_mem⟩ : R₀) ∈ IsLocalRing.maximalIdeal R₀ := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hin.pi_nonunit (hu.map R₀.subtype)
  have hmα : ϖ ^ (2 * a) * c ∈ R₀ := R₀.mul_mem (R₀.pow_mem hin.pi_mem _) hcR
  have hαm : (⟨ϖ ^ (2 * a) * c, hmα⟩ : R₀) ∈ IsLocalRing.maximalIdeal R₀ := by
    have e : (⟨ϖ ^ (2 * a) * c, hmα⟩ : R₀) = ⟨ϖ, hin.pi_mem⟩ ^ (2 * a) * ⟨c, hcR⟩ := Subtype.ext (by simp)
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hϖm _ (by omega))
  obtain ⟨W, hWdet, hW, s', hs'⟩ := h8 R R₀ ϖ hin ⟨ϖ ^ (2 * a) * c, hmα⟩ ⟨hf A y y, hβR⟩ hαm
  have e00 := congrFun (congrFun hW 0) 0
  have e11 := congrFun (congrFun hW 1) 1
  have e01 := congrFun (congrFun hW 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, hyp, conjTranspose_apply] at e00 e11 e01 hs'
  have hk : ϖ ^ (k + a) = ϖ ^ (2 * a) * ϖ ^ (k - a) := by rw [← pow_add]; congr 1; omega

  refine h6 R R₀ ϖ hin κ A A' h k a hP hak (W 0 0 • x + W 1 0 • y) (W 0 1 • x + W 1 1 • y) (W 0 0 • v + (s' * c) • w) ((W 0 1 * ϖ ^ (2 * a)) • v + W 1 1 • w) ?_ ?_ ?_ ?_ ?_
  · simp only [sg_hf_add_left, sg_hf_add_right, sg_hf_smul_left, sg_hf_smul_right, hxy, hyx, hc]
    linear_combination e00
  · simp only [sg_hf_add_left, sg_hf_add_right, sg_hf_smul_left, sg_hf_smul_right, hxy, hyx, hc]
    linear_combination e11
  · simp only [sg_hf_add_left, sg_hf_add_right, sg_hf_smul_left, sg_hf_smul_right, hxy, hyx, hc]
    linear_combination e01
  · rw [mulVec_add, mulVec_smul, mulVec_smul, hv, hw, hk, hs']
    simp only [smul_add, smul_smul]
    congr 1 <;> congr 1 <;> ring
  · rw [mulVec_add, mulVec_smul, mulVec_smul, hv, hw, hk]
    simp only [smul_add, smul_smul]
    congr 1 <;> congr 1 <;> ring
end PI.SqPair.LCP
