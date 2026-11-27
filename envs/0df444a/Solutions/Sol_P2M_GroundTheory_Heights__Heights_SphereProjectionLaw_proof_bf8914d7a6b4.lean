-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_proof_bf8914d7a6b4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:10:34.146382+00:00
-- url     : https://prove2.me/submissions/b2fa78d8-0c35-4b93-97df-c4125f032d07

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSphereProjectionLaw
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_coordAlong_smul_7c3936e57c10
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_coordAlong_sub_865ad3ae7aa7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_coordAlong_self_b948cf6b7db2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_std_norm_947a28c9cbcb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_sum_norm_sq_smul_e9836557e9c9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_sum_norm_sq_sub_ddb4e8b7c1b8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_exists_unitary_first_c8c74f914855
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereProjectionLaw_span_singleton_ne_top_f9fb01faf79a

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
open MeasureTheory ProbabilityTheory
noncomputable section
open SphereProjectionLaw
namespace GroundTheory.Heights₂.Heights
namespace SphereProjectionLaw
theorem _root_.solution (h1 : SphereLawBasic.Statement) (h2 : SphereLawUnitary.Statement)
    (h3 : SphereLawFirstCoord.Statement) (h4 : SpherePhase.Statement) :
    SphereProjectionLaw.Statement := by
  intro N p hp
  refine ⟨fun hN ↦ ?_, fun hN ↦ ⟨?_, h4 N p hp hN, ?_⟩⟩
  ·
    subst hN
    filter_upwards [(h1 1 le_rfl).2.1] with z hz
    simp only [Fin.sum_univ_one] at hz hp
    have hz1 : ‖z 0‖ = 1 := by nlinarith [norm_nonneg (z 0)]
    have hp1 : ‖p 0‖ = 1 := by nlinarith [norm_nonneg (p 0)]
    simp [coordAlong, hz1, hp1]
  ·
    have hnull := measure_eq_zero_iff_ae_notMem.mp
      ((h1 N (by omega)).2.2 _ (span_singleton_ne_top hN p))
    filter_upwards [(h1 N (by omega)).2.1, hnull] with z hz hzS
    set a := coordAlong p z with ha
    set w := z - a • p with hw
    have hw0 : w ≠ 0 := by
      intro h
      apply hzS
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      exact ⟨a, (sub_eq_zero.mp h).symm⟩
    have hsq : ∑ j, ‖w j‖ ^ 2 = 1 - ‖a‖ ^ 2 := sum_norm_sq_sub hp hz
    have hpos : 0 < ∑ j, ‖w j‖ ^ 2 := by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hw0
      calc (0 : ℝ) < ‖w j‖ ^ 2 := by positivity
        _ ≤ ∑ j, ‖w j‖ ^ 2 :=
          Finset.single_le_sum (f := fun j ↦ ‖w j‖ ^ 2) (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ j)
    set s := √(1 - ‖a‖ ^ 2) with hs
    have hs0 : 0 < s := Real.sqrt_pos.mpr (hsq ▸ hpos)
    have hss : s ^ 2 = 1 - ‖a‖ ^ 2 := Real.sq_sqrt (hsq ▸ hpos.le)
    have hdir : orthoDir p z = ((s : ℂ))⁻¹ • w := by
      rw [orthoDir, std_norm, ← ha, ← hw, hsq]
    have hwp : coordAlong p w = 0 := by
      rw [hw, coordAlong_sub, coordAlong_smul, coordAlong_self hp, mul_one, sub_self]
    refine ⟨?_, ?_, ?_⟩
    · rw [hdir, smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hs0.ne'), one_smul, hw,
        add_sub_cancel]
    · rw [hdir, coordAlong_smul, hwp, mul_zero]
    · rw [hdir, std_norm, sum_norm_sq_smul, hsq, ← hss, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg hs0.le, inv_pow, inv_mul_cancel₀ (pow_pos hs0 2).ne', Real.sqrt_one]
  ·
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
    obtain ⟨U, hU, hU0⟩ := exists_unitary_first p hp
    have hf : (fun z ↦ ‖coordAlong p z‖ ^ 2) =
        (fun z : Fin (m + 1) → ℂ ↦ ‖z ⟨0, by omega⟩‖ ^ 2) ∘ U := by
      funext z
      simp [hU0]
    have hUm : Measurable U := U.continuous_of_finiteDimensional.measurable
    have hgm : Measurable fun z : Fin (m + 1) → ℂ ↦ ‖z ⟨0, by omega⟩‖ ^ 2 :=
      ((continuous_apply _).norm.pow 2).measurable
    rw [hf, ← Measure.map_map hgm hUm, h2 _ U hU, h3 _ hN]
end SphereProjectionLaw
end GroundTheory.Heights₂.Heights
