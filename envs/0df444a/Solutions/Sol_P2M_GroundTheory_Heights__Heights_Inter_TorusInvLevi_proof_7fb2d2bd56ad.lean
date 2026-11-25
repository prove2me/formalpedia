-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_TorusInvLevi_proof_7fb2d2bd56ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:30:01.582825+00:00
-- url     : https://prove2.me/submissions/292bcae3-c80f-4829-a561-b6e474fea220

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StTorusInvLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_FubiniLevi
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PTorusInvLevi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_leviForm_phi_nonneg_f9953347f1be
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_chart_bound_14af4c518f29
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_levi_bound_compact_c78187bb777a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_norm_mul_self_le_sum_96ee2cbc5748
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_isOpen_noZeroBlock_d982401b3f8e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_levi_Phi_d5cfcffc1145
import Theorems.Thm_ReciprocityTheory_AnForm_levi_comp
import Theorems.Thm_ReciprocityTheory_AnForm_levi_congr


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open TorusInvariantLevi
namespace GroundTheory.Heights₂.Heights.Inter
namespace TorusInvLevi
theorem _root_.solution : TorusInvLevi.Statement := by
  intro K _ ι _ u hu hinv
  have hUo := isOpen_noZeroBlock (ι := ι)
  set U := {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} with hUdef

  set Q : Set ((Σ k, ι k) → ℂ) := Metric.closedBall 0 1 ∩ {x | ∀ k, ∃ j, x ⟨k, j⟩ = 1} with hQ
  have hQc : IsCompact Q := by
    have hcl : IsClosed {x : (Σ k, ι k) → ℂ | ∀ k, ∃ j, x ⟨k, j⟩ = 1} := by
      have h : {x : (Σ k, ι k) → ℂ | ∀ k, ∃ j, x ⟨k, j⟩ = 1} = ⋂ k, ⋃ j, {x | x ⟨k, j⟩ = 1} := by
        ext x
        simp
      rw [h]
      exact isClosed_iInter fun k => isClosed_iUnion_of_finite fun j =>
        isClosed_eq (continuous_apply _) continuous_const
    exact (isCompact_closedBall 0 1).inter_right hcl
  have hQU : Q ⊆ U := fun x hx k => by
    obtain ⟨j, hj⟩ := hx.2 k
    exact ⟨j, by rw [hj]; exact one_ne_zero⟩
  obtain ⟨M, hM0, hM⟩ := levi_bound_compact hUo hu hQc hQU
  set B : ℝ := ∑ k, 4 * (Fintype.card (ι k) : ℝ) ^ 2 with hB
  refine ⟨M * B, fun z hz w => ?_⟩

  have hmax : ∀ k, ∃ j, ∀ j', ‖z ⟨k, j'⟩‖ ≤ ‖z ⟨k, j⟩‖ := fun k => by
    obtain ⟨j0, _⟩ := hz k
    obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun j => ‖z ⟨k, j⟩‖)
      ⟨j0, Finset.mem_univ _⟩
    exact ⟨j, fun j' => hj j' (Finset.mem_univ _)⟩
  choose i hi using hmax
  have hne : ∀ k, z ⟨k, i k⟩ ≠ 0 := fun k => by
    obtain ⟨j0, hj0⟩ := hz k
    intro h0
    have h := hi k j0
    rw [h0, norm_zero] at h
    exact hj0 (norm_le_zero_iff.1 h)
  set τ : ((Σ k, ι k) → ℂ) → ((Σ k, ι k) → ℂ) := fun y p => y p * (y ⟨p.1, i p.1⟩)⁻¹ with hτdef
  have hτa : AnalyticAt ℂ τ z := analyticAt_pi_iff.2 fun p =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι k) => ℂ) p).analyticAt z).mul
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι k) => ℂ) ⟨p.1, i p.1⟩).analyticAt
        z).inv (hne p.1))
  have hτQ : τ z ∈ Q := by
    refine ⟨?_, fun k => ⟨i k, ?_⟩⟩
    · rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      rintro ⟨k, j⟩
      simp only [hτdef, norm_mul, norm_inv]
      rw [mul_inv_le_iff₀ (norm_pos_iff.2 (hne k)), one_mul]
      exact hi k j
    · simp only [hτdef]
      exact mul_inv_cancel₀ (hne k)

  have hev : u ∘ τ =ᶠ[𝓝 z] u := by
    have hV : IsOpen {y : (Σ k, ι k) → ℂ | ∀ k, y ⟨k, i k⟩ ≠ 0} := by
      have h : {y : (Σ k, ι k) → ℂ | ∀ k, y ⟨k, i k⟩ ≠ 0} = ⋂ k, {y | y ⟨k, i k⟩ ≠ 0} := by
        ext y
        simp
      rw [h]
      exact isOpen_iInter_of_finite fun k => isOpen_ne_fun (continuous_apply _) continuous_const
    filter_upwards [hV.mem_nhds hne] with y hy
    have h := hinv (fun k => (y ⟨k, i k⟩)⁻¹) y (fun k => inv_ne_zero (hy k)) (fun k => ⟨i k, hy k⟩)
    simp only [Function.comp_apply, hτdef]
    rw [← h]
    congr 1
    funext p
    ring
  have hu' : ContDiffAt ℝ 2 u (τ z) := hu.contDiffAt (hUo.mem_nhds (hQU hτQ))
  have hlevi : leviForm u z w = ReciprocityTheory.AnForm.levi u (τ z) (fderiv ℂ τ z w) := by
    show ReciprocityTheory.AnForm.levi u z w = _
    rw [← ReciprocityTheory.AnForm.levi_congr hev w, ReciprocityTheory.AnForm.levi_comp w hτa hu']

  have hD : ∀ p, fderiv ℂ τ z w p =
      (z ⟨p.1, i p.1⟩ * w p - z p * w ⟨p.1, i p.1⟩) / z ⟨p.1, i p.1⟩ ^ 2 := by
    intro p
    have hinvq : ∀ q : (Σ k, ι k), z q ≠ 0 → HasFDerivAt (fun y : (Σ k, ι k) → ℂ => (y q)⁻¹) _ z :=
      fun q hq => (hasFDerivAt_inv hq).comp z (hasFDerivAt_apply (𝕜 := ℂ) q z)
    have hc : ∀ p : (Σ k, ι k), HasFDerivAt (fun y : (Σ k, ι k) → ℂ => y p * (y ⟨p.1, i p.1⟩)⁻¹) _ z :=
      fun p => (hasFDerivAt_apply (𝕜 := ℂ) p z).mul (hinvq _ (hne p.1))
    have key : fderiv ℂ τ z = ContinuousLinearMap.pi fun p =>
        fderiv ℂ (fun y : (Σ k, ι k) → ℂ => y p * (y ⟨p.1, i p.1⟩)⁻¹) z :=
      fderiv_pi fun p => (hc p).differentiableAt
    rw [key, ContinuousLinearMap.pi_apply, (hc p).fderiv]
    have hq := hne p.1
    simp
    field_simp
    ring

  have hS : ∀ k, sqSum (blk k z) ≠ 0 := by
    intro k
    refine (lt_of_lt_of_le (pow_pos (norm_pos_iff.2 (hne k)) 2) ?_).ne'
    exact Finset.single_le_sum (f := fun j => ‖blk k z j‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ (i k))
  have hLnn : ∀ k, 0 ≤ leviForm phi (blk k z) (blk k w) := fun k => leviForm_phi_nonneg (hS k) _
  have hblock : ∀ k, ∑ l, ‖fderiv ℂ τ z w ⟨k, l⟩‖ ^ 2 ≤
      4 * (Fintype.card (ι k) : ℝ) ^ 2 * leviForm phi (blk k z) (blk k w) := by
    intro k
    calc _ = ∑ l, ‖(blk k z (i k) * blk k w l - blk k z l * blk k w (i k)) / blk k z (i k) ^ 2‖ ^ 2 :=
          Finset.sum_congr rfl fun l _ => by rw [hD]; rfl
      _ ≤ _ := chart_bound (fun j => hi k j) (hne k)
  have hv := hM (τ z) hτQ (fderiv ℂ τ z w)
  have hsup := norm_mul_self_le_sum (fderiv ℂ τ z w)
  have hsplit : ∑ p, ‖fderiv ℂ τ z w p‖ ^ 2 = ∑ k, ∑ l, ‖fderiv ℂ τ z w ⟨k, l⟩‖ ^ 2 :=
    Fintype.sum_sigma _
  rw [hlevi, levi_Phi hz w]
  calc _ ≤ M * (‖fderiv ℂ τ z w‖ * ‖fderiv ℂ τ z w‖) := hv
    _ ≤ M * ∑ k, ∑ l, ‖fderiv ℂ τ z w ⟨k, l⟩‖ ^ 2 := by
      rw [← hsplit]
      exact mul_le_mul_of_nonneg_left hsup hM0
    _ ≤ M * ∑ k, 4 * (Fintype.card (ι k) : ℝ) ^ 2 * leviForm phi (blk k z) (blk k w) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hblock k) hM0
    _ ≤ M * ∑ k, B * leviForm phi (blk k z) (blk k w) := by
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) hM0
      refine mul_le_mul_of_nonneg_right ?_ (hLnn k)
      exact Finset.single_le_sum (f := fun k => 4 * (Fintype.card (ι k) : ℝ) ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ k)
    _ = M * B * ∑ k, leviForm phi (blk k z) (blk k w) := by
      rw [← Finset.mul_sum]
      ring
end TorusInvLevi
end GroundTheory.Heights₂.Heights.Inter
