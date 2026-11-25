-- Prove2me | solution 1 for PI.VolStabSW.exists_sub_osc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:55:48.170951+00:00
-- url     : https://prove2.me/submissions/ca3e8a37-cb48-41f6-888c-3da63a3ed0cc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibFour
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVGen
import Theorems.Thm_PI_VolStabSW_isOpen_inf_iInf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open MeasureTheory Topology Set Filter
open scoped Pointwise
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
namespace PI.VolStabSW
theorem _root_.solution (hNA : HasCOSub V) {φ : V → ℝ} (hc : Continuous φ)
    (hs : HasCompactSupport φ) {ε : ℝ} (hε : 0 < ε) (Λ₀ : AddSubgroup V)
    (h₀o : IsOpen (Λ₀ : Set V)) (h₀c : IsCompact (Λ₀ : Set V)) :
    ∃ Λ : AddSubgroup V, IsOpen (Λ : Set V) ∧ IsCompact (Λ : Set V) ∧ Λ ≤ Λ₀ ∧
      ∀ x z, z ∈ Λ → |φ (x + z) - φ x| < ε := by
  have hloc : ∀ x : V, ∃ W : AddSubgroup V, IsOpen (W : Set V) ∧
      ∀ w ∈ W, |φ (x + w) - φ x| < ε / 2 := by
    intro x
    have hcx : ContinuousAt (fun w => φ (x + w)) 0 :=
      (hc.comp (continuous_const.add continuous_id)).continuousAt
    have hN : {w | |φ (x + w) - φ x| < ε / 2} ∈ 𝓝 (0 : V) := by
      have h1 := hcx.preimage_mem_nhds (Metric.ball_mem_nhds _ (half_pos hε))
      filter_upwards [h1] with w hw
      simpa [Real.dist_eq] using hw
    obtain ⟨W, hWo, -, hWN⟩ := hNA _ hN
    exact ⟨W, hWo, fun w hw => hWN hw⟩
  choose W hWo hW using hloc
  have hUo : ∀ i, IsOpen ((fun y => -i + y) ⁻¹' (W i : Set V)) :=
    fun i => (hWo i).preimage (continuous_const.add continuous_id)
  have hcov : tsupport φ ⊆ ⋃ i, (fun y => -i + y) ⁻¹' (W i : Set V) := by
    intro y _
    refine Set.mem_iUnion.mpr ⟨y, ?_⟩
    show -y + y ∈ W y
    simp
  obtain ⟨t, ht⟩ := hs.elim_finite_subcover (fun i => (fun y => -i + y) ⁻¹' (W i : Set V)) hUo hcov
  have hΛo := isOpen_inf_iInf Λ₀ h₀o t W hWo
  refine ⟨Λ₀ ⊓ ⨅ i ∈ t, W i, hΛo,
    h₀c.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ hΛo)
      (SetLike.coe_subset_coe.mpr inf_le_left), inf_le_left, ?_⟩
  intro x z hz
  have hz' := hz
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_iInf] at hz'
  have hzW : ∀ i ∈ t, z ∈ W i := hz'.2
  have hzero : ∀ y, y ∉ tsupport φ → φ y = 0 := fun y hy => by
    by_contra hne
    exact hy (subset_tsupport φ (Function.mem_support.mpr hne))
  by_cases hx : x ∈ ⋃ i ∈ t, (fun y => -i + y) ⁻¹' (W i : Set V)
  · simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    have hxi' : -i + x ∈ W i := hxi
    have h1 := hW i (-i + x) hxi'
    have h2 := hW i (-i + (x + z)) (by
      have e : -i + (x + z) = (-i + x) + z := by abel
      rw [e]
      exact (W i).add_mem hxi' (hzW i hi))
    simp only [add_neg_cancel_left] at h1 h2
    rw [abs_lt] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · have hxz : x + z ∉ ⋃ i ∈ t, (fun y => -i + y) ⁻¹' (W i : Set V) := by
      intro hc'
      apply hx
      simp only [Set.mem_iUnion] at hc' ⊢
      obtain ⟨i, hi, hxi⟩ := hc'
      refine ⟨i, hi, ?_⟩
      have hxi' : -i + (x + z) ∈ W i := hxi
      show -i + x ∈ W i
      have e : -i + x = (-i + (x + z)) + -z := by abel
      rw [e]
      exact (W i).add_mem hxi' ((W i).neg_mem (hzW i hi))
    rw [hzero x (fun h => hx (ht h)), hzero (x + z) (fun h => hxz (ht h))]
    simpa using hε
end PI.VolStabSW
