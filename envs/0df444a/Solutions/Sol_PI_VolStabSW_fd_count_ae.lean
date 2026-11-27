-- Prove2me | solution 1 for PI.VolStabSW.fd_count_ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:18:12.494313+00:00
-- url     : https://prove2.me/submissions/cb164350-f006-412d-937a-6546c4db7cb6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_UnfoldAbs

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
open MeasureTheory Set
open scoped ENNReal Pointwise
variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
namespace PI.VolStabSW
theorem _root_.solution {Γ : Subgroup G} [Countable Γ] {μ : Measure G} {s : Set G}
    (h : IsFundamentalDomain Γ s μ) :
    ∀ᵐ g ∂μ, ∑' γ : Γ, s.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * g) = 1 := by
  classical
  have huniq : ∀ᵐ x ∂μ, ∀ γ γ' : Γ, (γ : G) * x ∈ s → (γ' : G) * x ∈ s → γ = γ' := by
    rw [ae_all_iff]
    intro γ
    rw [ae_all_iff]
    intro γ'
    by_cases hg : γ = γ'
    · exact Filter.Eventually.of_forall fun _ _ _ => hg
    · have hd := h.aedisjoint (show γ⁻¹ ≠ γ'⁻¹ from fun e => hg (inv_injective e))
      refine ae_iff.mpr (measure_mono_null ?_ hd)
      intro x hx
      simp only [Set.mem_setOf_eq, _root_.not_imp] at hx
      obtain ⟨h1, h2, -⟩ := hx
      refine ⟨Set.mem_smul_set_iff_inv_smul_mem.mpr ?_, Set.mem_smul_set_iff_inv_smul_mem.mpr ?_⟩
      · simpa [Subgroup.smul_def] using h1
      · simpa [Subgroup.smul_def] using h2
  filter_upwards [h.ae_covers, huniq] with x hx hu
  obtain ⟨γ0, hγ0⟩ := hx
  have h0 : (γ0 : G) * x ∈ s := by simpa [Subgroup.smul_def] using hγ0
  rw [tsum_eq_single γ0]
  · simp [Set.indicator_of_mem h0]
  · intro γ hγ
    simp only [Set.indicator_apply]
    split_ifs with hm
    · exact absurd (hu γ γ0 hm h0) hγ
    · rfl
end PI.VolStabSW
