-- Prove2me | solution 1 for PI.VolStabW.fd_count_ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:01:33.858288+00:00
-- url     : https://prove2.me/submissions/46a9e66d-08de-4d25-b653-a73d75ea9450

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnfoldAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open MeasureTheory Set
open scoped ENNReal Pointwise
variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
namespace PI.VolStabW
theorem _root_.solution {Γ : Subgroup G} [Countable Γ] {μ : Measure G} {s : Set G}
    (h : IsFundamentalDomain Γ s μ) :
    ∀ᵐ g ∂μ, ∑' γ : Γ, s.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * g) = 1 := by
  have hpair : ∀ᵐ g ∂μ, ∀ γ γ' : Γ, γ • g ∈ s → γ' • g ∈ s → γ = γ' := by
    rw [ae_all_iff]
    intro γ
    rw [ae_all_iff]
    intro γ'
    by_cases hγ : γ = γ'
    · exact Filter.Eventually.of_forall fun _ _ _ => hγ
    · have hd : μ (γ⁻¹ • s ∩ γ'⁻¹ • s) = 0 :=
        h.aedisjoint (show γ⁻¹ ≠ γ'⁻¹ from fun e => hγ (inv_injective e))
      filter_upwards [compl_mem_ae_iff.2 hd] with g hg h1 h2
      exact absurd ⟨Set.mem_inv_smul_set_iff.2 h1, Set.mem_inv_smul_set_iff.2 h2⟩ hg
  filter_upwards [h.ae_covers, hpair] with g hc hu
  obtain ⟨γ0, hγ0⟩ := hc
  rw [tsum_eq_single γ0]
  · exact Set.indicator_of_mem hγ0 _
  · intro γ hne
    exact Set.indicator_apply_eq_zero.2 fun hm => absurd (hu γ γ0 hm hγ0) hne
end PI.VolStabW
