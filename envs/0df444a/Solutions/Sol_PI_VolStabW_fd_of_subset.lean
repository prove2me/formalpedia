-- Prove2me | solution 1 for PI.VolStabW.fd_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:01:38.068867+00:00
-- url     : https://prove2.me/submissions/ca53b264-bb03-4bb9-8ed3-2cf253ee6f91

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
theorem _root_.solution {Γ : Subgroup G} [Countable Γ] {μ : Measure G} [μ.IsMulLeftInvariant]
    {s t : Set G} (h : IsFundamentalDomain Γ s μ) (hts : t ⊆ s) (ht : MeasurableSet t)
    (hnull : μ (s \ t) = 0) : IsFundamentalDomain Γ t μ where
  nullMeasurableSet := ht.nullMeasurableSet
  ae_covers := by
    have h1 : ∀ (γ : Γ), ∀ᵐ g ∂μ, g ∉ (fun g => (γ : G) * g) ⁻¹' (s \ t) := fun γ =>
      measure_eq_zero_iff_ae_notMem.1 (by rw [measure_preimage_mul]; exact hnull)
    have h2 := (ae_all_iff (ι := Γ)).2 h1
    filter_upwards [h.ae_covers, h2] with g hg h3
    obtain ⟨γ, hγ⟩ := hg
    refine ⟨γ, ?_⟩
    by_contra hn
    exact h3 γ ⟨hγ, hn⟩
  aedisjoint := fun γ γ' hne =>
    measure_mono_null (inter_subset_inter (smul_set_mono hts) (smul_set_mono hts)) (h.aedisjoint hne)
end PI.VolStabW
