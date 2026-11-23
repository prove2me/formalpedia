-- Prove2me | solution 1 for PI.HtPlacesSumWork.gauss_unif
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:38.732882+00:00
-- url     : https://prove2.me/submissions/c614a576-6965-4623-a834-93851eb28319

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_PlaceSumHeights_PlaceSumStatements_PlaceSumLemmas_GaussValuationSums_GaussMaximalIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.HtPlacesSumWork
open NumberField IsLocalRing ReciprocityTheory.ChartRestriction.G.T0
variable {K : Type} [Field K] [NumberField K] (D N : ℕ)
  (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
namespace PI.HtPlacesSumWork
theorem _root_.solution : ∃ π ∈ la.asIdeal, π ≠ 0 ∧ ∃ s ∉ la.asIdeal,
    ∀ a ∈ la.asIdeal, ∃ b, s * a = π * b := by
  have hp0 : la.asIdeal ≠ ⊥ := la.ne_bot
  have hp1 : la.asIdeal ≠ ⊤ := la.isPrime.ne_top
  have hlt : la.asIdeal ^ 2 < la.asIdeal := by
    have := Ideal.pow_right_strictAnti la.asIdeal hp0 hp1 (show 1 < 2 by norm_num)
    simpa using this
  obtain ⟨π, hπ, hπ2⟩ := SetLike.exists_of_lt hlt
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact hπ2 (Ideal.zero_mem _)
  obtain ⟨J, hJ⟩ : la.asIdeal ∣ Ideal.span {π} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hπ)
  have hJp : ¬ J ≤ la.asIdeal := by
    intro hle
    apply hπ2
    have h1 : π ∈ la.asIdeal * J := by
      rw [← hJ]; exact Ideal.mem_span_singleton_self π
    have h2 : la.asIdeal * J ≤ la.asIdeal ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mono_right hle
    exact h2 h1
  obtain ⟨s, hsJ, hsp⟩ := SetLike.not_le_iff_exists.mp hJp
  refine ⟨π, hπ, hπ0, s, hsp, fun a ha => ?_⟩
  have hmem : a * s ∈ Ideal.span {π} := by
    rw [hJ]; exact Ideal.mul_mem_mul ha hsJ
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨b, by rw [mul_comm s a, ← hb, mul_comm]⟩
end PI.HtPlacesSumWork
