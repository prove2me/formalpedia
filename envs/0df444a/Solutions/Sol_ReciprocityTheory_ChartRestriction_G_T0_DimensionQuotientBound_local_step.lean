-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.DimensionQuotientBound.local_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:50:59.622188+00:00
-- url     : https://prove2.me/submissions/59c88b47-4dd3-4fa0-a664-d49bf5018f5e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AvPrimeDimOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DimensionQuotientBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_DimensionQuotientBound_le_dim_quot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_DimensionQuotientBound_one_le_dim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_av_prime_dim_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.DimensionQuotientBound
open IsLocalRing
namespace ReciprocityTheory.ChartRestriction.G.T0.DimensionQuotientBound
theorem _root_.solution {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] (M : Ideal B) [hM : M.IsMaximal]
    (w e : B) (hw : w ∈ M) (hw0 : w ≠ 0) (he : e ≠ 0) :
    ∃ q : Ideal B, q.IsPrime ∧ q ≤ M ∧ e ∉ q ∧ w ∉ q ∧
      ∀ P : Ideal B, P.IsPrime → q ≤ P → P ≤ M → w ∈ P → P = M := by
  classical
  let R := Localization.AtPrime M
  haveI : IsDomain R := IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors M)
  have hinj : Function.Injective (algebraMap B R) :=
    IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors M)
  have hcm : (IsLocalRing.maximalIdeal R).comap (algebraMap B R) = M :=
    Localization.AtPrime.comap_maximalIdeal (I := M)
  have hh : algebraMap B R (e * w) ≠ 0 := by
    intro h
    exact mul_ne_zero he hw0 (hinj (by rw [h, map_zero]))
  have hmax : (⊥ : Ideal R) < IsLocalRing.maximalIdeal R := by
    rw [bot_lt_iff_ne_bot]
    intro h
    have hw' : algebraMap B R w ∈ IsLocalRing.maximalIdeal R := by
      rw [← Ideal.mem_comap, hcm]; exact hw
    rw [h, Ideal.mem_bot] at hw'
    exact hw0 (hinj (by rw [hw', map_zero]))
  have hdim : 1 ≤ ringKrullDim R := one_le_dim ⊥ (IsLocalRing.maximalIdeal R) hmax
  obtain ⟨p, hp, hpd, hpn⟩ := ReciprocityTheory.ChartRestriction.G.T0.av_prime_dim_one hdim _ hh
  haveI := hp
  refine ⟨p.comap (algebraMap B R), Ideal.comap_isPrime _ _, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [← hcm]
    exact IsLocalRing.le_maximalIdeal hp.ne_top hx
  · intro he'
    apply hpn
    rw [map_mul]
    exact p.mul_mem_right _ he'
  · intro hw'
    apply hpn
    rw [map_mul]
    exact p.mul_mem_left _ hw'
  · intro P hP hqP hPM hwP
    by_contra hne
    have hdisj : Disjoint (M.primeCompl : Set B) P := by
      rw [Set.disjoint_left]
      intro x hx hxP
      exact hx (hPM hxP)
    haveI hP' : (P.map (algebraMap B R)).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint M.primeCompl R P hP hdisj
    have hcomap : (P.map (algebraMap B R)).comap (algebraMap B R) = P :=
      IsLocalization.comap_map_of_isPrime_disjoint M.primeCompl R hP hdisj
    have h1 : p < P.map (algebraMap B R) := by
      refine lt_of_le_of_ne ?_ ?_
      · have hpe : (p.comap (algebraMap B R)).map (algebraMap B R) = p :=
          IsLocalization.map_comap M.primeCompl R p
        rw [← hpe]
        exact Ideal.map_mono hqP
      · intro heq
        apply hpn
        rw [heq, map_mul]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hwP)
    have h2 : P.map (algebraMap B R) < IsLocalRing.maximalIdeal R := by
      refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hP'.ne_top) ?_
      intro heq
      apply hne
      rw [← hcomap, heq, hcm]
    have h3 := le_dim_quot p (P.map (algebraMap B R)) (IsLocalRing.maximalIdeal R) h1 h2
    rw [hpd] at h3
    exact absurd h3 (by decide)
end ReciprocityTheory.ChartRestriction.G.T0.DimensionQuotientBound
