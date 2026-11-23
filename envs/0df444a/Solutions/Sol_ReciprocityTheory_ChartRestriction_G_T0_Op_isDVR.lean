-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Op_isDVR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:03.052321+00:00
-- url     : https://prove2.me/submissions/5625cb36-f0d8-46ff-89de-a7a5ec137be0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OpIsDVR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsLocalRing
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {K : Type} [Field K] [NumberField K] (D N : ℕ)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : IsDiscreteValuationRing (Op D N la) := by
  classical
  set P := laT D N la with hP
  have hp0 : la.asIdeal ≠ ⊥ := la.ne_bot
  have hp1 : la.asIdeal ≠ ⊤ := la.isPrime.ne_top

  obtain ⟨π, hπp, hπ2⟩ : ∃ π ∈ la.asIdeal, π ∉ la.asIdeal ^ 2 := by
    have hlt : la.asIdeal ^ 2 < la.asIdeal ^ 1 :=
      Ideal.pow_right_strictAnti la.asIdeal hp0 hp1 (by norm_num : 1 < 2)
    rw [pow_one] at hlt
    obtain ⟨x, hx, hx2⟩ := SetLike.exists_of_lt hlt
    exact ⟨x, hx, hx2⟩
  have hmemP : ∀ t : 𝓞 K, MvPolynomial.C t ∈ P ↔ t ∈ la.asIdeal := by
    intro t
    rw [hP, laT, MvPolynomial.mem_map_C_iff]
    constructor
    · intro h
      simpa using h 0
    · intro h m
      rw [MvPolynomial.coeff_C]
      split_ifs
      · exact h
      · exact zero_mem _

  have hdiv : ∀ a ∈ la.asIdeal, ∃ t c : 𝓞 K, t ∉ la.asIdeal ∧ t * a = π * c := by
    intro a ha
    have hle : Ideal.span {π} ≤ la.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hπp
    obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
    have hJp : ¬ J ≤ la.asIdeal := by
      intro hJle
      apply hπ2
      have hsq : Ideal.span {π} ≤ la.asIdeal ^ 2 := by
        rw [hJ, pow_two]
        exact Ideal.mul_mono_right hJle
      exact hsq (Ideal.mem_span_singleton_self π)
    obtain ⟨t, htJ, htp⟩ := SetLike.not_le_iff_exists.mp hJp
    have hta : t * a ∈ Ideal.span {π} := by
      rw [hJ, mul_comm t a]
      exact Ideal.mul_mem_mul ha htJ
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hta
    exact ⟨t, c, htp, by rw [← hc, mul_comm]⟩
  haveI : IsNoetherianRing (Op D N la) :=
    IsLocalization.isNoetherianRing P.primeCompl (Op D N la) inferInstance
  let f : 𝓞 K →+* Op D N la := (algebraMap (OT K D N) (Op D N la)).comp MvPolynomial.C
  have hmax : IsLocalRing.maximalIdeal (Op D N la) = Ideal.map f la.asIdeal := by
    have e : Ideal.map f la.asIdeal =
        Ideal.map (algebraMap (OT K D N) (Op D N la)) (laT D N la) :=
      (Ideal.map_map (MvPolynomial.C : 𝓞 K →+* OT K D N) (algebraMap (OT K D N) (Op D N la))).symm
    rw [e]
    exact (Localization.AtPrime.map_eq_maximalIdeal).symm
  have hπm : IsLocalRing.maximalIdeal (Op D N la) = Ideal.span {f π} := by
    apply le_antisymm
    · rw [hmax, Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap]
      obtain ⟨t, c, htp, htc⟩ := hdiv a ha
      have hu : IsUnit (f t) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff (Op D N la) P (MvPolynomial.C t)).mpr
          (fun h => htp ((hmemP t).mp h))
      obtain ⟨u, hu'⟩ := hu
      rw [Ideal.mem_span_singleton']
      refine ⟨↑u⁻¹ * f c, ?_⟩
      have hfm : f t * f a = f π * f c := by rw [← map_mul, ← map_mul, htc]
      calc ↑u⁻¹ * f c * f π = ↑u⁻¹ * (f π * f c) := by ring
        _ = ↑u⁻¹ * (f t * f a) := by rw [hfm]
        _ = f a := by rw [← hu', ← mul_assoc, Units.inv_mul, one_mul]
    · rw [Ideal.span_le, Set.singleton_subset_iff, hmax]
      exact Ideal.mem_map_of_mem f hπp
  have hnf : ¬ IsField (Op D N la) := by
    intro hF
    have hb := IsLocalRing.isField_iff_maximalIdeal_eq.mp hF
    rw [hπm, Ideal.span_singleton_eq_bot] at hb
    have hπ0 : π ≠ 0 := fun h => hπ2 (h ▸ zero_mem _)
    have hinj : Function.Injective (algebraMap (OT K D N) (Op D N la)) :=
      IsLocalization.injective (Op D N la) (Ideal.primeCompl_le_nonZeroDivisors P)
    exact hπ0 (MvPolynomial.C_injective _ _ ((hinj (hb.trans (map_zero _).symm)).trans
      (map_zero _).symm))
  have hprin : (IsLocalRing.maximalIdeal (Op D N la)).IsPrincipal := ⟨⟨f π, hπm⟩⟩
  exact ((IsDiscreteValuationRing.TFAE (Op D N la) hnf).out 0 4).mpr hprin
end ReciprocityTheory.ChartRestriction.G.T0
