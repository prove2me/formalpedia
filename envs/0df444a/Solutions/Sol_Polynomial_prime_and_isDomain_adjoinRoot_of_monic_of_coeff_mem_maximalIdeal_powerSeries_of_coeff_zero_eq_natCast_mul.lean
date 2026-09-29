-- Prove2me | solution 1 for Polynomial.prime_and_isDomain_adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_powerSeries_of_coeff_zero_eq_natCast_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/1fa17f1b-00ba-50f8-9909-2f532d648406

import Mathlib
import Theorems.Thm_IsRegularLocalRing_adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_of_coeff_zero_not_mem_sq
import Theorems.Thm_IsRegularLocalRing_isDomain
import Theorems.Thm_IsRegularLocalRing_mvPowerSeries_fin
import Theorems.Thm_MvPowerSeries_ringKrullDim_fin_eq_of_isDiscreteValuationRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_prime_and_isDomain_adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_powerSeries_of_coeff_zero_eq_natCast_mul
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open Polynomial IsLocalRing

namespace EisDom

open Polynomial

section powerSeriesFacts

variable (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]

lemma isRegularLocalRing_powerSeries : IsRegularLocalRing (PowerSeries W₀) := by
  haveI := IsRegularLocalRing.mvPowerSeries_fin W₀ 1
  exact IsRegularLocalRing.of_ringEquiv
    (R := MvPowerSeries (Fin 1) W₀) (MvPowerSeries.renameEquiv W₀ finOneEquiv).toRingEquiv

lemma ringKrullDim_powerSeries : ringKrullDim (PowerSeries W₀) = 2 := by
  have h := MvPowerSeries.ringKrullDim_fin_eq_of_isDiscreteValuationRing W₀ 1
  rw [← ringKrullDim_eq_of_ringEquiv (MvPowerSeries.renameEquiv W₀ finOneEquiv).toRingEquiv]
  rw [h]; rfl

lemma mem_maximalIdeal_powerSeries_iff (f : PowerSeries W₀) :
    f ∈ maximalIdeal (PowerSeries W₀) ↔ PowerSeries.constantCoeff f ∈ maximalIdeal W₀ := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    PowerSeries.isUnit_iff_constantCoeff]

lemma map_constantCoeff_maximalIdeal_le :
    (maximalIdeal (PowerSeries W₀)).map (PowerSeries.constantCoeff (R := W₀)) ≤ maximalIdeal W₀ := by
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  exact (mem_maximalIdeal_powerSeries_iff W₀ f).1 hf

variable (q : ℕ) (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})

include hW₀ in
lemma natCast_mem_maximalIdeal : (q : W₀) ∈ maximalIdeal W₀ := by
  rw [hW₀]; exact Ideal.subset_span rfl

include hW₀ in
lemma natCast_ne_zero : (q : W₀) ≠ 0 := by
  intro h
  have : maximalIdeal W₀ = ⊥ := by rw [hW₀, h, Ideal.span_singleton_eq_bot]
  exact IsDiscreteValuationRing.not_isField W₀ (IsLocalRing.isField_iff_maximalIdeal_eq.mpr this)

include hW₀ in
lemma natCast_mem_maximalIdeal_powerSeries : (q : PowerSeries W₀) ∈ maximalIdeal (PowerSeries W₀) := by
  rw [mem_maximalIdeal_powerSeries_iff, map_natCast]
  exact natCast_mem_maximalIdeal W₀ q hW₀

include hW₀ in

lemma natCast_mul_not_mem_sq (u : PowerSeries W₀) (hu : IsUnit u) :
    (q : PowerSeries W₀) * u ∉ maximalIdeal (PowerSeries W₀) ^ 2 := by
  intro hmem
  have h1 : PowerSeries.constantCoeff ((q : PowerSeries W₀) * u) ∈ (maximalIdeal W₀) ^ 2 := by
    have := Ideal.mem_map_of_mem (PowerSeries.constantCoeff (R := W₀)) hmem
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono (map_constantCoeff_maximalIdeal_le W₀) 2 this
  rw [map_mul, map_natCast, hW₀, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  have hu0 : IsUnit (PowerSeries.constantCoeff u) := PowerSeries.isUnit_constantCoeff u hu
  have hq0 := natCast_ne_zero W₀ q hW₀
  have : PowerSeries.constantCoeff u = (q : W₀) * c := by
    have : (q : W₀) * PowerSeries.constantCoeff u = (q : W₀) * ((q : W₀) * c) := by
      rw [hc]; ring
    exact mul_left_cancel₀ hq0 this
  have hmem' : PowerSeries.constantCoeff u ∈ maximalIdeal W₀ := by
    rw [this]; exact Ideal.mul_mem_right _ _ (natCast_mem_maximalIdeal W₀ q hW₀)
  exact (IsLocalRing.mem_maximalIdeal _ |>.1 hmem') hu0

include hW₀ in

lemma isDomain_quotient_span_natCast :
    IsDomain (PowerSeries W₀ ⧸ Ideal.span {(q : PowerSeries W₀)}) := by
  have hmax : (Ideal.span {(q : W₀)}).IsMaximal := by rw [← hW₀]; exact maximalIdeal.isMaximal W₀
  letI : Field (W₀ ⧸ Ideal.span {(q : W₀)}) := Ideal.Quotient.field _
  let π : PowerSeries W₀ →+* PowerSeries (W₀ ⧸ Ideal.span {(q : W₀)}) :=
    PowerSeries.map (Ideal.Quotient.mk _)
  have hker : RingHom.ker π = Ideal.span {(q : PowerSeries W₀)} := by
    ext f
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    constructor
    · intro hf
      have hc : ∀ n, (q : W₀) ∣ PowerSeries.coeff n f := by
        intro n
        have := congrArg (PowerSeries.coeff n) hf
        rw [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
        exact this
      choose c hc using hc
      refine ⟨PowerSeries.mk c, ?_⟩
      ext n
      rw [show (q : PowerSeries W₀) = PowerSeries.C (q : W₀) by rw [map_natCast], PowerSeries.coeff_C_mul,
        PowerSeries.coeff_mk, hc n]
    · rintro ⟨c, rfl⟩
      have hq : (q : PowerSeries (W₀ ⧸ Ideal.span {(q : W₀)})) = 0 := by
        have h0 : ((q : W₀ ⧸ Ideal.span {(q : W₀)})) = 0 := by
          rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(q : W₀)})), Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.subset_span rfl
        rw [show (q : PowerSeries (W₀ ⧸ Ideal.span {(q : W₀)})) =
          PowerSeries.C ((q : W₀ ⧸ Ideal.span {(q : W₀)})) by rw [map_natCast], h0, map_zero]
      rw [map_mul, map_natCast, hq, zero_mul]
  rw [← hker]
  exact (Ideal.Quotient.isDomain_iff_prime _).2 (RingHom.ker_isPrime π)

end powerSeriesFacts

end EisDom

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 2 ≤ q)
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (g : Polynomial (PowerSeries W₀)) (hgm : g.Monic) (hgdeg : g.natDegree = q - 1)
    (hgcoeff : ∀ i < q - 1, g.coeff i ∈ maximalIdeal (PowerSeries W₀))
    (hg0 : ∃ u : PowerSeries W₀, IsUnit u ∧ g.coeff 0 = (q : PowerSeries W₀) * u) :
    Prime g ∧ IsDomain (AdjoinRoot g) := by
  classical
  haveI hSreg : IsRegularLocalRing (PowerSeries W₀) := EisDom.isRegularLocalRing_powerSeries W₀
  have hq1 : 1 ≤ q - 1 := by omega
  obtain ⟨u, hu, hgu⟩ := hg0
  have hg0' : g.coeff 0 ∉ maximalIdeal (PowerSeries W₀) ^ 2 := by
    rw [hgu]; exact EisDom.natCast_mul_not_mem_sq W₀ q hW₀ u hu
  obtain ⟨hRreg, -⟩ :=
    IsRegularLocalRing.adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_of_coeff_zero_not_mem_sq
      (PowerSeries W₀) g hgm (by rw [hgdeg]; exact hq1) (by rw [hgdeg]; exact hgcoeff) hg0'
  haveI := hRreg
  haveI hRdom : IsDomain (AdjoinRoot g) := IsRegularLocalRing.isDomain _
  refine ⟨?_, hRdom⟩
  refine ⟨hgm.ne_zero, ?_, ?_⟩
  · intro hunit
    have h1 : g = 1 := hgm.isUnit_iff.mp hunit
    have : g.natDegree = 0 := by rw [h1, natDegree_one]
    omega
  · intro a b hab
    have h0 : AdjoinRoot.mk g (a * b) = 0 := AdjoinRoot.mk_eq_zero.mpr hab
    rw [map_mul, mul_eq_zero] at h0
    rcases h0 with h | h
    · exact Or.inl (AdjoinRoot.mk_eq_zero.mp h)
    · exact Or.inr (AdjoinRoot.mk_eq_zero.mp h)

end S_Polynomial_prime_and_isDomain_adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_powerSeries_of_coeff_zero_eq_natCast_mul
end P2MW
export P2MW.S_Polynomial_prime_and_isDomain_adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_powerSeries_of_coeff_zero_eq_natCast_mul (solution)
