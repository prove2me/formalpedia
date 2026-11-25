-- Prove2me | solution 1 for UpperTheory.exists_shift_weightCongruence_lt_torsionOrder
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:58:51.608909+00:00
-- url     : https://prove2.me/submissions/95610708-4099-4a1e-bda4-33f37e0d7bee

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ProdNegOneZpow
import Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_ExistsShiftWeightCongruenceLtTorsionOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
namespace UpperTheory
theorem _root_.solution :
    ∀ (E K : Type) [Field E] [NumberField E] [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (φ : ι → E →+* K) (e : ι → ℤ) (i₀ : ι),
      ∃ s : ℕ, s < NumberField.Units.torsionOrder E ∧ UpperTheory.MU φ (fun i => e i + if i = i₀ then (s : ℤ) else 0) := by
  intro E K _ _ _ ι _ _ φ e i₀
  obtain ⟨μ, hμ⟩ : ∃ μ : NumberField.Units.torsion E,
      orderOf μ = NumberField.Units.torsionOrder E :=
    IsCyclic.exists_ofOrder_eq_natCard
  rw [← IsPrimitiveRoot.iff_orderOf, ← IsPrimitiveRoot.coe_submonoidClass_iff,
    ← IsPrimitiveRoot.coe_units_iff] at hμ
  replace hμ := hμ.map_of_injective (FaithfulSMul.algebraMap_injective (NumberField.RingOfIntegers E) E)
  obtain ⟨ζ, hζ⟩ : ∃ ζ : E, IsPrimitiveRoot ζ (NumberField.Units.torsionOrder E) := ⟨_, hμ⟩
  have hw0 : 0 < NumberField.Units.torsionOrder E := NumberField.Units.torsionOrder_pos E
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hw0.ne'
  have hψ : IsPrimitiveRoot (φ i₀ ζ) (NumberField.Units.torsionOrder E) :=
    hζ.map_of_injective (φ i₀).injective
  have hc0 : (∏ i, (φ i ζ) ^ e i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ ((map_ne_zero _).mpr hζ0)
  have hcw : ((∏ i, (φ i ζ) ^ e i)⁻¹) ^ (NumberField.Units.torsionOrder E) = 1 := by
    rw [inv_pow, ← Finset.prod_pow]
    have h1 : ∀ i ∈ (Finset.univ : Finset ι),
        ((φ i ζ) ^ e i) ^ (NumberField.Units.torsionOrder E) = 1 := by
      intro i _
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← map_pow,
        hζ.pow_eq_one, map_one, one_zpow]
    rw [Finset.prod_eq_one h1, inv_one]
  obtain ⟨s, hs, hsc⟩ := hψ.eq_pow_of_pow_eq_one hcw
  refine ⟨s, hs, ?_⟩
  have key : ∏ i, (φ i ζ) ^ (e i + if i = i₀ then (s : ℤ) else 0) = 1 := by
    have hsplit : ∀ i, (φ i ζ) ^ (e i + if i = i₀ then (s : ℤ) else 0) =
        (φ i ζ) ^ e i * (if i = i₀ then (φ i ζ) ^ s else 1) := by
      intro i
      rw [zpow_add₀ ((map_ne_zero _).mpr hζ0)]
      split_ifs <;> simp
    simp_rw [hsplit]
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', if_pos (Finset.mem_univ _), hsc,
      mul_inv_cancel₀ hc0]
  intro z hz
  obtain ⟨m, hm, hzm⟩ := hz
  have hzw : z ^ (NumberField.Units.torsionOrder E) = 1 := by
    have hpos : 0 < orderOf z :=
      orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, hzm⟩)
    haveI : NeZero (orderOf z) := ⟨hpos.ne'⟩
    obtain ⟨k, hk⟩ :=
      NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot (IsPrimitiveRoot.orderOf z)
    rw [hk, pow_mul, pow_orderOf_eq_one, one_pow]
  obtain ⟨j, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hzw
  calc ∏ i, (φ i (ζ ^ j)) ^ (e i + if i = i₀ then (s : ℤ) else 0)
      = (∏ i, (φ i ζ) ^ (e i + if i = i₀ then (s : ℤ) else 0)) ^ j := by
        rw [← Finset.prod_pow]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [map_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    _ = 1 := by rw [key, one_pow]
end UpperTheory
