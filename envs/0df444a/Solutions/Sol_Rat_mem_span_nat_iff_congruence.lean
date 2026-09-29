-- Prove2me | solution 1 for Rat.mem_span_nat_iff_congruence
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T23:01:45.604274+00:00
-- url     : https://prove2.me/submissions/bcf56043-a058-4a5f-9d5d-c4f63c28ebe7

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Span

theorem solution (n : ℕ) (a : NumberField.RingOfIntegers ℚ) :
    a - 1 ∈ Ideal.span {(n : NumberField.RingOfIntegers ℚ)} ↔
      ∃ k : ℤ, Rat.ringOfIntegersEquiv a = 1 + (n : ℤ) * k := by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨Rat.ringOfIntegersEquiv k, ?_⟩
    have hh : Rat.ringOfIntegersEquiv a - 1 =
        (n : ℤ) * Rat.ringOfIntegersEquiv k := by
      simpa only [map_sub, map_one, map_mul, map_natCast] using
        congrArg Rat.ringOfIntegersEquiv hk
    omega
  · rintro ⟨k, hk⟩
    refine ⟨Rat.ringOfIntegersEquiv.symm k, ?_⟩
    apply Rat.ringOfIntegersEquiv.injective
    have hh : Rat.ringOfIntegersEquiv a - 1 = (n : ℤ) * k := by omega
    simpa only [map_sub, map_one, map_mul, map_natCast,
      RingEquiv.apply_symm_apply] using hh
