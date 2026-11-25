-- Prove2me | solution 1 for UpperTheory.Mu.torsion_reduce_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:00:05.465041+00:00
-- url     : https://prove2.me/submissions/f5458636-de90-4f2c-9c73-f242a61e069c

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RootsOfUnity_TorsionReduceInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Classical
noncomputable section
open UpperTheory UpperTheory.Mu
namespace UpperTheory.Mu
theorem _root_.solution (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))
    (hw : ((NumberField.Units.torsionOrder L : ℕ) : 𝓞 L) ∉ v.asIdeal) :
    Function.Injective ((Units.map (Ideal.Quotient.mk v.asIdeal).toMonoidHom).comp
      (NumberField.Units.torsion L).subtype) := by
  rw [injective_iff_map_eq_one]
  intro ζ hζ
  by_contra hne
  have hmk : Ideal.Quotient.mk v.asIdeal (((ζ : NumberField.Units.torsion L) : (𝓞 L)ˣ) : 𝓞 L) = 1 := by
    have h := congrArg (fun u : (𝓞 L ⧸ v.asIdeal)ˣ => (u : 𝓞 L ⧸ v.asIdeal)) hζ
    simpa using h
  have hx1 : (((ζ : NumberField.Units.torsion L) : (𝓞 L)ˣ) : 𝓞 L) ≠ 1 := by
    intro h
    apply hne
    apply Subtype.ext
    exact Units.ext h
  have hpow : (((ζ : NumberField.Units.torsion L) : (𝓞 L)ˣ) : 𝓞 L) ^ NumberField.Units.torsionOrder L = 1 := by
    have h : ζ ^ Nat.card (NumberField.Units.torsion L) = 1 := pow_card_eq_one'
    show (((ζ : NumberField.Units.torsion L) : (𝓞 L)ˣ) : 𝓞 L) ^ Nat.card (NumberField.Units.torsion L) = 1
    rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, h]
    simp
  have hsum : ∑ i ∈ Finset.range (NumberField.Units.torsionOrder L),
      (((ζ : NumberField.Units.torsion L) : (𝓞 L)ˣ) : 𝓞 L) ^ i = 0 := by
    have h := geom_sum_mul (((ζ : NumberField.Units.torsion L) : (𝓞 L)ˣ) : 𝓞 L)
      (NumberField.Units.torsionOrder L)
    rw [hpow, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hx1)
  apply hw
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h := congrArg (Ideal.Quotient.mk v.asIdeal) hsum
  rw [map_sum, map_zero] at h
  simp only [map_pow, hmk, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h
  simpa using h
end UpperTheory.Mu
