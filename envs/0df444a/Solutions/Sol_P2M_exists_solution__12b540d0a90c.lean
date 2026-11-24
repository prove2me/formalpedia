-- Prove2me | solution 1 for P2M_exists_solution__12b540d0a90c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:19:10.723809+00:00
-- url     : https://prove2.me/submissions/49a78f3b-3f4d-49fc-8f66-ed153e6a27ed

module
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Mathlib.RingTheory.ClassGroup.Basic
public import Definitions.Def_FltRegular_CaseII_AuxLemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_MoreLemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_UnitLemmas
public import Definitions.Def_FltRegular_NumberTheory_KummersLemma_KummersLemma
public import Definitions.Def_FltRegular_CaseII_InductionStep
public import Theorems.Thm_one_le_m
public import Theorems.Thm_P2M_exists_solution__aux_11ef8cae6b3d
public import Theorems.Thm_exists_solution
public import Theorems.Thm_eq_pow_prime_of_unit_of_congruent
public import Theorems.Thm_exists_dvd_pow_sub_Int_pow


set_option autoImplicit false
@[expose] public section
public section
open scoped nonZeroDivisors NumberField
open Polynomial IsCyclotomicExtension.Rat
attribute [local implicit_reducible] integralClosure NumberField.RingOfIntegers
variable {K : Type} {p : ℕ} [NeZero p] [Field K] [NumberField K] (hp : p ≠ 2)
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p) {x y z : 𝓞 K} {ε : (𝓞 K)ˣ}
local notation3 "π" => hζ.toInteger - 1
local notation3 "𝔭" => Ideal.span {π}
local notation3 "𝔦" η => Ideal.span {(x + y * η : 𝓞 K)}
local notation3 "𝔵" => Ideal.span {x}
local notation3 "𝔶" => Ideal.span {y}
local notation3 "𝔷" => Ideal.span {z}
variable {m : ℕ} (e : x ^ p + y ^ p = ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ p)
variable (hy : ¬ hζ.toInteger - 1 ∣ y) (hz : ¬ hζ.toInteger - 1 ∣ z)
variable (η : nthRootsFinset p (1 : 𝓞 K))
local notation3 "𝔪" => gcd 𝔵 𝔶
variable [hpri : Fact p.Prime]
variable [IsCyclotomicExtension {p} ℚ K]
local notation "𝔠" => fun η ↦ divZetaSubOneDvdGcd hp hζ e hy η
local notation "𝔷'" => zDivM hζ e hy
local notation "𝔞" => rootDivZetaSubOneDvdGcd hp hζ e hy
local notation "η₀" => zetaSubOneDvdRoot hp hζ e hy
local notation "𝔞₀" => aEtaZeroDvdPPow hp hζ e hy
variable [Fintype (ClassGroup (𝓞 K))] (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K))
local notation "α" => fun η ↦ aDivAZeroNum hp hζ e hy hz η hreg
local notation "β" => fun η ↦ aDivAZeroDenom hp hζ e hy hz η hreg
local notation "ε" => fun η ↦ associatedEtaZeroUnit hp hζ e hy hz η hreg
include hp hreg e hy hz
theorem _root_.solution : ∃ (x' y' z' : 𝓞 K) (ε₃ : (𝓞 K)ˣ),
    ¬ π ∣ y' ∧ ¬ π ∣ z' ∧ x' ^ p + y' ^ p = ε₃ * (π ^ m * z') ^ p := by
  obtain ⟨x', y', z', ε₁, ε₂, ε₃, hx', hy', hz', e'⟩ :=
    exists_solution hp hζ e hy hz hreg
  obtain ⟨ε', hε'⟩ : ∃ ε', ε₁ / ε₂ = ε' ^ p := by
    apply eq_pow_prime_of_unit_of_congruent hp hreg
    have : p - 1 ≤ m * p := (Nat.sub_le _ _).trans
      ((le_of_eq (one_mul _).symm).trans (Nat.mul_le_mul_right p (one_le_m hp hζ e hy hz)))
    obtain ⟨u, hu⟩ := (associated_zeta_sub_one_pow_prime _ hζ).symm
    rw [mul_pow, ← pow_mul, mul_comm (ε₃ : 𝓞 K), mul_assoc, ← Nat.sub_add_cancel this,
      add_comm _ (p - 1), pow_add, mul_assoc] at e'
    apply_fun Ideal.Quotient.mk (Ideal.span <| singleton (p : 𝓞 K)) at e'
    rw [map_mul, (Ideal.Quotient.eq_zero_iff_dvd _ _).mpr
      (associated_zeta_sub_one_pow_prime _ hζ).symm.dvd, zero_mul,
      Ideal.Quotient.eq_zero_iff_dvd] at e'
    obtain ⟨a, ha⟩ := exists_solution'_aux hp hζ hx' e'
    obtain ⟨b, hb⟩ := exists_dvd_pow_sub_Int_pow hp a
    have := dvd_add ha hb
    rw [sub_add_sub_cancel, ← Int.cast_pow] at this
    exact ⟨b ^ p, this⟩
  refine ⟨ε' * x', y', z', ε₃ / ε₂, hy', hz', ?_⟩
  rwa [mul_pow, ← Units.val_pow_eq_pow_val, ← hε', ← mul_right_inj' ε₂.isUnit.ne_zero,
    mul_add, ← mul_assoc, ← Units.val_mul, mul_div_cancel,
    ← mul_assoc, ← Units.val_mul, mul_div_cancel]
