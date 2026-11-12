-- Prove2me | solution 1 for OddOrder.Algebra.exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:11:14.735695+00:00
-- url     : https://prove2.me/submissions/b67b8fd9-7343-44b9-b468-3817f40df510

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Algebra/GaloisRationalInteger.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CyclotomicGaloisAction
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassSumAlgebra
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterConjugate
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterCompleteness
import Definitions.Def_OddOrder_Algebra_GaloisRationalInteger
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Theorems.Thm_OddOrder_Algebra_exists_int_of_isIntegral_of_forall_complexRingEquiv_fixed

-- ===== OddOrder/Algebra/GaloisRationalInteger.lean =====
namespace OddOrder.Algebra

open Polynomial IntermediateField

/-- **Every ring automorphism of `ℂ` acts as a uniform power on `n`-th roots of unity.**
For `σ : ℂ ≃+* ℂ` and `n ≠ 0` there is a `k` coprime to `n` with `σ ζ = ζ ^ k` for every `n`-th root
of unity `ζ`.  This is the converse of `exists_complexRingEquiv_pow_of_rootsOfUnity` (which, given a
coprime `k`, produces such a `σ`): here we start from an arbitrary `σ` and *read off* its exponent.
The exponent is well defined because `σ` sends a fixed primitive root `μ` to another primitive root
`μ ^ k`, and every `n`-th root is a power of `μ`. -/
theorem exists_pow_of_complexRingEquiv (σ : ℂ ≃+* ℂ) {n : ℕ} (hn : n ≠ 0) :
    ∃ k : ℕ, k.Coprime n ∧ ∀ ζ : ℂ, ζ ^ n = 1 → σ ζ = ζ ^ k := by
  have : NeZero n := ⟨hn⟩
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨μ, hμ⟩ : ∃ μ : ℂ, IsPrimitiveRoot μ n := ⟨_, Complex.isPrimitiveRoot_exp n hn⟩
  have hσμ : IsPrimitiveRoot (σ μ) n := hμ.map_of_injective σ.injective
  have hpow1 : (σ μ) ^ n = 1 := by rw [← map_pow, hμ.pow_eq_one, map_one]
  obtain ⟨k, -, hk_eq⟩ := hμ.eq_pow_of_pow_eq_one hpow1
  refine ⟨k, ?_, ?_⟩
  · have : IsPrimitiveRoot (μ ^ k) n := hk_eq ▸ hσμ
    exact (hμ.pow_iff_coprime hnpos k).mp this
  · intro ζ hζ
    obtain ⟨j, -, hj_eq⟩ := hμ.eq_pow_of_pow_eq_one hζ
    rw [← hj_eq, map_pow, ← hk_eq, ← pow_mul, ← pow_mul, Nat.mul_comm]

open OddOrder.RepresentationTheory in
/-- **Galois-fixedness step, extracted** (issue 0106): a ring automorphism `σ : ℂ ≃+* ℂ` that
acts as `(· ^ k)` on all `|G|`-th roots of unity substitutes the coprime power on virtual
character values: `σ (φ w) = φ (w ^ k)` (Peterfalvi (1.9), `ZIrr` form).  The order-of-`w`
torsion descent packaged here was previously copied inline by each of the product/sum
integrality theorems below. -/
theorem complexRingEquiv_apply_eq_apply_pow_of_mem_ZIrr {G : Type*} [Group G] [Finite G]
    {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) (σ : ℂ ≃+* ℂ) {k : ℕ}
    (hkσ : ∀ ζ : ℂ, ζ ^ Nat.card G = 1 → σ ζ = ζ ^ k) (w : G) :
    σ (φ w) = φ (w ^ k) := by
  have hσw : ∀ ζ : ℂ, ζ ^ orderOf w = 1 → σ ζ = ζ ^ k := by
    intro ζ hζ
    refine hkσ ζ ?_
    obtain ⟨c, hc⟩ := orderOf_dvd_of_pow_eq_one (pow_card_eq_one' (x := w))
    rw [hc, pow_mul, hζ, one_pow]
  have h := mapRingEquiv_apply_eq_apply_pow_of_mem_ZIrr hφ σ (isOfFinOrder_of_finite w) hσw
  rwa [ClassFunction.mapRingEquiv_apply] at h

open OddOrder.RepresentationTheory in
/-- **Virtual-character values are algebraic integers** (general form, `OddOrder.Algebra` copy of
the `S05` leaf lemma): each irreducible character value is a sum of roots of unity
(`character_isIntegral`), and `IsIntegral ℤ` is closed under the `ℤ`-span operations. -/
theorem isIntegral_apply_of_mem_ZIrr {G : Type*} [Group G] [Finite G]
    {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) (g : G) :
    IsIntegral ℤ (φ g) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨V, _, _, _, ρ, hchar⟩ := IsIrreducibleCharacter.isCharacter hx
      rw [show x g = ρ.character g from congrFun hchar g]
      exact character_isIntegral ρ g
  | zero => rw [ClassFunction.zero_apply]; exact isIntegral_zero
  | add a b _ _ ha hb => rw [ClassFunction.add_apply]; exact ha.add hb
  | smul n a _ ha =>
      rw [ClassFunction.zsmul_apply, zsmul_eq_mul]
      exact (isIntegral_algebraMap (x := n)).mul ha

open scoped Classical in
/-- **Cyclic-closed sets are permuted by coprime powers**: if `A` is closed under `x ↦ x ^ k` for
every `k` coprime to `|G|`, then each such power map is a bijection of `A` onto itself (it is
undone by `x ↦ x ^ (k ^ (φ(|G|) − 1))`, Euler).  Extracted from
`exists_int_prod_character_of_cyclicClosed` for reuse by the sum form. -/
theorem powClosed_image_pow_eq_of_cyclicClosed {G : Type*} [Group G] [Finite G]
    {A : Finset G} (hclosed : ∀ x ∈ A, ∀ k : ℕ, k.Coprime (Nat.card G) → x ^ k ∈ A)
    {k : ℕ} (hkcop : k.Coprime (Nat.card G)) :
    (∀ x ∈ A, ∀ y ∈ A, x ^ k = y ^ k → x = y) ∧ A.image (· ^ k) = A := by
  classical
  set N := Nat.card G with hNdef
  have hN0 : N ≠ 0 := Nat.card_pos.ne'
  set t := N.totient with htdef
  have ht1 : 1 ≤ t := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN0)
  have hpowN : ∀ w : G, w ^ N = 1 := fun w => by rw [hNdef]; exact pow_card_eq_one'
  have hround : ∀ w : G, (w ^ k) ^ (k ^ (t - 1)) = w := by
    intro w
    rw [← pow_mul]
    have hkt : k * k ^ (t - 1) = k ^ t := by rw [← pow_succ']; congr 1; omega
    rw [hkt]
    have hord : orderOf w ∣ N := orderOf_dvd_of_pow_eq_one (hpowN w)
    have hmod : k ^ t ≡ 1 [MOD orderOf w] := (Nat.ModEq.pow_totient hkcop).of_dvd hord
    rw [pow_eq_pow_iff_modEq.mpr hmod, pow_one]
  have hinj : ∀ x ∈ A, ∀ y ∈ A, x ^ k = y ^ k → x = y := by
    intro x _ y _ hxy
    have h := hround x
    rw [hxy, hround y] at h
    exact h.symm
  refine ⟨hinj, Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_⟩
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hclosed x hx k hkcop
  · rw [Finset.card_image_of_injOn (fun x hx y hy => hinj x hx y hy)]

open OddOrder.RepresentationTheory in
/-- **The squared-norm sum of a virtual character over a cyclic-closed `Finset` is a nonnegative
rational integer** (the sum form of [Isaacs] Lemma 3.14 / Peterfalvi (13.9.b), and the
integrality that makes the (13.10) atoms `slam = (1/|G|)·Σ_{G₀}‖λ^{τ₁}‖²` etc. *rational*).

The complex sum `Σ_{x∈A} φ(x)·φ(x⁻¹)` is an algebraic integer (values of `φ ∈ ℤ[Irr G]` are,
`isIntegral_apply_of_mem_ZIrr`) fixed by every `σ : ℂ ≃+* ℂ` — `σ` acts as `(· ^ k)` on all
`|G|`-th roots of unity (`exists_pow_of_complexRingEquiv`), so `σ(φ(x)) = φ(x^k)` and
`σ(φ(x⁻¹)) = φ((x^k)⁻¹)` ((1.9), ZIrr form), and `x ↦ x^k` permutes `A`
(`powClosed_image_pow_eq_of_cyclicClosed`); hence it is a rational integer
(`exists_int_of_isIntegral_of_forall_complexRingEquiv_fixed`).  Since `φ(x⁻¹) = conj(φ(x))`
(`apply_inv_eq_star_of_mem_ZIrr`), the sum *is* `Σ_{x∈A}‖φ(x)‖²` — real and nonnegative, so the
integer is a natural number. -/
theorem _root_.solution {G : Type*} [Group G] [Finite G]
    {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) {A : Finset G}
    (hclosed : ∀ x ∈ A, ∀ k : ℕ, k.Coprime (Nat.card G) → x ^ k ∈ A) :
    ∃ n : ℕ, (n : ℝ) = ∑ x ∈ A, ‖φ x‖ ^ 2 := by
  classical
  -- The ℂ-valued avatar of the sum.
  have hval : ∀ x : G, φ x * φ x⁻¹ = ((‖φ x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [apply_inv_eq_star_of_mem_ZIrr hφ x, ← Complex.normSq_eq_norm_sq]
    exact Complex.mul_conj (φ x)
  -- It is an algebraic integer.
  have hint : IsIntegral ℤ (∑ x ∈ A, φ x * φ x⁻¹) :=
    IsIntegral.sum _ (fun x _ =>
      (isIntegral_apply_of_mem_ZIrr hφ x).mul (isIntegral_apply_of_mem_ZIrr hφ x⁻¹))
  -- It is fixed by every ring automorphism of `ℂ`.
  have hfix : ∀ σ : ℂ ≃+* ℂ, σ (∑ x ∈ A, φ x * φ x⁻¹) = ∑ x ∈ A, φ x * φ x⁻¹ := by
    intro σ
    have hN0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
    obtain ⟨k, hkcop, hkσ⟩ := exists_pow_of_complexRingEquiv σ hN0
    obtain ⟨hinj, himg⟩ := powClosed_image_pow_eq_of_cyclicClosed hclosed hkcop
    have hσval : ∀ w : G, σ (φ w) = φ (w ^ k) :=
      complexRingEquiv_apply_eq_apply_pow_of_mem_ZIrr hφ σ hkσ
    have hstep : ∀ x ∈ A, σ (φ x * φ x⁻¹) = φ (x ^ k) * φ ((x ^ k)⁻¹) := by
      intro x _
      rw [map_mul, hσval x, hσval x⁻¹, inv_pow]
    calc σ (∑ x ∈ A, φ x * φ x⁻¹)
        = ∑ x ∈ A, φ (x ^ k) * φ ((x ^ k)⁻¹) := by rw [map_sum]; exact Finset.sum_congr rfl hstep
      _ = ∑ x ∈ A, φ x * φ x⁻¹ := by
          conv_rhs => rw [← himg]
          exact (Finset.sum_image (f := fun y => φ y * φ y⁻¹)
            (fun x hx y hy => hinj x hx y hy)).symm
  obtain ⟨z, hz⟩ := exists_int_of_isIntegral_of_forall_complexRingEquiv_fixed hint hfix
  -- The integer is the real nonnegative sum.
  have hreal : (z : ℂ) = ((∑ x ∈ A, ‖φ x‖ ^ 2 : ℝ) : ℂ) := by
    rw [hz, Finset.sum_congr rfl (fun x _ => hval x), ← Complex.ofReal_sum]
  have hzr : (z : ℝ) = ∑ x ∈ A, ‖φ x‖ ^ 2 := by exact_mod_cast hreal
  have hz0 : 0 ≤ z := by
    have h0 : (0 : ℝ) ≤ (z : ℝ) := hzr ▸ Finset.sum_nonneg (fun x _ => by positivity)
    exact_mod_cast h0
  refine ⟨z.toNat, ?_⟩
  rw [← hzr]
  exact_mod_cast congrArg Int.cast (Int.toNat_of_nonneg hz0)

end OddOrder.Algebra
