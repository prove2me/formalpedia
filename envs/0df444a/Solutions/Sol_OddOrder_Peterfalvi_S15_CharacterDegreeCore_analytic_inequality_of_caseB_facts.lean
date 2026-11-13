-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.CharacterDegreeCore.analytic_inequality_of_caseB_facts
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:03:17.365347+00:00
-- url     : https://prove2.me/submissions/ebd41c43-b341-438c-b84c-e90251edc1e8

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/CyclotomicGaloisAction.lean
--   OddOrder/Algebra/GaloisRationalInteger.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/Machinery135.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/Canonicalization.lean
--   OddOrder/Peterfalvi/S15_SAndT_Setup/NormEstimates.lean
--   OddOrder/Peterfalvi/S15_CaseBEndgameSupply/HSharpChosenBase.lean
--   OddOrder/Peterfalvi/S15_CaseBEndgameSupply/AnalyticRelayer.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Theorems.Thm_OddOrder_Algebra_exists_int_of_isIntegral_of_forall_complexRingEquiv_fixed
import Theorems.Thm_OddOrder_Algebra_exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed
import Theorems.Thm_OddOrder_Peterfalvi_S15_CharacterDegreeCore_analyticEstimate_eta_core
import Theorems.Thm_OddOrder_Peterfalvi_S15_CharacterDegreeCore_G0_nonvanishing_dichotomy_core
import Theorems.Thm_OddOrder_Peterfalvi_S15_CharacterDegreeCore_lambda_tau1_sharp_norm_lower_core
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_sum_univ_split
import Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_G0Finset_cyclicClosed

-- ===== OddOrder/GroupTheory/RepresentationTheory/CyclotomicGaloisAction.lean =====
namespace OddOrder.RepresentationTheory

open Polynomial

section OneNineB

variable {G : Type*} [Group G]

/-- **Peterfalvi (1.9)(b)** ((1.9), p. 6).  Let `|G| = a * b` with `a, b` coprime and let
`k` be coprime to `a`.  There is a ring automorphism `σ` of `ℂ` such that simultaneously
for **all** virtual characters `φ ∈ ℤ[Irr G]` and all `g : G`:

* `(σ ∘ φ)(g) = φ(g ^ k)` if the order of `g` divides `a`;
* `(σ ∘ φ)(g) = φ(g)` if the order of `g` is prime to `a`.

The book states this for a single character; the automorphism produced is uniform, which
is how (6.8.2.1) uses it (applied to `η^{τ₁} ∈ ℤ[Irr G]`). -/
theorem exists_complexRingEquiv_mapRingEquiv_eq_pow (G : Type*) [Group G] [Finite G]
    {a b k : ℕ} (hcard : Nat.card G = a * b) (hab : a.Coprime b) (hk : k.Coprime a) :
    ∃ σ : ℂ ≃+* ℂ,
      ∀ {φ : ClassFunction G ℂ}, φ ∈ ZIrr G → ∀ g : G,
        (orderOf g ∣ a → ClassFunction.mapRingEquiv σ φ g = φ (g ^ k)) ∧
        ((orderOf g).Coprime a → ClassFunction.mapRingEquiv σ φ g = φ g) := by
  have hcard0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have ha : a ≠ 0 := fun h => hcard0 (by rw [hcard, h, zero_mul])
  have hb : b ≠ 0 := fun h => hcard0 (by rw [hcard, h, mul_zero])
  obtain ⟨σ, hσa, hσb⟩ := exists_complexRingEquiv_pow_and_fixed ha hb hab hk
  refine ⟨σ, fun {φ} hφ g => ⟨fun hdvd => ?_, fun hcop => ?_⟩⟩
  · -- `orderOf g ∣ a`: eigenvalues are `a`-th roots of unity, on which `σ = (· ^ k)`
    refine mapRingEquiv_apply_eq_apply_pow_of_mem_ZIrr hφ σ (isOfFinOrder_of_finite g)
      fun ζ hζ => hσa ζ ?_
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, pow_mul, hζ, one_pow]
  · -- `orderOf g` prime to `a`: then `orderOf g ∣ b` and `σ` fixes the eigenvalues
    have hdvdb : orderOf g ∣ b := by
      have hdvd : orderOf g ∣ a * b := hcard ▸ orderOf_dvd_natCard g
      exact (Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd)
    have h := mapRingEquiv_apply_eq_apply_pow_of_mem_ZIrr hφ σ
      (isOfFinOrder_of_finite g) (k := 1) fun ζ hζ => by
        rw [pow_one]
        refine hσb ζ ?_
        obtain ⟨c, hc⟩ := hdvdb
        rw [hc, pow_mul, hζ, one_pow]
    simpa using h

end OneNineB

end OddOrder.RepresentationTheory

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
/-- **Virtual-character product over a cyclic-closed set is a rational integer** — the `ℤ[Irr]`
extension of `exists_int_prod_character_of_cyclicClosed`: `∏_{x∈A} φ(x)` is an algebraic integer
(values are, `isIntegral_apply_of_mem_ZIrr`) fixed by every `σ : ℂ ≃+* ℂ` (`σ` acts as a coprime
power `x ↦ x^k` permuting `A`), hence a rational integer. -/
theorem exists_int_prod_of_mem_ZIrr_of_cyclicClosed {G : Type*} [Group G] [Finite G]
    {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) {A : Finset G}
    (hclosed : ∀ x ∈ A, ∀ k : ℕ, k.Coprime (Nat.card G) → x ^ k ∈ A) :
    ∃ z : ℤ, (z : ℂ) = ∏ x ∈ A, φ x := by
  classical
  have hint : IsIntegral ℤ (∏ x ∈ A, φ x) :=
    IsIntegral.prod _ (fun x _ => isIntegral_apply_of_mem_ZIrr hφ x)
  have hfix : ∀ σ : ℂ ≃+* ℂ, σ (∏ x ∈ A, φ x) = ∏ x ∈ A, φ x := by
    intro σ
    have hN0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
    obtain ⟨k, hkcop, hkσ⟩ := exists_pow_of_complexRingEquiv σ hN0
    obtain ⟨hinj, himg⟩ := powClosed_image_pow_eq_of_cyclicClosed hclosed hkcop
    have hσval : ∀ w : G, σ (φ w) = φ (w ^ k) :=
      complexRingEquiv_apply_eq_apply_pow_of_mem_ZIrr hφ σ hkσ
    calc σ (∏ x ∈ A, φ x)
        = ∏ x ∈ A, φ (x ^ k) := by
          rw [map_prod]; exact Finset.prod_congr rfl (fun x _ => hσval x)
      _ = ∏ x ∈ A, φ x := by
          conv_rhs => rw [← himg]
          exact (Finset.prod_image (fun x hx y hy => hinj x hx y hy)).symm
  exact exists_int_of_isIntegral_of_forall_complexRingEquiv_fixed hint hfix

open OddOrder.RepresentationTheory in
/-- **[Isaacs] Lemma 3.14 (product form, virtual characters)**: for `φ ∈ ℤ[Irr G]` nowhere zero
on a cyclic-closed `Finset A`, `∏_{x∈A} ‖φ(x)‖² ≥ 1` — the product of the values is a *nonzero*
rational integer (`exists_int_prod_of_mem_ZIrr_of_cyclicClosed`). -/
theorem one_le_prod_normSq_of_mem_ZIrr_of_cyclicClosed {G : Type*} [Group G] [Finite G]
    {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) {A : Finset G}
    (hclosed : ∀ x ∈ A, ∀ k : ℕ, k.Coprime (Nat.card G) → x ^ k ∈ A)
    (hne : ∀ x ∈ A, φ x ≠ 0) :
    1 ≤ ∏ x ∈ A, ‖φ x‖ ^ 2 := by
  obtain ⟨z, hz⟩ := exists_int_prod_of_mem_ZIrr_of_cyclicClosed hφ hclosed
  have hprodne : (∏ x ∈ A, φ x) ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
  have hz0 : z ≠ 0 := by
    intro h
    apply hprodne
    rw [← hz, h, Int.cast_zero]
  have hnorm : ∏ x ∈ A, ‖φ x‖ ^ 2 = ‖(z : ℂ)‖ ^ 2 := by
    rw [Finset.prod_pow, ← norm_prod, ← hz]
  rw [hnorm]
  have hzabs : (1 : ℝ) ≤ ‖(z : ℂ)‖ := by
    rw [Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hz0
  nlinarith [hzabs, norm_nonneg ((z : ℂ))]

end OddOrder.Algebra

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/Machinery135.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Self inner-sum as a real squared-norm sum** (general `ClassFunction` identity).

For any class function `α : H → ℂ`, the unscaled self inner sum `Σ_g α(g)·conj(α(g))` equals the
real sum of squared norms `Σ_g ‖α(g)‖²` cast to `ℂ`.  This is the bridge between the abstract
`ClassFunction.innerSum`/`inner` API and the concrete `Σ |α(g)|²` quantities of Peterfalvi's norm
estimates (13.6)–(13.10); combined with `Σ_{H#} = Σ_H − |α(1)|²` it converts every Dade-norm
inequality into an elementary squared-norm sum.  A general fact for any finite group `H`. -/
theorem innerSum_self_eq_sum_normSq {H : Type*} [Group H] [Fintype H]
    (α : ClassFunction H ℂ) :
    ClassFunction.innerSum α α = ((∑ g : H, ‖α g‖ ^ 2 : ℝ) : ℂ) := by
  rw [ClassFunction.innerSum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← starRingEnd_apply, RCLike.mul_conj]
  norm_cast

/-- **Parseval identity for class functions** (general): `Σ_g ‖α(g)‖² = |H| · ⟨α, α⟩`.

The full squared-norm sum equals `|H|` times the normalized self inner product `⟨α,α⟩ = ‖α‖²`.
Combined with `Σ_{H#} = Σ_H − ‖α(1)‖²` this is precisely the Parseval relation `s + d² = |H|·n`
consumed by `caseB_eta_norm_core` (the (13.7) core): it lets the cascade read off `s = ∑_{H#}|α|²`
from the abstract inner product `n = ⟨α,α⟩`.  Immediate from `innerSum_self_eq_sum_normSq` and
`ClassFunction.card_mul_inner`. -/
theorem sum_normSq_eq_card_mul_inner {H : Type*} [Group H] [Fintype H]
    [Invertible (Nat.card H : ℂ)] (α : ClassFunction H ℂ) :
    ((∑ g : H, ‖α g‖ ^ 2 : ℝ) : ℂ) = (Nat.card H : ℂ) * ClassFunction.inner α α := by
  rw [← innerSum_self_eq_sum_normSq, ClassFunction.card_mul_inner]

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- The defining property of `normSqSumQ` on its good domain. -/
theorem normSqSumQ_spec {H : Type*} [Group H] {A : Finset H} {χ : ClassFunction H ℂ}
    (h : ∃ n : ℕ, (n : ℝ) = ∑ x ∈ A, ‖χ x‖ ^ 2) :
    ((normSqSumQ A χ : ℚ) : ℝ) = ∑ x ∈ A, ‖χ x‖ ^ 2 := by
  rw [normSqSumQ, dif_pos h]
  exact_mod_cast Classical.choose_spec h

open scoped FiniteInduce in
/-- **`η₁₀` is a virtual character of `G`** — real content of the 3002-threaded grid:
`η₁₀ = τ₃(ω₁₀)` (`eta_eq_tau_omega`), `ω₁₀ ∈ ZIrr W` (`omega_mem_ZIrr`), and `τ₃` preserves
virtual characters (`tau3_mem_ZIrr`). -/
theorem Hypothesis.eta10_mem_ZIrr [Finite G] (hyp : Hypothesis (G := G)) :
    hyp.eta10 ∈ ZIrr G := by
  rw [Hypothesis.eta10, hyp.eta_eq_tau_omega]
  exact hyp.tau3_mem_ZIrr _ (hyp.omega_mem_ZIrr _ _)

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

section CountingLayer

open OddOrder.GroupTheory

/-- `|T| = |Q|·(vd)·p` — the `T`-side order decomposition, read off the reconciled type-`P`
datum (`M_complement`/`derived_complement` of `reconciled_typePData_T`) with `|V| = vd` and
`|W₂| = p`. -/
theorem Hypothesis.card_T_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.T = Nat.card ↥hyp.Q * (hyp.v * hyp.d) * hyp.p := by
  obtain ⟨tpd, hU, hW1, -⟩ := reconciled_typePData_T hG hyp
  -- `|T| = |T'|·p`.
  have hle : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have h1 := tpd.M_complement.card_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.W1_le).toEquiv,
    hW1, ← hyp.p_eq_card_W2] at h1
  -- `|T'| = |Q|·|V| = |Q|·(vd)`.
  have h2 := tpd.derived_complement.card_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.H_le).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.U_le).toEquiv, tpd.H_eq, ← hyp.Q_eq_TF,
    hU, hyp.card_V_eq_vd] at h2
  rw [← h1, ← h2]

open scoped Classical in
/-- `|K^#| = |K| − 1`, `Finset` form. -/
theorem card_sharp_toFinset [Finite G] (K : Subgroup G) :
    (Set.toFinite (sharpSubgroup K)).toFinset.card = Nat.card ↥K - 1 := by
  have : Fintype G := Fintype.ofFinite G
  classical
  have h : (Set.toFinite (sharpSubgroup K)).toFinset
      = (Finset.univ.filter (· ∈ K)).erase 1 := by
    ext x
    rw [Set.Finite.mem_toFinset, Finset.mem_erase, Finset.mem_filter]
    change x ∈ (K : Set G) \ {1} ↔ _
    rw [Set.mem_sdiff, Set.mem_singleton_iff]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, Finset.mem_univ _, h1⟩, fun ⟨h2, _, h1⟩ => ⟨h1, h2⟩⟩
  rw [h, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, K.one_mem⟩)]
  congr 1
  rw [Nat.card_eq_fintype_card]
  simp [Fintype.card_subtype]

/-- **Peterfalvi (13.10.3), ℕ form**: `|G| = 1 + |G₀| + [G:S]·|H^#| + [G:T]·|Q^#|` — the
`f = 1` instance of the four-piece split. -/
theorem Hypothesis.card_univ_split [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (hcardQ : Nat.card ↥hyp.Q = hyp.q ^ hyp.p) (hvd : hyp.v * hyp.d ≠ 1) :
    Nat.card G = 1 + hyp.G0Finset.card
      + hyp.S.index * (Nat.card ↥hyp.H - 1) + hyp.T.index * (Nat.card ↥hyp.Q - 1) := by
  have : Fintype G := Fintype.ofFinite G
  have h := hyp.sum_univ_split hG (fun _ => (1 : ℕ)) (fun _ _ => rfl) hcardQ hvd
  simp only [← Finset.card_eq_sum_ones, Finset.card_univ, smul_eq_mul,
    card_sharp_toFinset] at h
  rw [Nat.card_eq_fintype_card]
  exact h

open scoped FiniteInduce in
/-- **Global Parseval four-piece split** for a norm-`1` class function (the shared spine of the
Peterfalvi (13.10.1)/(13.10.2) estimates):

  `|G| = ‖φ(1)‖² + ∑_{G₀}‖φ‖² + [G:S]·∑_{H^#}‖φ‖² + [G:T]·∑_{Q^#}‖φ‖²`.

The total `∑_G ‖φ‖² = |G|·⟨φ,φ⟩ = |G|` (Parseval, `sum_normSq_eq_card_mul_inner`), split by the
four-piece decomposition `sum_univ_split` (the summand `‖φ(·)‖²` is conjugation-invariant since
`φ` is a class function). -/
theorem Hypothesis.global_normSq_split [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (φ : ClassFunction G ℂ)
    (hn : ClassFunction.inner φ φ = 1)
    (hcardQ : Nat.card ↥hyp.Q = hyp.q ^ hyp.p) (hvd : hyp.v * hyp.d ≠ 1) :
    (Nat.card G : ℝ)
      = ‖φ 1‖ ^ 2 + (∑ x ∈ hyp.G0Finset, ‖φ x‖ ^ 2)
        + hyp.S.index • (∑ x ∈ (Set.toFinite (sharpSubgroup hyp.H)).toFinset, ‖φ x‖ ^ 2)
        + hyp.T.index • (∑ x ∈ (Set.toFinite (sharpSubgroup hyp.Q)).toFinset, ‖φ x‖ ^ 2) := by
  have hsplit := hyp.sum_univ_split hG (fun x => ‖φ x‖ ^ 2)
    (fun g x => by
      show ‖φ (g * x * g⁻¹)‖ ^ 2 = ‖φ x‖ ^ 2
      rw [ClassFunction.conj_eq φ x g]) hcardQ hvd
  have htotal : ((∑ x : G, ‖φ x‖ ^ 2 : ℝ) : ℂ) = (Nat.card G : ℂ) := by
    rw [sum_normSq_eq_card_mul_inner, hn, mul_one]
  have htotalR : ∑ x : G, ‖φ x‖ ^ 2 = (Nat.card G : ℝ) := by exact_mod_cast htotal
  rw [← htotalR, hsplit]

end CountingLayer

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/Canonicalization.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- The (13.4) case-(b) parameters, unpacked: `d = 1`, `v ≥ 2`, and (for the type-V exclusion
of the counting layer) `vd ≠ 1`. -/
theorem Hypothesis.caseB_vd_facts (hyp : Hypothesis (G := G))
    (hD : hyp.D = ⊥) (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1)) :
    hyp.d = 1 ∧ 2 ≤ hyp.v ∧ hyp.v * hyp.d ≠ 1 := by
  have hd1 : hyp.d = 1 := by rw [hyp.d_eq_card_D, hD, Subgroup.card_bot]
  have hq3 : 3 ≤ hyp.q := hyp.three_le_q
  have hqp_ge : hyp.q * hyp.q ≤ hyp.q ^ hyp.p := by
    calc hyp.q * hyp.q = hyp.q ^ 2 := (sq hyp.q).symm
      _ ≤ hyp.q ^ hyp.p := Nat.pow_le_pow_right (by omega)
        (by have := hyp.three_le_p; omega)
  have hv2 : 2 ≤ hyp.v := by
    rw [hv, Nat.le_div_iff_mul_le (by omega : 0 < hyp.q - 1)]
    have h3q : 3 * hyp.q ≤ hyp.q * hyp.q := Nat.mul_le_mul_right _ hq3
    omega
  exact ⟨hd1, hv2, by rw [hd1, mul_one]; omega⟩

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/NormEstimates.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **AM–GM via `log`** (analytic core of [Is] Lemma 3.14): for positive reals whose product is
`≥ 1`, the sum is at least the count.  This powers Peterfalvi (13.9.b): for a cyclic-equivalence
class `[a] = {a^k : gcd(k, |⟨a⟩|) = 1}`, the values `χ(a^k)` are the Galois conjugates of `χ(a)`,
so `∏_k |χ(a^k)|² = |N(χ(a))|² ≥ 1` whenever `χ(a) ≠ 0` (the field norm of a nonzero algebraic
integer is a nonzero rational integer), whence `∑_k |χ(a^k)|² ≥ φ(|⟨a⟩|) = |[a]|`; summing over the
cyclic classes gives `∑_{x∈A}|χ(x)|² ≥ |A|` for any cyclic-closed `A` with `χ ≠ 0` on `A`.
Proof: `log x ≤ x − 1` summed gives `0 ≤ log (∏ f) ≤ ∑ (f − 1) = ∑ f − |s|`. -/
theorem sum_ge_card_of_one_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hpos : ∀ i ∈ s, 0 < f i) (hprod : 1 ≤ ∏ i ∈ s, f i) :
    (s.card : ℝ) ≤ ∑ i ∈ s, f i := by
  have hlog : ∑ i ∈ s, Real.log (f i) ≤ ∑ i ∈ s, (f i - 1) :=
    Finset.sum_le_sum (fun i hi => Real.log_le_sub_one_of_pos (hpos i hi))
  have hprodlog : (0 : ℝ) ≤ ∑ i ∈ s, Real.log (f i) := by
    rw [← Real.log_prod (fun i hi => (hpos i hi).ne')]
    exact Real.log_nonneg hprod
  have hsum : (0 : ℝ) ≤ ∑ i ∈ s, (f i - 1) := le_trans hprodlog hlog
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  linarith

/-- **[Isaacs] Lemma 3.14 (sum form, virtual characters)**: a virtual character nowhere zero on
a cyclic-closed `Finset A` has `∑_{x∈A}‖φ(x)‖² ≥ |A|` — the `ℤ[Irr]` extension of
`sum_normSq_ge_ncard_of_isCharacter_of_cyclicClosed`, combining the Galois product bound
`one_le_prod_normSq_of_mem_ZIrr_of_cyclicClosed` with the AM–GM
`sum_ge_card_of_one_le_prod`. -/
theorem sum_normSq_ge_card_of_mem_ZIrr_of_cyclicClosed {H : Type*} [Group H] [Finite H]
    {φ : ClassFunction H ℂ} (hφ : φ ∈ ZIrr H) {A : Finset H}
    (hclosed : ∀ x ∈ A, ∀ k : ℕ, k.Coprime (Nat.card H) → x ^ k ∈ A)
    (hne : ∀ x ∈ A, φ x ≠ 0) :
    (A.card : ℝ) ≤ ∑ x ∈ A, ‖φ x‖ ^ 2 :=
  sum_ge_card_of_one_le_prod A (fun x => ‖φ x‖ ^ 2)
    (fun x hx => pow_pos (norm_pos_iff.mpr (hne x hx)) 2)
    (OddOrder.Algebra.one_le_prod_normSq_of_mem_ZIrr_of_cyclicClosed hφ hclosed hne)

/-- **The nonvanishing locus of a virtual character inside a cyclic-closed set is cyclic-closed**
(Peterfalvi (1.9.b)): for `k` coprime to `|G|` there is `σ : ℂ ≃+* ℂ` with
`σ(φ(x)) = φ(x^k)` (`exists_complexRingEquiv_mapRingEquiv_eq_pow` with `a = |G|`, `b = 1`),
and ring automorphisms preserve nonvanishing. -/
theorem filter_ne_zero_cyclicClosed [Finite G] {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G)
    {A : Finset G} (hclosed : ∀ x ∈ A, ∀ k : ℕ, k.Coprime (Nat.card G) → x ^ k ∈ A) :
    ∀ x ∈ A.filter (fun y => φ y ≠ 0), ∀ k : ℕ, k.Coprime (Nat.card G) →
      x ^ k ∈ A.filter (fun y => φ y ≠ 0) := by
  classical
  intro x hx k hk
  obtain ⟨hxA, hxne⟩ := Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨hclosed x hxA k hk, ?_⟩
  obtain ⟨σ, hσ⟩ := OddOrder.RepresentationTheory.exists_complexRingEquiv_mapRingEquiv_eq_pow G
    (a := Nat.card G) (b := 1) (mul_one _).symm (Nat.coprime_one_right _) hk
  have hval : ClassFunction.mapRingEquiv σ φ x = φ (x ^ k) :=
    (hσ hφ x).1 (orderOf_dvd_natCard x)
  rw [ClassFunction.mapRingEquiv_apply] at hval
  rw [← hval]
  simpa using hxne

/-- **Peterfalvi (13.10), arithmetic core** (04.15 pp.85–86): the (13.6)–(13.9) norm estimates,
the disjoint-union counting identity, and the (13.4) counting values force
`u / c > m p^(q-1) / q`.  All character-theoretic inputs are explicit hypotheses. -/
theorem analytic_inequality_arith {p q u c : ℕ} {m gi slam seta g0 LS HS TT QT : ℚ}
    (hp2 : 2 ≤ p) (hq2 : 2 ≤ q) (hc0 : 0 < c)
    (h1 : 1 ≥ gi + slam + 1 - LS)
    (h2 : 1 ≥ gi + seta + HS + TT)
    (h3 : 1 = gi + g0 + HS + QT)
    (h139b : g0 ≤ slam + seta)
    (hgi : 0 < gi)
    (hLS : LS = ((u : ℚ) * (q : ℚ)) / ((c : ℚ) * (p : ℚ) ^ q))
    (hTT : TT = 1 / (p : ℚ) - 1 / ((p : ℚ) * ((q : ℚ) - 1))
      + 1 / ((p : ℚ) * ((q : ℚ) - 1) * (q : ℚ) ^ p))
    (hQT : QT = ((q : ℚ) - 1) / ((p : ℚ) * (q : ℚ) ^ p))
    (hm : m = 1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p
      + 1 / (((q : ℚ) - 1) * (q : ℚ) ^ p)) :
    (u : ℚ) / (c : ℚ) > m * ((p : ℚ) ^ (q - 1)) / (q : ℚ) := by
  have hpQ : (0 : ℚ) < (p : ℚ) := by exact_mod_cast (show 0 < p by omega)
  have hqQ : (0 : ℚ) < (q : ℚ) := by exact_mod_cast (show 0 < q by omega)
  have hcQ : (0 : ℚ) < (c : ℚ) := by exact_mod_cast hc0
  have hq1 : (0 : ℚ) < (q : ℚ) - 1 := by
    have h2q : (2 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq2
    linarith
  have hqpowp : (0 : ℚ) < (q : ℚ) ^ p := by positivity
  have hppow1 : (0 : ℚ) < (p : ℚ) ^ (q - 1) := by positivity
  have hppowq : (0 : ℚ) < (p : ℚ) ^ q := by positivity
  have hStageA : LS > TT - QT := by linarith
  have hTTQT : TT - QT = m / (p : ℚ) := by
    rw [hTT, hQT, hm]
    field_simp
    ring
  rw [hTTQT, hLS] at hStageA
  have hpexp : (p : ℚ) ^ q = (p : ℚ) ^ (q - 1) * (p : ℚ) := by
    rw [← pow_succ]
    congr 1
    omega
  have hfac : (0 : ℚ) < (q : ℚ) / (p : ℚ) ^ q := by positivity
  have e1 : ((u : ℚ) * (q : ℚ)) / ((c : ℚ) * (p : ℚ) ^ q)
      = ((u : ℚ) / (c : ℚ)) * ((q : ℚ) / (p : ℚ) ^ q) := by
    field_simp
  have e2 : m / (p : ℚ)
      = (m * ((p : ℚ) ^ (q - 1)) / (q : ℚ)) * ((q : ℚ) / (p : ℚ) ^ q) := by
    rw [hpexp]
    field_simp
  rw [e1, e2] at hStageA
  exact lt_of_mul_lt_mul_right hStageA (le_of_lt hfac)

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CaseBEndgameSupply/HSharpChosenBase.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

section

open scoped FiniteInduce in
/-- **Peterfalvi (13.2.d)/(13.3), Core form**: `λ^{τ₁}` is a norm-one virtual
character.  The `P`-nonkernel witness stored in `LambdaClusterData` is exactly the guard needed
by the honest `CharacterDegreeCore` coherence fields. -/
theorem lambda_tau1_norm_one_core [Finite G] {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp) :
    core.tau1S lam.lambda ∈ ZIrr G ∧
      ClassFunction.inner (core.tau1S lam.lambda) (core.tau1S lam.lambda) = 1 ∧
      ClassFunction.inner lam.lambda lam.lambda = 1 := by
  have := hyp.finiteG
  obtain ⟨θ, hθirr, -, hlamEq, x₀, hx₀P, hx₀ker⟩ :=
    lam.lambda_induced_from_PC_linear
  have hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
      Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ) := by
    intro hsub
    exact hx₀ker (hsub (by
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact hx₀P))
  have hnorm : ClassFunction.inner lam.lambda lam.lambda = 1 := by
    have h := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨lam.lambda, lam.lambda_irreducible⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S)
      ⟨lam.lambda, lam.lambda_irreducible⟩
    simpa using h
  refine ⟨?_, ?_, hnorm⟩
  · rw [hlamEq]
    exact core.tau1S_induce_mem_ZIrr θ hθirr hθP
  · rw [hlamEq, core.tau1S_inner_induce θ θ hθirr hθirr hθP hθP, ← hlamEq]
    exact hnorm

end

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S15_CaseBEndgameSupply/AnalyticRelayer.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

section

open scoped FiniteInduce in
/-- **Peterfalvi (13.6) + Parseval, Core form**: the first analytic estimate in (13.10).

The norm-one virtual character and the sharp norm bound are the honest Core outputs
`lambda_tau1_norm_one_core` and `lambda_tau1_sharp_norm_lower_core`.  The two case-B
values are explicit inputs; `|Q| = q^p` is the unconditional (13.2.b) theorem. -/
theorem CharacterDegreeCore.analyticEstimate_lambda_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (hD : hyp.D = ⊥) (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1)) :
    (1 : ℚ) ≥ 1 / (Nat.card G : ℚ)
        + normSqSumQ hyp.G0Finset (core.tau1S lam.lambda) / (Nat.card G : ℚ) + 1
        - (hyp.u : ℚ) * (hyp.q : ℚ) / ((hyp.c : ℚ) * (hyp.p : ℚ) ^ hyp.q) := by
  classical
  obtain ⟨hZ, hn, -⟩ := lambda_tau1_norm_one_core core lam
  have hQ : Nat.card ↥hyp.Q = hyp.q ^ hyp.p := hyp.card_Q_eq_qp hG
  obtain ⟨hd1, hv2, hvd⟩ := hyp.caseB_vd_facts hD hv
  set φ : ClassFunction G ℂ := core.tau1S lam.lambda with hφdef
  have hsplit := hyp.global_normSq_split hG φ hn hQ hvd
  have hone : (1 : ℝ) ≤ ‖φ 1‖ ^ 2 :=
    OddOrder.RepresentationTheory.one_le_normSq_apply_one_of_mem_ZIrr_of_inner_self_one hZ hn
  have hsharp := core.lambda_tau1_sharp_norm_lower_core hG lam
  rw [← hφdef] at hsharp
  have hQnonneg : (0 : ℝ) ≤ (hyp.T.index : ℝ)
      * ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.Q)).toFinset, ‖φ x‖ ^ 2 := by
    have h1 : (0 : ℝ) ≤ ∑ x ∈ (Set.toFinite (sharpSubgroup hyp.Q)).toFinset, ‖φ x‖ ^ 2 :=
      Finset.sum_nonneg fun x _ => by positivity
    positivity
  have hGal := OddOrder.Algebra.exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed hZ
    hyp.G0Finset_cyclicClosed
  have hspec := normSqSumQ_spec hGal
  have hg0 : (0 : ℝ) < (Nat.card G : ℝ) := by exact_mod_cast Nat.card_pos (α := G)
  have hGeq : (Nat.card G : ℝ)
      = (hyp.p : ℝ) ^ hyp.q * ((hyp.u : ℝ) * (hyp.c : ℝ)) * (hyp.q : ℝ)
        * (hyp.S.index : ℝ) := by
    have h := hyp.S.card_mul_index
    rw [hyp.card_S_val hG] at h
    exact_mod_cast h.symm
  have hc0 : (0 : ℝ) < (hyp.c : ℝ) := by
    have : 0 < hyp.c := by rw [hyp.c_eq_card_C]; exact Nat.card_pos
    exact_mod_cast this
  have hp0 : (0 : ℝ) < (hyp.p : ℝ) := by
    have := hyp.three_le_p
    exact_mod_cast (by omega : 0 < hyp.p)
  rw [ge_iff_le, ← Rat.cast_le (K := ℝ)]
  push_cast
  rw [hspec]
  set s : ℝ := ∑ x ∈ hyp.G0Finset, ‖φ x‖ ^ 2 with hsdef
  set w : ℝ := (hyp.u : ℝ) * (hyp.q : ℝ) /
    ((hyp.c : ℝ) * (hyp.p : ℝ) ^ hyp.q) with hwdef
  have hwg : w * (Nat.card G : ℝ) =
      (hyp.S.index : ℝ) * ((hyp.u : ℝ) * (hyp.q : ℝ)) ^ 2 := by
    rw [hwdef, hGeq]
    field_simp
  have hSidx0 : (0 : ℝ) ≤ (hyp.S.index : ℝ) := by positivity
  have hkey : 1 + s ≤ w * (Nat.card G : ℝ) := by
    rw [hwg]
    have hSGeq : (hyp.S.index : ℝ) * (Nat.card ↥hyp.S : ℝ) = (Nat.card G : ℝ) := by
      exact_mod_cast mul_comm (Nat.card ↥hyp.S) hyp.S.index ▸ hyp.S.card_mul_index
    have huq : ((hyp.u * hyp.q : ℕ) : ℝ) = (hyp.u : ℝ) * (hyp.q : ℝ) := by
      push_cast
      ring
    rw [huq] at hsharp
    have hHbound := mul_le_mul_of_nonneg_left hsharp hSidx0
    rw [nsmul_eq_mul, nsmul_eq_mul] at hsplit
    linarith [hsplit, hone, hHbound, hQnonneg, hSGeq]
  have hdiv : (1 + s) / (Nat.card G : ℝ) ≤ w :=
    (div_le_iff₀ hg0).mpr (by linarith [hkey])
  calc 1 / (Nat.card G : ℝ) + s / (Nat.card G : ℝ) + 1 - w
      = (1 + s) / (Nat.card G : ℝ) + 1 - w := by rw [add_div]
    _ ≤ w + 1 - w := by linarith [hdiv]
    _ = 1 := by ring

end

section

/-- **Peterfalvi (13.9.a), explicit case-B facts form**: the four-piece disjoint-cover
counting identity.  This is the legacy `analyticCounting_disjointCover` proof with the
uninhabitable character-degree obtain removed; only the two genuine (13.4) values are
passed in. -/
theorem Hypothesis.analyticCounting_disjointCover_of_caseB_facts [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hD : hyp.D = ⊥) (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1)) :
    (1 : ℚ) = 1 / (Nat.card G : ℚ) + (hyp.G0Finset.card : ℚ) / (Nat.card G : ℚ)
        + ((Nat.card hyp.H - 1 : ℕ) : ℚ) / (Nat.card hyp.S : ℚ)
        + ((hyp.q : ℚ) - 1) / ((hyp.p : ℚ) * (hyp.q : ℚ) ^ hyp.p) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hQ : Nat.card ↥hyp.Q = hyp.q ^ hyp.p := hyp.card_Q_eq_qp hG
  have hd1 : hyp.d = 1 := by rw [hyp.d_eq_card_D, hD, Subgroup.card_bot]
  have hq3 : 3 ≤ hyp.q := hyp.three_le_q
  have hp3 : 3 ≤ hyp.p := hyp.three_le_p
  have hqp_ge : hyp.q * hyp.q ≤ hyp.q ^ hyp.p := by
    calc hyp.q * hyp.q = hyp.q ^ 2 := (sq hyp.q).symm
      _ ≤ hyp.q ^ hyp.p := Nat.pow_le_pow_right (by omega) (by omega)
  have hv2 : 2 ≤ hyp.v := by
    rw [hv, Nat.le_div_iff_mul_le (by omega : 0 < hyp.q - 1)]
    have h3q : 3 * hyp.q ≤ hyp.q * hyp.q := Nat.mul_le_mul_right _ hq3
    omega
  have hvd : hyp.v * hyp.d ≠ 1 := by rw [hd1, mul_one]; omega
  have hsplit := hyp.card_univ_split hG hQ hvd
  have key : (Nat.card G : ℚ) = 1 + (hyp.G0Finset.card : ℚ)
      + (hyp.S.index : ℚ) * ((Nat.card ↥hyp.H - 1 : ℕ) : ℚ)
      + (hyp.T.index : ℚ) * ((Nat.card ↥hyp.Q - 1 : ℕ) : ℚ) := by
    exact_mod_cast hsplit
  have hG0 : (0 : ℚ) < (Nat.card G : ℚ) := by exact_mod_cast Nat.card_pos (α := G)
  have hS0 : (0 : ℚ) < (Nat.card ↥hyp.S : ℚ) := by
    exact_mod_cast Nat.card_pos (α := ↥hyp.S)
  have hT0 : (0 : ℚ) < (Nat.card ↥hyp.T : ℚ) := by
    exact_mod_cast Nat.card_pos (α := ↥hyp.T)
  have hSidx : (hyp.S.index : ℚ) * (Nat.card ↥hyp.S : ℚ) = (Nat.card G : ℚ) := by
    exact_mod_cast mul_comm (Nat.card ↥hyp.S) hyp.S.index ▸ hyp.S.card_mul_index
  have hTidx : (hyp.T.index : ℚ) * (Nat.card ↥hyp.T : ℚ) = (Nat.card G : ℚ) := by
    exact_mod_cast mul_comm (Nat.card ↥hyp.T) hyp.T.index ▸ hyp.T.card_mul_index
  have hSidx0 : (hyp.S.index : ℚ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hSidx
    exact hG0.ne' hSidx.symm
  have hTidx0 : (hyp.T.index : ℚ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hTidx
    exact hG0.ne' hTidx.symm
  have hq1 : (1 : ℕ) ≤ hyp.q := by omega
  have hqp1 : (1 : ℕ) ≤ hyp.q ^ hyp.p := Nat.one_le_pow _ _ (by omega)
  have hdvd : (hyp.q - 1) ∣ (hyp.q ^ hyp.p - 1) := by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow hyp.q 1 hyp.p
  have hvq : (hyp.v : ℚ) * ((hyp.q : ℚ) - 1) = (hyp.q : ℚ) ^ hyp.p - 1 := by
    have h := Nat.div_mul_cancel hdvd
    rw [← hv] at h
    have := congrArg (Nat.cast (R := ℚ)) h
    push_cast [Nat.cast_sub hq1, Nat.cast_sub hqp1] at this
    convert this using 2
  have hTval : (Nat.card ↥hyp.T : ℚ) =
      (hyp.q : ℚ) ^ hyp.p * (hyp.v : ℚ) * (hyp.p : ℚ) := by
    have h := hyp.card_T_eq hG
    rw [hQ, hd1, mul_one] at h
    exact_mod_cast h
  have hQ1 : ((Nat.card ↥hyp.Q - 1 : ℕ) : ℚ) = (hyp.q : ℚ) ^ hyp.p - 1 := by
    rw [hQ, Nat.cast_sub hqp1]
    push_cast
    ring
  have hterm3 : ((Nat.card ↥hyp.H - 1 : ℕ) : ℚ) / (Nat.card ↥hyp.S : ℚ)
      = (hyp.S.index : ℚ) * ((Nat.card ↥hyp.H - 1 : ℕ) : ℚ) /
        (Nat.card G : ℚ) := by
    rw [← hSidx, mul_div_mul_left _ _ hSidx0]
  have hv0 : (hyp.v : ℚ) ≠ 0 := by
    have : (2 : ℚ) ≤ (hyp.v : ℚ) := by exact_mod_cast hv2
    linarith
  have hq10 : (hyp.q : ℚ) - 1 ≠ 0 := by
    have : (3 : ℚ) ≤ (hyp.q : ℚ) := by exact_mod_cast hq3
    linarith
  have hp0 : (hyp.p : ℚ) ≠ 0 := by
    have : (3 : ℚ) ≤ (hyp.p : ℚ) := by exact_mod_cast hp3
    linarith
  have hqp0 : (hyp.q : ℚ) ^ hyp.p ≠ 0 := by
    have : (1 : ℚ) ≤ (hyp.q : ℚ) ^ hyp.p := by exact_mod_cast hqp1
    linarith
  have hterm4 : ((hyp.q : ℚ) - 1) / ((hyp.p : ℚ) * (hyp.q : ℚ) ^ hyp.p)
      = (hyp.T.index : ℚ) * ((Nat.card ↥hyp.Q - 1 : ℕ) : ℚ) /
        (Nat.card G : ℚ) := by
    rw [hQ1, ← hvq, ← hTidx, hTval]
    field_simp
  rw [hterm3, hterm4, ← add_div, ← add_div, ← add_div, ← key, div_self hG0.ne']

end

section

open scoped FiniteInduce in
/-- **Peterfalvi (13.9.b), Core form**: the generic-set proportion is bounded by
the two normalized squared-norm sums.  The two nonvanishing loci cover `G₀` by
`G0_nonvanishing_dichotomy_core`; cyclic closure and Isaacs Lemma 3.14 bound each
locus by the corresponding virtual-character norm sum. -/
theorem CharacterDegreeCore.analyticEstimate_galois_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp) :
    (hyp.G0Finset.card : ℚ) / (Nat.card G : ℚ)
      ≤ normSqSumQ hyp.G0Finset (core.tau1S lam.lambda) / (Nat.card G : ℚ)
        + normSqSumQ hyp.G0Finset hyp.eta10 / (Nat.card G : ℚ) := by
  classical
  obtain ⟨hZlam, -, -⟩ := lambda_tau1_norm_one_core core lam
  have hZeta := hyp.eta10_mem_ZIrr
  set φ : ClassFunction G ℂ := core.tau1S lam.lambda with hφdef
  set A : Finset G := hyp.G0Finset.filter (fun y => φ y ≠ 0) with hA
  set B : Finset G := hyp.G0Finset.filter (fun y => hyp.eta10 y ≠ 0) with hB
  have hdich := core.G0_nonvanishing_dichotomy_core hG lam
  have hcover : hyp.G0Finset ⊆ A ∪ B := by
    intro x hx
    rcases hdich x hx with h | h
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hx, by rw [← hφdef] at h; exact h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, h⟩)
  have hcard : hyp.G0Finset.card ≤ A.card + B.card :=
    le_trans (Finset.card_le_card hcover) (Finset.card_union_le _ _)
  have hgeA : (A.card : ℝ) ≤ ∑ x ∈ A, ‖φ x‖ ^ 2 :=
    sum_normSq_ge_card_of_mem_ZIrr_of_cyclicClosed hZlam
      (filter_ne_zero_cyclicClosed hZlam hyp.G0Finset_cyclicClosed)
      (fun x hx => (Finset.mem_filter.mp hx).2)
  have hgeB : (B.card : ℝ) ≤ ∑ x ∈ B, ‖hyp.eta10 x‖ ^ 2 :=
    sum_normSq_ge_card_of_mem_ZIrr_of_cyclicClosed hZeta
      (filter_ne_zero_cyclicClosed hZeta hyp.G0Finset_cyclicClosed)
      (fun x hx => (Finset.mem_filter.mp hx).2)
  have hsubA : ∑ x ∈ A, ‖φ x‖ ^ 2 ≤ ∑ x ∈ hyp.G0Finset, ‖φ x‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun x _ _ => by positivity)
  have hsubB : ∑ x ∈ B, ‖hyp.eta10 x‖ ^ 2 ≤
      ∑ x ∈ hyp.G0Finset, ‖hyp.eta10 x‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun x _ _ => by positivity)
  have hspecLam := normSqSumQ_spec
    (OddOrder.Algebra.exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed hZlam
      hyp.G0Finset_cyclicClosed)
  have hspecEta := normSqSumQ_spec
    (OddOrder.Algebra.exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed hZeta
      hyp.G0Finset_cyclicClosed)
  have hg0 : (0 : ℝ) < (Nat.card G : ℝ) := by exact_mod_cast Nat.card_pos (α := G)
  rw [← Rat.cast_le (K := ℝ)]
  push_cast
  rw [hspecLam, hspecEta, ← add_div]
  have hnum : (hyp.G0Finset.card : ℝ) ≤
      (∑ x ∈ hyp.G0Finset, ‖φ x‖ ^ 2) +
        ∑ x ∈ hyp.G0Finset, ‖hyp.eta10 x‖ ^ 2 := by
    have hcard' : (hyp.G0Finset.card : ℝ) ≤ (A.card : ℝ) + (B.card : ℝ) := by
      exact_mod_cast hcard
    linarith [hgeA, hgeB, hsubA, hsubB]
  gcongr

end

section

/-- **Peterfalvi (13.6)–(13.9), Core form**: the four honest estimates consumed by
the arithmetic core of (13.10).  Every character-theoretic input is expressed through
`CharacterDegreeCore` and `LambdaClusterData`; the case-B structure is explicit. -/
theorem CharacterDegreeCore.analyticInequalityEstimates_core [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (hD : hyp.D = ⊥) (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1))
    (hQcomm : IsMulCommutative ↥hyp.Q) (pins : NuGridSupplyData hyp) :
    ∃ slam seta g0 HS : ℚ,
      (1 : ℚ) ≥ 1 / (Nat.card G : ℚ) + slam + 1
          - (hyp.u : ℚ) * (hyp.q : ℚ) / ((hyp.c : ℚ) * (hyp.p : ℚ) ^ hyp.q) ∧
        (1 : ℚ) ≥ 1 / (Nat.card G : ℚ) + seta + HS
          + (1 / (hyp.p : ℚ) - 1 / ((hyp.p : ℚ) * ((hyp.q : ℚ) - 1))
            + 1 / ((hyp.p : ℚ) * ((hyp.q : ℚ) - 1) * (hyp.q : ℚ) ^ hyp.p)) ∧
        (1 : ℚ) = 1 / (Nat.card G : ℚ) + g0 + HS
          + ((hyp.q : ℚ) - 1) / ((hyp.p : ℚ) * (hyp.q : ℚ) ^ hyp.p) ∧
        g0 ≤ slam + seta := by
  exact ⟨normSqSumQ hyp.G0Finset (core.tau1S lam.lambda) / (Nat.card G : ℚ),
    normSqSumQ hyp.G0Finset hyp.eta10 / (Nat.card G : ℚ),
    (hyp.G0Finset.card : ℚ) / (Nat.card G : ℚ),
    ((Nat.card hyp.H - 1 : ℕ) : ℚ) / (Nat.card hyp.S : ℚ),
    core.analyticEstimate_lambda_core hG lam hD hv,
    core.analyticEstimate_eta_core hG hD hv hQcomm pins,
    hyp.analyticCounting_disjointCover_of_caseB_facts hG hD hv,
    core.analyticEstimate_galois_core hG lam⟩

/-- **Peterfalvi (13.10), honest Core endpoint**: explicit case-B facts and the
Core/cluster character data force `u/c > m p^(q-1)/q`.

Unlike the legacy endpoint, this theorem returns the mathematical inequality directly;
it does not manufacture a `NormCascadeData` record whose proof flags carry no content. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {hyp : Hypothesis (G := G)}
    (core : CharacterDegreeCore hyp) (lam : LambdaClusterData hyp)
    (hD : hyp.D = ⊥) (hv : hyp.v = (hyp.q ^ hyp.p - 1) / (hyp.q - 1))
    (hQcomm : IsMulCommutative ↥hyp.Q) (pins : NuGridSupplyData hyp) :
    (hyp.u : ℚ) / (hyp.c : ℚ) >
      hyp.m * ((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ) / (hyp.q : ℚ) := by
  obtain ⟨slam, seta, g0, HS, h1, h2, h3, h139b⟩ :=
    core.analyticInequalityEstimates_core hG lam hD hv hQcomm pins
  have hc0 : 0 < hyp.c := by rw [hyp.c_eq_card_C]; exact Nat.card_pos
  have hgi : (0 : ℚ) < 1 / (Nat.card G : ℚ) := by
    have : 0 < Nat.card G := Nat.card_pos
    positivity
  have hpq : ((hyp.p ^ (hyp.q - 1) : ℕ) : ℚ) =
      (hyp.p : ℚ) ^ (hyp.q - 1) := by
    push_cast
    ring
  rw [hpq]
  exact analytic_inequality_arith hyp.p_prime.two_le hyp.q_prime.two_le hc0
    h1 h2 h3 h139b hgi rfl rfl rfl hyp.m_eq

end

end OddOrder.Peterfalvi.S15
