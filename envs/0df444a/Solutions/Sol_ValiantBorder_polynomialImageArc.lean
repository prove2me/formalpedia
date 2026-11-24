-- Prove2me | solution 1 for ValiantBorder.polynomialImageArc
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:00:26.049195+00:00
-- url     : https://prove2.me/submissions/5f4fc0ef-8a85-45f1-9b26-b88f3bde155b

/- Laurent curve selection for polynomial maps. The target statement is a consequence of
Guo, Saxena and Sinhababu, CCC 2018, Theorem 15, https://doi.org/10.4230/LIPIcs.CCC.2018.10.
The proof below constructs a branch with residue p over the original field ℂ.
The Newton–Puiseux proof and its attribution follow. -/
import Mathlib

/-!
Formal curve selection over the complex numbers by Noether normalization and Newton–Puiseux.
The four Puiseux modules below are from Dean Cureton’s Apache-2.0-licensed implementation,
https://github.com/deancureton/Puiseux/tree/73e78681d7bb78ddb202e29cb92ab3c16b723126 .
For this submission the module headers and imports have been combined into a single file.
Original copyright notices and the full license are reproduced below.
-/

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/


/-!
# The field of Puiseux series

This file defines the field of Puiseux series over a field `K` as a subfield of the Hahn series
field `HahnSeries ℚ K`, namely the directed union of the images of the embeddings
`LaurentSeries.toHahn K n : K((t)) →+* HahnSeries ℚ K` sending `t` to `t ^ (1 / n)`.

## Main definitions

* `LaurentSeries.expand K m`: the expansion ring endomorphism of `K((t))` sending `t` to `t ^ m`.
* `LaurentSeries.toHahn K n`: the ring embedding `K((t)) →+* HahnSeries ℚ K`
  sending `t` to `t ^ (1 / n)`.
* `PuiseuxSeries.subfield K`: the Puiseux subfield `⨆ n, (toHahn K n).fieldRange` of
  `HahnSeries ℚ K`.
* `PuiseuxSeries K`: the type of Puiseux series over `K`, a field, equipped with an algebra
  structure over `LaurentSeries K` via `toHahn K 1`.

## Main results

* `PuiseuxSeries.mem_subfield_iff`: membership in the Puiseux subfield is membership in the range
  of some `toHahn K n`.
* `PuiseuxSeries.mem_subfield_iff_support`: the classical bounded-denominator characterization —
  a Hahn series is a Puiseux series iff its support lies in `(1 / n) • ℤ` for a single `n`.
* `PuiseuxSeries.exists_common_index`: finitely many Puiseux series lie in the range of a single
  `toHahn K N`.

## Tags

puiseux series, laurent series, hahn series
-/


noncomputable section

open HahnSeries Polynomial

namespace HahnSeries

/-- `embDomain` composes: extending along `f` and then along `g` is extending along
`f.trans g`. -/
@[simp]
theorem embDomain_embDomain {Γ Γ' Γ'' R : Type*} [PartialOrder Γ] [PartialOrder Γ']
    [PartialOrder Γ''] [Zero R] (f : Γ ↪o Γ') (g : Γ' ↪o Γ'') (x : HahnSeries Γ R) :
    embDomain g (embDomain f x) = embDomain (f.trans g) x := by
  ext b
  by_cases hb : b ∈ Set.range (f.trans g)
  · obtain ⟨a, rfl⟩ := hb
    rw [embDomain_coeff, RelEmbedding.trans_apply, embDomain_coeff, embDomain_coeff]
  · rw [embDomain_of_notMem_range hb]
    by_cases hb' : b ∈ Set.range g
    · obtain ⟨c, rfl⟩ := hb'
      rw [embDomain_coeff, embDomain_of_notMem_range fun ⟨a, ha⟩ => hb ⟨a, by simp [ha]⟩]
    · exact embDomain_of_notMem_range hb'

end HahnSeries

namespace LaurentSeries

variable (K : Type*) [Field K]

/-- The expansion ring embedding `K((t)) →+* K((t))`, `t ↦ t ^ m`:
`embDomainRingHom` along the exponent map `k ↦ m * k` on `ℤ`. -/
def expand (m : ℕ+) : LaurentSeries K →+* LaurentSeries K :=
  HahnSeries.embDomainRingHom (AddMonoidHom.mk' ((m : ℤ) * ·) (mul_add _))
    (fun _ _ => mul_left_cancel₀ (by exact_mod_cast m.ne_zero))
    fun _ _ => mul_le_mul_iff_right₀ (by exact_mod_cast m.pos)

/-- The embedding `K((t)) →+* HahnSeries ℚ K`, "`t ↦ t ^ (1 / n)`":
`embDomainRingHom` along the exponent map `k ↦ k / n : ℤ → ℚ`. -/
def toHahn (n : ℕ+) : LaurentSeries K →+* HahnSeries ℚ K :=
  HahnSeries.embDomainRingHom
    (AddMonoidHom.mk' (fun k : ℤ => (k : ℚ) / (n : ℕ)) fun a b => by push_cast; ring)
    (fun _ _ h => Int.cast_injective ((div_left_inj' (Nat.cast_ne_zero.mpr n.ne_zero)).mp h))
    fun _ _ => (div_le_div_iff_of_pos_right (Nat.cast_pos.mpr n.pos)).trans Int.cast_le

@[simp]
theorem toHahn_single (n : ℕ+) (k : ℤ) (a : K) :
    toHahn K n (HahnSeries.single k a) = HahnSeries.single ((k : ℚ) / (n : ℕ)) a :=
  HahnSeries.embDomain_single ..

/-- Compatibility of the embeddings: `toHahn K n = toHahn K (n * m) ∘ expand K m` — expanding
by `m` and then mapping `t ↦ t ^ (1 / (n * m))` is mapping `t ↦ t ^ (1 / n)`. -/
theorem toHahn_comp_expand (n m : ℕ+) :
    (toHahn K (n * m)).comp (expand K m) = toHahn K n :=
  RingHom.ext fun f => by
    show HahnSeries.embDomain _ (HahnSeries.embDomain _ f) = HahnSeries.embDomain _ f
    rw [HahnSeries.embDomain_embDomain]
    congr 1
    ext k
    simp [mul_comm ((n : ℚ)), mul_div_mul_left]

/-- Range monotonicity: the range of `toHahn K n` is contained in the range of
`toHahn K (n * m)`, as subfields of `HahnSeries ℚ K`. -/
theorem fieldRange_toHahn_le (n m : ℕ+) :
    (toHahn K n).fieldRange ≤ (toHahn K (n * m)).fieldRange :=
  fun _ ⟨f, hf⟩ => ⟨expand K m f, (DFunLike.congr_fun (toHahn_comp_expand K n m) f).trans hf⟩

/-- The family `n ↦ (toHahn K n).fieldRange` is directed: the ranges of `toHahn K a` and
`toHahn K b` both sit inside the range of `toHahn K (a * b)`. -/
theorem directed_fieldRange_toHahn :
    Directed (· ≤ ·) fun n : ℕ+ => (toHahn K n).fieldRange := fun a b =>
  ⟨a * b, fieldRange_toHahn_le K a b, mul_comm b a ▸ fieldRange_toHahn_le K b a⟩

end LaurentSeries

namespace PuiseuxSeries

open LaurentSeries

variable (K : Type*) [Field K]

/-- The Puiseux subfield `⨆ n, (toHahn K n).fieldRange` of `HahnSeries ℚ K` — the directed union
of the images of the embeddings `toHahn K n`, i.e. `⋃ n, K((t ^ (1 / n)))`. -/
def subfield : Subfield (HahnSeries ℚ K) :=
  ⨆ n : ℕ+, (toHahn K n).fieldRange

/-- Membership in the Puiseux subfield: `x ∈ subfield K` iff `x` is in the range of some
`toHahn K n` (the supremum of the directed family of subfields is their union). -/
theorem mem_subfield_iff {x : HahnSeries ℚ K} :
    x ∈ subfield K ↔ ∃ n : ℕ+, x ∈ (toHahn K n).fieldRange :=
  Subfield.mem_iSup_of_directed (directed_fieldRange_toHahn K)

/-- **Bounded-denominator characterization**: membership in the Puiseux subfield
is exactly the classical support condition — the support lies in `(1 / n) • ℤ` for a
single `n`. This certifies the directed-union definition against the textbook
description of Puiseux series. -/
theorem mem_subfield_iff_support {x : HahnSeries ℚ K} :
    x ∈ subfield K ↔
      ∃ n : ℕ+, ∀ q ∈ x.support, ∃ k : ℤ, q = (k : ℚ) / (n : ℚ) := by
  -- the key coefficient fact about `toHahn K n`, which is an `embDomain` by definition
  have key₂ : ∀ (n : ℕ+) (f : LaurentSeries K) (q : ℚ),
      (¬ ∃ k : ℤ, q = (k : ℚ) / (n : ℚ)) → ((toHahn K n) f).coeff q = 0 := fun n f q hq =>
    HahnSeries.embDomain_of_notMem_range fun ⟨k, hk⟩ => hq ⟨k, hk.symm⟩
  rw [mem_subfield_iff]
  constructor
  · rintro ⟨n, f, rfl⟩
    exact ⟨n, fun q => Not.imp_symm (key₂ n f q)⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rcases Set.eq_empty_or_nonempty x.support with hs | hs
    · exact ⟨0, (map_zero _).trans (HahnSeries.support_eq_empty_iff.mp hs).symm⟩
    -- the minimum of the support gives an integer lower bound for the support of `f`
    refine ⟨⟨fun k => x.coeff ((k : ℚ) / (n : ℚ)), ?_⟩, ?_⟩
    · exact (BddBelow.isWF ⟨⌈(n : ℚ) * x.isWF_support.min hs⌉, fun k hk => Int.ceil_le.mpr
        ((le_div_iff₀' (by exact_mod_cast n.pos)).mp (x.isWF_support.min_le hs hk))⟩).isPWO
    · ext q
      by_cases hq : ∃ k : ℤ, q = (k : ℚ) / (n : ℚ)
      · obtain ⟨k, rfl⟩ := hq
        exact HahnSeries.embDomain_coeff
      · exact (key₂ n _ q hq).trans (of_not_not (mt (hn q) hq)).symm

/-- Common index: a finite set of elements of the Puiseux subfield lies in the
range of a single `toHahn K N`. -/
theorem exists_common_index (s : Finset (HahnSeries ℚ K))
    (hs : ∀ x ∈ s, x ∈ subfield K) :
    ∃ N : ℕ+, ∀ x ∈ s, x ∈ (toHahn K N).fieldRange := by
  choose! n hn using fun x (hx : x ∈ s) => (mem_subfield_iff K).mp (hs x hx)
  obtain ⟨N, hN⟩ := (directed_fieldRange_toHahn K).finset_le (s.image n)
  exact ⟨N, fun x hx => hN (n x) (Finset.mem_image_of_mem n hx) (hn x hx)⟩

end PuiseuxSeries

/-- The type of Puiseux series over `K`: the carrier of the Puiseux subfield of
`HahnSeries ℚ K`. A field, by the generic subfield instances. -/
def PuiseuxSeries (K : Type*) [Field K] : Type _ :=
  ↥(PuiseuxSeries.subfield K)

namespace PuiseuxSeries

variable (K : Type*) [Field K]

instance : Field (PuiseuxSeries K) :=
  inferInstanceAs (Field ↥(subfield K))

/-- The `K((t))`-algebra structure on Puiseux series: `toHahn K 1` corestricted to the
Puiseux subfield. This fixes the embedding of `K((t))` into the Puiseux series. -/
instance algebraLaurentSeries : Algebra (LaurentSeries K) (PuiseuxSeries K) :=
  RingHom.toAlgebra <|
    (LaurentSeries.toHahn K 1).codRestrict (subfield K) fun x =>
      (mem_subfield_iff K).mpr ⟨1, RingHom.mem_fieldRange_self _ x⟩

end PuiseuxSeries
end

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/


/-!

# Hensel splitting for polynomials over power series

In this file we derive from the Weierstrass preparation theorem
(`PowerSeries.exists_isWeierstrassFactorization`) a Hensel-style splitting for a monic
polynomial `p` over `K⟦X⟧`: a root of multiplicity `k` of the reduction of `p` modulo the
maximal ideal of `K⟦X⟧` (that is, of the coefficientwise application of
`PowerSeries.constantCoeff` to `p`) lifts to a monic factor of `p` of degree `k`.

## Main results

- `Polynomial.Monic.exists_factorization_rootMultiplicity_zero`: a monic `p` over `K⟦X⟧` of
  degree `m` whose reduction has `0` as a root of multiplicity `k` with `0 < k ≤ m` factors as
  `p = g * h` with `g`, `h` monic of degrees `k` and `m - k`, and the reduction of `g` is `X ^ k`.

- `Polynomial.Monic.exists_factorization_rootMultiplicity`: a monic `p` over `K⟦X⟧` of degree
  `m` whose reduction has a root `a : K` of multiplicity `k` with `0 < k < m` factors as
  `p = g * h` with `g`, `h` monic of degrees `k` and `m - k`.

-/


namespace Polynomial

variable {K : Type*} [Field K]

/-- **Hensel splitting at zero**: a monic `p` over `K⟦X⟧` of degree `m` whose reduction
(coefficientwise `PowerSeries.constantCoeff`) has `0` as a root of multiplicity `k` with
`0 < k ≤ m` factors as `p = g * h` with `g`, `h` monic of degrees `k` and `m - k`, and `g`
distinguished: its reduction is `X ^ k`. -/
theorem Monic.exists_factorization_rootMultiplicity_zero {p : (PowerSeries K)[X]} {m k : ℕ}
    (hp : p.Monic) (hm : p.natDegree = m)
    (hk : (p.map (PowerSeries.constantCoeff (R := K))).rootMultiplicity 0 = k)
    (_hk0 : 0 < k) (hkm : k ≤ m) :
    ∃ g h : (PowerSeries K)[X], g.Monic ∧ h.Monic ∧ p = g * h ∧
      g.natDegree = k ∧ h.natDegree = m - k ∧
      g.map (PowerSeries.constantCoeff (R := K)) = X ^ k := by
  have : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries K)) (PowerSeries K) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  set A := PowerSeries K
  set e := PowerSeries.residueFieldOfPowerSeries (k := K)
  set φ := (p : PowerSeries A).map (IsLocalRing.residue A) with hφ
  -- The residue field of `A` is `K`, so `φ` corresponds to the reduction of `p`.
  have key : φ.map e.toRingHom
      = ((p.map (PowerSeries.constantCoeff (R := K)) : K[X]) : PowerSeries K) := by
    ext n
    simp [hφ, Polynomial.coeff_coe]
    rfl
  -- The order of the coercion of a nonzero polynomial is its root multiplicity at `0`.
  have hordK : ((p.map (PowerSeries.constantCoeff (R := K)) : K[X]) : PowerSeries K).order
      = (k : ℕ∞) := by
    have hnz : (p.map (PowerSeries.constantCoeff (R := K))) ≠ 0 := (hp.map _).ne_zero
    rw [← hk, Polynomial.rootMultiplicity_eq_natTrailingDegree', PowerSeries.order_eq_nat]
    refine ⟨?_, fun i hi ↦ by simpa using Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi⟩
    simpa [Polynomial.trailingCoeff] using Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hnz
  have hmap : (φ.map e.toRingHom).order = φ.order := by
    have h : (φ.map e.toRingHom).map e.symm.toRingHom = φ := by ext n; simp
    refine le_antisymm ?_ (PowerSeries.le_order_map _)
    simpa only [h] using PowerSeries.le_order_map (φ := φ.map e.toRingHom) e.symm.toRingHom
  have horder : φ.order = (k : ℕ∞) := by rw [← hmap, key, hordK]
  have hφnz : φ ≠ 0 := fun h ↦ by simp [h] at horder
  -- Weierstrass preparation for `A⟦X⟧`.
  obtain ⟨f, u, H⟩ := PowerSeries.exists_isWeierstrassFactorization hφnz
  have hfmonic : f.Monic := H.isDistinguishedAt.monic
  have hfdeg : f.natDegree = k := by
    rw [H.natDegree_eq_toNat_order_map, ← hφ, horder, ENat.toNat_natCast]
  have hordf : ((f : PowerSeries A).map
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))).order = (k : ℕ∞) := by
    rw [← H.isDistinguishedAt.coe_natDegree_eq_order_map (f : PowerSeries A) 1 (by simp)
      (by simp), hfdeg]
  -- Divide `p` by the monic `f` in `A[X]`; uniqueness of Weierstrass division forces `u = p /ₘ f`.
  have hdivmod : p = f * (p /ₘ f) + p %ₘ f :=
    ((add_comm _ _).trans (p.modByMonic_add_div f)).symm
  have hrdeg : (p %ₘ f).degree < (k : ℕ) :=
    hfdeg ▸ Polynomial.degree_eq_natDegree hfmonic.ne_zero ▸ p.degree_modByMonic_lt hfmonic
  have huniq := H.isDistinguishedAt.isWeierstrassDivisorAt'.eq_of_mul_add_eq_mul_add (q := u)
    (q' := ↑(p /ₘ f)) (r := 0) (r' := p %ₘ f) (by simp [hordf]) (by rw [hordf]; simpa using hrdeg)
    (by rw [Polynomial.coe_zero, add_zero, ← H.eq_mul]
        exact_mod_cast hdivmod)
  rw [huniq.2.symm, add_zero] at hdivmod
  refine ⟨f, p /ₘ f, hfmonic, hfmonic.of_mul_monic_left (hdivmod ▸ hp), hdivmod, hfdeg, ?_, ?_⟩
  · have := p.natDegree_divByMonic hfmonic
    omega
  · -- `f` is distinguished of degree `k`, so its reduction is `X ^ k`.
    have h1 := congrArg (Polynomial.map e.toRingHom)
      (show f.map (IsLocalRing.residue A) = X ^ k from hfdeg ▸ H.isDistinguishedAt.map_eq_X_pow)
    rwa [Polynomial.map_map, Polynomial.map_pow, Polynomial.map_X] at h1

/-- **Hensel splitting at a root**: a monic `p` over `K⟦X⟧` of degree `m` whose reduction
(coefficientwise `PowerSeries.constantCoeff`) has a root `a : K` of multiplicity `k` with
`0 < k < m` factors as `p = g * h` with `g`, `h` monic of degrees `k` and `m - k`. -/
theorem Monic.exists_factorization_rootMultiplicity {p : (PowerSeries K)[X]} {m k : ℕ} {a : K}
    (hp : p.Monic) (hm : p.natDegree = m)
    (hk : (p.map (PowerSeries.constantCoeff (R := K))).rootMultiplicity a = k)
    (hk0 : 0 < k) (hkm : k < m) :
    ∃ g h : (PowerSeries K)[X], g.Monic ∧ h.Monic ∧ p = g * h ∧
      g.natDegree = k ∧ h.natDegree = m - k := by
  set c : PowerSeries K := PowerSeries.C a with hc
  -- Shift the root to `0`.
  have hPmonic : (p.comp (X + C c)).Monic := hp.comp_X_add_C c
  have hPdeg : (p.comp (X + C c)).natDegree = m := by simp [Polynomial.natDegree_comp, hm]
  have hred : (p.comp (X + C c)).map (PowerSeries.constantCoeff (R := K))
      = (p.map (PowerSeries.constantCoeff (R := K))).comp (X + C a) := by
    simp [Polynomial.map_comp, hc]
  have hkP : ((p.comp (X + C c)).map
      (PowerSeries.constantCoeff (R := K))).rootMultiplicity 0 = k := by
    rw [hred, ← Polynomial.rootMultiplicity_eq_rootMultiplicity, hk]
  obtain ⟨g₀, h₀, hg₀, hh₀, hpr, hg₀deg, hh₀deg, -⟩ :=
    hPmonic.exists_factorization_rootMultiplicity_zero hPdeg hkP hk0 hkm.le
  -- Shift back.
  have hdegsub : ∀ q : (PowerSeries K)[X], (q.comp (X - C c)).natDegree = q.natDegree := by
    simp [Polynomial.natDegree_comp]
  refine ⟨g₀.comp (X - C c), h₀.comp (X - C c), hg₀.comp_X_sub_C c, hh₀.comp_X_sub_C c, ?_,
    by rw [hdegsub, hg₀deg], by rw [hdegsub, hh₀deg]⟩
  simp [← Polynomial.mul_comp, ← hpr, Polynomial.comp_assoc]

end Polynomial

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/


/-!
# Puiseux series are algebraic over Laurent series

This file proves that the field of Puiseux series over a field `K` is algebraic over the field of
Laurent series: the monomial `t ^ (1 / n)` is integral over the image of `K((t))` (it is a root of
the monic polynomial `Y ^ n - t`), and the image of `toHahn K n` lies in the subalgebra generated
by this monomial (sorting a series in `t ^ (1 / n)` by exponent residues mod `n`).

## Main results

* `PuiseuxSeries.isIntegral_single_one_div`: the monomial `t ^ (1 / n)` of `HahnSeries ℚ K` is
  integral over the range of `LaurentSeries.toHahn K 1`.
* `PuiseuxSeries.mem_adjoin_single_of_mem_fieldRange`: every element of the range of
  `LaurentSeries.toHahn K n` lies in the subalgebra generated by `t ^ (1 / n)` over the range of
  `LaurentSeries.toHahn K 1`.
* `PuiseuxSeries.isAlgebraic`: `PuiseuxSeries K` is algebraic over `LaurentSeries K`.

## Tags

puiseux series, laurent series, algebraic
-/


noncomputable section

namespace PuiseuxSeries

open LaurentSeries Polynomial

variable (K : Type*) [Field K]

/-- The monomial `t ^ (1 / n)` of `HahnSeries ℚ K` is integral over the range of
`LaurentSeries.toHahn K 1`: it is a root of the monic polynomial `Y ^ n - t`. -/
theorem isIntegral_single_one_div (n : ℕ+) :
    IsIntegral (LaurentSeries.toHahn K 1).fieldRange
      (HahnSeries.single ((1 : ℚ) / (n : ℕ)) (1 : K)) := by
  have hpow : (HahnSeries.single ((1 : ℚ) / (n : ℕ)) (1 : K)) ^ (n : ℕ)
      = HahnSeries.single (1 : ℚ) (1 : K) := by
    simp [HahnSeries.single_pow, one_div, nsmul_eq_mul, n.ne_zero]
  refine ⟨X ^ (n : ℕ) - C ⟨HahnSeries.single (1 : ℚ) (1 : K),
      ⟨HahnSeries.single (1 : ℤ) (1 : K), by simp [toHahn_single]⟩⟩,
    monic_X_pow_sub_C _ n.ne_zero, ?_⟩
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C, hpow]
  exact sub_eq_zero.mpr rfl

/-- Every element of the range of `LaurentSeries.toHahn K n` lies in the subalgebra of
`HahnSeries ℚ K` generated by the monomial `t ^ (1 / n)` over the range of
`LaurentSeries.toHahn K 1` — sort a series in `t ^ (1 / n)` by exponent residues mod `n`. -/
theorem mem_adjoin_single_of_mem_fieldRange (n : ℕ+) {x : HahnSeries ℚ K}
    (hx : x ∈ (LaurentSeries.toHahn K n).fieldRange) :
    x ∈ Algebra.adjoin (LaurentSeries.toHahn K 1).fieldRange
      {HahnSeries.single ((1 : ℚ) / (n : ℕ)) (1 : K)} := by
  classical
  obtain ⟨f, rfl⟩ := hx
  obtain ⟨b, hb⟩ : BddBelow f.support :=
    f.support.eq_empty_or_nonempty.elim (· ▸ bddBelow_empty)
      fun h => ⟨_, fun _ hy => f.isWF_support.min_le h hy⟩
  have hg : ∀ r : ℤ, ∃ y : LaurentSeries K, ∀ k : ℤ, y.coeff k = f.coeff ((n : ℤ) * k + r) := by
    intro r
    refine ⟨⟨fun k => f.coeff ((n : ℤ) * k + r),
        (BddBelow.isWF ⟨min 0 (b - r), fun k hk => ?_⟩).isPWO⟩, fun _ => rfl⟩
    exact min_le_iff.mpr <| (le_or_gt 0 k).imp id fun h0 => by nlinarith [hb hk, n.pos]
  choose g hgc using hg
  have hexp1 (y : LaurentSeries K) (k : ℤ) : (expand K n y).coeff ((n : ℤ) * k) = y.coeff k :=
    HahnSeries.embDomain_coeff
  have hexp0 (y : LaurentSeries K) {j : ℤ} (hj : ¬∃ k : ℤ, (n : ℤ) * k = j) :
      (expand K n y).coeff j = 0 := HahnSeries.embDomain_of_notMem_range hj
  have hf : f = ∑ r ∈ Finset.range (n : ℕ),
      HahnSeries.single (r : ℤ) (1 : K) * expand K n (g r) := by
    ext j
    rw [HahnSeries.coeff_sum]
    have hn0 : (0 : ℤ) < (n : ℤ) := by exact_mod_cast n.pos
    set r₀ : ℕ := (j % (n : ℤ)).toNat
    have hnonneg := Int.emod_nonneg j (ne_of_gt hn0)
    have hr₀lt : r₀ < (n : ℕ) := (Int.toNat_lt hnonneg).mpr (Int.emod_lt_of_pos j hn0)
    have hr₀cast : (r₀ : ℤ) = j % (n : ℤ) := Int.toNat_of_nonneg hnonneg
    rw [Finset.sum_eq_single_of_mem r₀ (Finset.mem_range.mpr hr₀lt) ?_]
    · have hdiv : j - j % (n : ℤ) = (n : ℤ) * (j / (n : ℤ)) := by
        linarith [Int.mul_ediv_add_emod j (n : ℤ)]
      rw [HahnSeries.coeff_single_mul, one_mul, hr₀cast, hdiv, hexp1, hgc]
      exact congrArg _ (by omega)
    · intro r hr hne
      have hnd : ¬∃ k : ℤ, (n : ℤ) * k = j - (r : ℤ) := by
        rintro ⟨k, hk⟩
        have hrlt : (r : ℤ) < (n : ℤ) := by exact_mod_cast Finset.mem_range.mp hr
        refine hne (Nat.cast_injective (R := ℤ) ?_)
        rw [hr₀cast, show j = (n : ℤ) * k + r by omega, Int.mul_add_emod_self_left,
          Int.emod_eq_of_lt (Nat.cast_nonneg _) hrlt]
      rw [HahnSeries.coeff_single_mul, hexp0 _ hnd, mul_zero]
  rw [hf, map_sum]
  refine Subalgebra.sum_mem _ fun r _ => ?_
  have h1 : toHahn K n (HahnSeries.single (r : ℤ) (1 : K))
      = HahnSeries.single ((1 : ℚ) / (n : ℕ)) (1 : K) ^ r := by
    rw [HahnSeries.single_pow, one_pow, toHahn_single, nsmul_eq_mul, mul_one_div,
      Int.cast_natCast]
  have h2 : toHahn K n (expand K n (g r)) ∈ (toHahn K 1).fieldRange :=
    ⟨g r, by simpa [one_mul] using (DFunLike.congr_fun (toHahn_comp_expand K 1 n) (g r)).symm⟩
  rw [map_mul, h1]
  exact mul_mem (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton _ _) _)
    (Subalgebra.algebraMap_mem _ (⟨_, h2⟩ : (toHahn K 1).fieldRange))

/-- **Puiseux series are algebraic over Laurent series**, for any field `K`. -/
instance isAlgebraic : Algebra.IsAlgebraic (LaurentSeries K) (PuiseuxSeries K) where
  isAlgebraic x := by
    let v : PuiseuxSeries K →+* HahnSeries ℚ K := (subfield K).subtype
    obtain ⟨n, hn⟩ := (mem_subfield_iff K).mp x.property
    exact (IsIntegral.isAlgebraic <|
        .of_mem_of_fg _ (isIntegral_single_one_div K n).fg_adjoin_singleton _
          (mem_adjoin_single_of_mem_fieldRange K n hn)).of_ringHom_of_comp_eq
      (toHahn K 1).rangeRestrictFieldEquiv v (EquivLike.surjective _) Subtype.val_injective
      (by ext; rfl)

end PuiseuxSeries
end

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/


/-!
# Puiseux's theorem

This file proves **Puiseux's theorem**: over an algebraically closed field `K` of characteristic
zero, the field `PuiseuxSeries K = ⋃ n, K((t ^ (1 / n)))` of Puiseux series is algebraically
closed, and is an algebraic closure of the Laurent series field `K((t))`.

The proof is the classical Newton–Puiseux algorithm, organized as a strong induction on the
degree. Given a monic polynomial `p` of degree `m` over `K((t))`:

* a Tschirnhausen substitution `X ↦ X + c` kills the coefficient of degree `m - 1`
  (this is where characteristic zero enters);
* if all lower coefficients vanish the polynomial is `X ^ m`, with root `0`;
* otherwise, rescaling the variable by a monomial `t ^ (a / (nq))` chosen by the minimal Newton
  slope produces a monic polynomial `P` over `K⟦t⟧` whose reduction mod `t` is not a pure power
  (`LaurentSeries.newton_slope_scaling`);
* the reduction of `P` has a root of multiplicity strictly between `0` and `m`, so the Hensel
  splitting `Polynomial.Monic.exists_factorization_rootMultiplicity` produces a proper monic
  factor, and the induction hypothesis applies to it at a finer index
  (`LaurentSeries.newton_puiseux_descent`).

## Main results

* `PuiseuxSeries.exists_root_mem_subfield`: every monic polynomial of positive degree over
  `K((t))`, mapped along any embedding `LaurentSeries.toHahn K n`, has a root in the Puiseux
  subfield of `HahnSeries ℚ K`.
* `PuiseuxSeries.isAlgClosed`: `PuiseuxSeries K` is algebraically closed for `K` algebraically
  closed of characteristic zero.
* `PuiseuxSeries.isAlgClosure`: **Puiseux's theorem** — `PuiseuxSeries K` is an algebraic closure
  of `LaurentSeries K`.

## References

* [D. Eisenbud, *Commutative Algebra with a view toward Algebraic Geometry*][Eisenbud1995],
  Corollary 13.15

## Tags

puiseux series, newton polygon, algebraically closed, algebraic closure
-/


noncomputable section

open Polynomial

/-! ## Auxiliary polynomial lemmas

Two generic lemmas over a field: the Tschirnhausen substitution killing the subleading
coefficient, and the existence of a root of intermediate multiplicity for a monic polynomial
with vanishing subleading coefficient which is not a pure power of `X`.
-/

namespace Polynomial

/-- **Tschirnhausen substitution**: for `p` monic of degree `m` over a field `F` with
`(m : F) ≠ 0`, substituting `X + C (-p.coeff (m - 1) / m)` for the variable preserves monicity
and degree and kills the coefficient of degree `m - 1`. -/
theorem Monic.tschirnhausen {F : Type*} [Field F] {p : F[X]} {m : ℕ} (hp : p.Monic)
    (hm : p.natDegree = m) (hmF : (m : F) ≠ 0) :
    (p.comp (X + C (-p.coeff (m - 1) / (m : F)))).Monic ∧
      (p.comp (X + C (-p.coeff (m - 1) / (m : F)))).natDegree = m ∧
      (p.comp (X + C (-p.coeff (m - 1) / (m : F)))).coeff (m - 1) = 0 := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hmF
  set b : F := -p.coeff (m - 1) / (m : F)
  refine ⟨hp.comp_X_add_C b, by rw [← taylor_apply, natDegree_taylor, hm], ?_⟩
  rw [← taylor_apply, taylor_coeff]
  have hdeg : ((hasseDeriv (m - 1)) p).natDegree < 2 :=
    lt_of_le_of_lt (natDegree_hasseDeriv_le p (m - 1)) (by rw [hm]; omega)
  rw [eval_eq_sum_range' hdeg, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, hasseDeriv_coeff, hasseDeriv_coeff,
    show 1 + (m - 1) = m by omega]
  simp only [Nat.choose_symm (Nat.one_le_iff_ne_zero.mpr hm0), Nat.choose_one_right,
    show p.coeff m = 1 from hm ▸ hp.coeff_natDegree, zero_add, Nat.choose_self,
    Nat.cast_one, one_mul, mul_one, pow_zero, pow_one, b]
  field_simp
  ring

/-- **A monic non-power has a mixed root**: over an algebraically closed field, a monic `r` of
degree `m` with `(m : K) ≠ 0`, vanishing coefficient of degree `m - 1`, and `r ≠ X ^ m` has a
root of multiplicity strictly between `0` and `m`. -/
theorem Monic.exists_rootMultiplicity_pos_lt {K : Type*} [Field K] [IsAlgClosed K]
    {r : K[X]} {m : ℕ} (hr : r.Monic) (hm : r.natDegree = m) (hmK : (m : K) ≠ 0)
    (hsub : r.coeff (m - 1) = 0) (hne : r ≠ X ^ m) :
    ∃ a : K, 0 < r.rootMultiplicity a ∧ r.rootMultiplicity a < m := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hmK
  have hr0 : r ≠ 0 := hr.ne_zero
  obtain ⟨a, ha⟩ :=
    IsAlgClosed.exists_root r (by rw [degree_eq_natDegree hr0, hm]; exact Nat.cast_ne_zero.mpr hm0)
  refine ⟨a, (rootMultiplicity_pos hr0).2 ha, ?_⟩
  by_contra hlt
  have heq : r = (X - C a) ^ m :=
    eq_of_monic_of_dvd_of_natDegree_le ((monic_X_sub_C a).pow m) hr
      (dvd_trans (pow_dvd_pow _ (Nat.le_of_not_lt hlt)) (pow_rootMultiplicity_dvd r a))
      (by simp [hm])
  have hcoef : ((X - C a) ^ m).coeff (m - 1) = -(m : K) * a := by
    rw [show m - 1 = ((X - C a) ^ m).natDegree - 1 by simp,
      ← nextCoeff_of_natDegree_pos (by simp [Nat.pos_of_ne_zero hm0]),
      (monic_X_sub_C a).nextCoeff_pow, nextCoeff_X_sub_C, nsmul_eq_mul, mul_neg,
      neg_mul]
  rw [heq, hcoef, mul_eq_zero, neg_eq_zero] at hsub
  exact hne (by simpa [hsub.resolve_left hmK] using heq)

end Polynomial

/-! ## The Newton slope rescaling

A Laurent series of nonnegative order is a power series; the per-summand monomial scaling
identity for the embeddings `toHahn`; and the main rescaling lemma producing an integral
polynomial with the right reduction and the root-transfer eval identity.
-/

namespace LaurentSeries

variable {K : Type*} [Field K]

/-- A Laurent series that is zero or has nonnegative order lies in the range of the coercion
from power series. -/
theorem exists_ofPowerSeries_eq_of_order_nonneg {f : LaurentSeries K}
    (hf : f = 0 ∨ 0 ≤ f.order) :
    ∃ F : PowerSeries K, HahnSeries.ofPowerSeries ℤ K F = f := by
  rcases hf with rfl | hf
  · exact ⟨0, PowerSeries.coe_zero⟩
  · exact ⟨PowerSeries.X ^ f.order.toNat * f.powerSeriesPart,
      LaurentSeries.X_order_mul_powerSeriesPart (Int.toNat_of_nonneg hf)⟩

/-- The expansion `expand K q` multiplies `orderTop` by `q`. -/
theorem orderTop_expand (q : ℕ+) (c : LaurentSeries K) :
    (expand K q c).orderTop = c.orderTop.map (fun k => (q : ℤ) * k) := by
  change (HahnSeries.embDomain
      ⟨⟨fun k => (q : ℤ) * k, fun _ _ h => mul_left_cancel₀ (by exact_mod_cast q.ne_zero) h⟩,
        mul_le_mul_iff_right₀ (by exact_mod_cast q.pos)⟩ c).orderTop = _
  rw [HahnSeries.orderTop_embDomain]
  rfl

/-- **Monomial scaling identity** (per-summand computation of the Newton rescaling): for
`τ = single (a / (nq)) 1`,
`τ ^ m * toHahn K (n * q) (expand K q c * single (a * (i - m)) 1) = toHahn K n c * τ ^ i`. -/
theorem toHahn_expand_single_scaling (n q : ℕ+) (a : ℤ) (c : LaurentSeries K) (i m : ℕ) :
    HahnSeries.single ((a : ℚ) / ((n * q : ℕ+) : ℕ)) (1 : K) ^ m *
        toHahn K (n * q) (expand K q c * HahnSeries.single (a * ((i : ℤ) - (m : ℤ))) 1)
      = toHahn K n c * HahnSeries.single ((a : ℚ) / ((n * q : ℕ+) : ℕ)) (1 : K) ^ i := by
  rw [map_mul, ← RingHom.comp_apply (toHahn K (n * q)) (expand K q),
    toHahn_comp_expand, toHahn_single, HahnSeries.single_pow, HahnSeries.single_pow,
    mul_left_comm, HahnSeries.single_mul_single]
  simp only [one_pow, mul_one, nsmul_eq_mul]
  congr 1
  push_cast
  ring_nf

/-- **Newton slope scaling**: given `p` monic of degree `m` over `K((t))` with vanishing
subleading coefficient and some nonzero lower coefficient, there are `q ≥ 1`, `a : ℤ`, and a
monic `P` of degree `m` over `K⟦X⟧` whose reduction has vanishing subleading coefficient but
some nonzero coefficient below the top, such that roots transfer: evaluating
`p.map (toHahn K n)` at `τ * y` (with `τ = single (a / (nq)) 1`) equals `τ ^ m` times the
evaluation at `y` of the image of `P` under `toHahn K (n * q)` composed with the Laurent
coercion. -/
theorem newton_slope_scaling (n : ℕ+) {p : Polynomial (LaurentSeries K)} {m : ℕ}
    (hp : p.Monic) (hm : p.natDegree = m) (hsub : p.coeff (m - 1) = 0)
    (hex : ∃ i < m, p.coeff i ≠ 0) :
    ∃ (q : ℕ+) (a : ℤ) (P : Polynomial (PowerSeries K)),
      P.Monic ∧ P.natDegree = m ∧
      (P.map (PowerSeries.constantCoeff (R := K))).coeff (m - 1) = 0 ∧
      (∃ i₀ < m, (P.map (PowerSeries.constantCoeff (R := K))).coeff i₀ ≠ 0) ∧
      ∀ y : HahnSeries ℚ K,
        (p.map (toHahn K n)).eval
            (HahnSeries.single ((a : ℚ) / ((n * q : ℕ+) : ℕ)) 1 * y)
          = HahnSeries.single ((a : ℚ) / ((n * q : ℕ+) : ℕ)) 1 ^ m *
              (P.map ((toHahn K (n * q)).comp (HahnSeries.ofPowerSeries ℤ K))).eval y := by
  classical
  obtain ⟨i₁, hi₁m, hi₁⟩ := hex
  obtain ⟨i₀, hi₀S, hi₀min⟩ :=
    ((Finset.range m).filter (fun i => p.coeff i ≠ 0)).exists_min_image
      (fun i => ((p.coeff i).order : ℚ) / ((m - i : ℕ) : ℚ))
      ⟨i₁, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi₁m, hi₁⟩⟩
  obtain ⟨hi₀m, hc₀⟩ : i₀ < m ∧ p.coeff i₀ ≠ 0 := by
    simpa [Finset.mem_filter, Finset.mem_range] using hi₀S
  obtain ⟨q, hq⟩ : ∃ q : ℕ+, (q : ℕ) = m - i₀ :=
    ⟨⟨m - i₀, Nat.zero_lt_sub_of_lt hi₀m⟩, rfl⟩
  set a : ℤ := (p.coeff i₀).order
  have hqZ : ((q : ℕ) : ℤ) = (m : ℤ) - (i₀ : ℤ) := by rw [hq]; omega
  have key : ∀ i, i < m → p.coeff i ≠ 0 →
      0 ≤ ((q : ℕ) : ℤ) * (p.coeff i).order + a * ((i : ℤ) - (m : ℤ)) := by
    intro i him hci
    have h := hi₀min i (Finset.mem_filter.2 ⟨Finset.mem_range.2 him, hci⟩)
    rw [div_le_div_iff₀ (mod_cast Nat.zero_lt_sub_of_lt hi₀m : (0 : ℚ) < _)
      (mod_cast Nat.zero_lt_sub_of_lt him : (0 : ℚ) < _)] at h
    push_cast [Nat.cast_sub him.le, Nat.cast_sub hi₀m.le] at h
    rw [hqZ]; nlinarith [show a * ((m : ℤ) - i) ≤ (p.coeff i).order * ((m : ℤ) - i₀) by
      exact_mod_cast h]
  let d : ℕ → LaurentSeries K := fun i =>
    expand K q (p.coeff i) * HahnSeries.single (a * ((i : ℤ) - (m : ℤ))) 1
  have hdm : d m = 1 := by simp [d, show p.coeff m = 1 from hm ▸ hp.coeff_natDegree]
  have hdz {i} (hi : p.coeff i = 0) : d i = 0 := by simp [d, hi]
  have horder {i} (him : i < m) (hci : p.coeff i ≠ 0) :
      (d i).orderTop = ((((q : ℕ) : ℤ) * (p.coeff i).order + a * ((i : ℤ) - (m : ℤ)) : ℤ) :
        WithTop ℤ) := by
    simp [d, HahnSeries.orderTop_mul, orderTop_expand, HahnSeries.orderTop_single one_ne_zero,
      ← HahnSeries.order_eq_orderTop_of_ne_zero hci]
  have hdnn (i : ℕ) :
      (0 : WithTop ℤ) ≤ (if i ≤ m then d i else 0 : LaurentSeries K).orderTop := by
    split_ifs with him
    · rcases eq_or_lt_of_le him with heq | hlt
      · simp [heq, hdm]
      · by_cases hci : p.coeff i = 0
        · simp [hdz hci]
        · rw [horder hlt hci]; exact_mod_cast key i hlt hci
    · simp
  choose D hD using fun i => exists_ofPowerSeries_eq_of_order_nonneg
    (Or.inr (HahnSeries.zero_le_orderTop_iff.mp (hdnn i)))
  have hDi {i} (hi : i ≤ m) : HahnSeries.ofPowerSeries ℤ K (D i) = d i :=
    (hD i).trans (if_pos hi)
  have hDm : D m = 1 :=
    HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by simpa [hdm] using hDi le_rfl)
  have hDm1 : D (m - 1) = 0 :=
    HahnSeries.ofPowerSeries_injective (Γ := ℤ)
      (by simpa [hdz hsub] using hDi (Nat.sub_le m 1))
  have hPcoeff (j) :
      (∑ i ∈ Finset.range (m + 1), Polynomial.monomial i (D i)).coeff j =
        if j ≤ m then D j else 0 := by
    simp [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq']
  set P : Polynomial (PowerSeries K) := ∑ i ∈ Finset.range (m + 1), Polynomial.monomial i (D i)
  have hnd : P.natDegree = m :=
    le_antisymm (Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun N hN => by
        rw [hPcoeff, if_neg (Nat.not_le_of_lt hN)])
      (Polynomial.le_natDegree_of_ne_zero (by rw [hPcoeff, if_pos le_rfl, hDm]; exact one_ne_zero))
  have hmon : P.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hnd, hPcoeff, if_pos le_rfl, hDm]
  refine ⟨q, a, P, hmon, hnd, ?_, ?_, ?_⟩
  · rw [Polynomial.coeff_map, hPcoeff, if_pos (Nat.sub_le _ _), hDm1, map_zero]
  · refine ⟨i₀, hi₀m, ?_⟩
    rw [Polynomial.coeff_map, hPcoeff, if_pos hi₀m.le]
    have hz : ((q : ℕ) : ℤ) * (p.coeff i₀).order + a * ((i₀ : ℤ) - (m : ℤ)) = 0 := by
      rw [hqZ]; simp [a]; ring
    have := HahnSeries.coeff_orderTop_ne (by rw [horder hi₀m hc₀, hz])
    rw [← hDi hi₀m.le] at this
    convert this
    simpa using (LaurentSeries.coeff_coe_powerSeries (D i₀) 0).symm
  · intro y
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hm ▸ Polynomial.natDegree_map_le)),
      Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hnd ▸ Polynomial.natDegree_map_le)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [Polynomial.coeff_map, Polynomial.coeff_map, hPcoeff, if_pos him, RingHom.comp_apply,
      hDi him]
    simp only [d]
    rw [mul_pow, ← mul_assoc, ← mul_assoc, toHahn_expand_single_scaling n q a (p.coeff i) i m]

/-! ## The descent step and the main induction -/

/-- **Newton–Puiseux descent**: for `p'` monic of degree `m` over `K((t))` with vanishing
subleading coefficient and some nonzero lower coefficient (`K` algebraically closed,
characteristic zero), there are `q ≥ 1`, an element `τ` in the range of `toHahn K (n * q)`,
and a monic `g` with `1 ≤ deg g < m` such that every root `y` of `g.map (toHahn K (n * q))`
gives the root `τ * y` of `p'.map (toHahn K n)`. -/
theorem newton_puiseux_descent [IsAlgClosed K] [CharZero K] (n : ℕ+)
    {p' : Polynomial (LaurentSeries K)} {m : ℕ}
    (hp : p'.Monic) (hm : p'.natDegree = m) (hsub : p'.coeff (m - 1) = 0)
    (hex : ∃ i < m, p'.coeff i ≠ 0) :
    ∃ (q : ℕ+) (τ : HahnSeries ℚ K) (g : Polynomial (LaurentSeries K)),
      τ ∈ (toHahn K (n * q)).fieldRange ∧ g.Monic ∧
      1 ≤ g.natDegree ∧ g.natDegree < m ∧
      ∀ y : HahnSeries ℚ K,
        (g.map (toHahn K (n * q))).eval y = 0 →
        (p'.map (toHahn K n)).eval (τ * y) = 0 := by
  obtain ⟨q, a, P, hPm, hPdeg, hRsub, hRex, hev⟩ := newton_slope_scaling n hp hm hsub hex
  set R := P.map (PowerSeries.constantCoeff (R := K))
  have hRmonic : R.Monic := hPm.map _
  have hRdeg : R.natDegree = m := by rw [hPm.natDegree_map, hPdeg]
  have hRne : R ≠ X ^ m :=
    hRex.elim fun i₀ ⟨hi₀, hne⟩ h => by simp [h, Polynomial.coeff_X_pow, hi₀.ne] at hne
  obtain ⟨a₀, hk0, hkm⟩ := hRmonic.exists_rootMultiplicity_pos_lt hRdeg
    (Nat.cast_ne_zero.mpr (hex.elim fun _ ⟨hi, _⟩ => (Nat.zero_lt_of_lt hi).ne')) hRsub hRne
  obtain ⟨G, h, hG, hh, hPeq, hGdeg, -⟩ :=
    hPm.exists_factorization_rootMultiplicity (a := a₀) hPdeg rfl hk0 hkm
  refine ⟨q, HahnSeries.single ((a : ℚ) / ((n * q : ℕ+) : ℕ)) 1,
    G.map (HahnSeries.ofPowerSeries ℤ K), ⟨HahnSeries.single a 1, by rw [toHahn_single]⟩,
    hG.map _, ?_, ?_, ?_⟩
  · rw [hG.natDegree_map, hGdeg]; exact hk0
  · rw [hG.natDegree_map, hGdeg]; exact hkm
  · intro y hy
    rw [hev y, ← Polynomial.map_map, hPeq, Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.eval_mul, hy, zero_mul, mul_zero]

end LaurentSeries

namespace PuiseuxSeries

open LaurentSeries

variable {K : Type*} [Field K]

/-- The Newton–Puiseux induction, in the form suitable for strong induction on the degree:
the statement is quantified over all indices `n`, since the descent step re-enters at a finer
index. -/
private theorem exists_root_mem_subfield_aux [IsAlgClosed K] [CharZero K] :
    ∀ m : ℕ, ∀ (n : ℕ+) (p : Polynomial (LaurentSeries K)), p.Monic → p.natDegree = m →
      1 ≤ m → ∃ x ∈ PuiseuxSeries.subfield K, (p.map (toHahn K n)).eval x = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro n p hp hm hm1
  have hmF : (m : LaurentSeries K) ≠ 0 :=
    mt (fun h => HahnSeries.single_eq_zero_iff.mp
        ((map_natCast (HahnSeries.C : K →+* LaurentSeries K) m).symm.trans h))
      (Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hm1) : (m : K) ≠ 0)
  obtain ⟨hp'm, hp'deg, hp'sub⟩ := hp.tschirnhausen hm hmF
  set b : LaurentSeries K := -p.coeff (m - 1) / (m : LaurentSeries K)
  set p' : Polynomial (LaurentSeries K) := p.comp (X + C b) with hp'def
  have key : ∃ y ∈ PuiseuxSeries.subfield K, (p'.map (toHahn K n)).eval y = 0 := by
    by_cases hex : ∃ i < m, p'.coeff i ≠ 0
    · obtain ⟨q, τ, g, hτ, hg, hg1, hgm, htrans⟩ :=
        newton_puiseux_descent n hp'm hp'deg hp'sub hex
      obtain ⟨y, hy, hy0⟩ := ih g.natDegree hgm (n * q) g hg rfl hg1
      exact ⟨τ * y, mul_mem ((PuiseuxSeries.mem_subfield_iff K).mpr ⟨n * q, hτ⟩) hy,
        htrans y hy0⟩
    · have hall : ∀ i < m, p'.coeff i = 0 := fun i hi => by_contra fun hne => hex ⟨i, hi, hne⟩
      have hXm : p' = X ^ m := Polynomial.ext fun i => by
        rcases lt_trichotomy i m with hi | rfl | hi
        · simp [hall i hi, Polynomial.coeff_X_pow, hi.ne]
        · simpa [Polynomial.leadingCoeff, hp'deg] using hp'm.leadingCoeff
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Polynomial.coeff_X_pow,
            if_neg hi.ne']
      exact ⟨0, zero_mem _, by simp [hXm, Polynomial.map_pow, zero_pow (Nat.ne_zero_of_lt hm1)]⟩
  obtain ⟨y, hy, hy0⟩ := key
  refine ⟨y + toHahn K n b, add_mem hy ((PuiseuxSeries.mem_subfield_iff K).mpr ⟨n, b, rfl⟩), ?_⟩
  simpa [hp'def, Polynomial.map_comp, Polynomial.eval_comp] using hy0

/-- **Puiseux root of a monic polynomial** (the Newton–Puiseux induction): for `K` algebraically
closed of characteristic zero, every monic `p` over `K((t))` of positive degree, mapped along
any embedding `toHahn K n`, has a root in the Puiseux subfield. -/
theorem exists_root_mem_subfield [IsAlgClosed K] [CharZero K] (n : ℕ+)
    {p : Polynomial (LaurentSeries K)} (hp : p.Monic) (hdeg : 1 ≤ p.natDegree) :
    ∃ x ∈ PuiseuxSeries.subfield K, (p.map (toHahn K n)).eval x = 0 :=
  exists_root_mem_subfield_aux p.natDegree n p hp rfl hdeg

/-! ## Main results -/

/-- **Puiseux series are algebraically closed**: for `K` an algebraically closed field of
characteristic zero, the field of Puiseux series over `K` is algebraically closed. This is the
analytic half of **Puiseux's theorem**, proved by the Newton–Puiseux algorithm. -/
instance isAlgClosed (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] :
    IsAlgClosed (PuiseuxSeries K) := by
  apply IsAlgClosed.of_exists_root
  intro r hr hirr
  classical
  set ι : PuiseuxSeries K →+* HahnSeries ℚ K := (PuiseuxSeries.subfield K).subtype
  have hιinj : Function.Injective ι := Subtype.val_injective
  obtain ⟨N, hN⟩ :=
    PuiseuxSeries.exists_common_index K
      ((Finset.range (r.natDegree + 1)).image fun i => (r.map ι).coeff i)
      (fun x hx => by
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
        rw [Polynomial.coeff_map]
        exact (r.coeff i).2)
  have hrange : ∀ i, (r.map ι).coeff i ∈ Set.range (LaurentSeries.toHahn K N) := by
    intro i
    by_cases hi : i ≤ r.natDegree
    · exact Set.mem_range.mpr
        (hN _ (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hi), rfl⟩))
    · refine ⟨0, ?_⟩
      rw [map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt
        (by rw [hr.natDegree_map]; exact Nat.lt_of_not_le hi)]
  obtain ⟨p, hpmap, hpdeg, hpm⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic ((Polynomial.lifts_iff_coeff_lifts _).mpr hrange) (hr.map ι)
  have hdeg : 1 ≤ p.natDegree := by
    rw [natDegree_eq_of_degree_eq hpdeg, hr.natDegree_map]; exact hirr.natDegree_pos
  obtain ⟨x, hx, hx0⟩ := exists_root_mem_subfield N hpm hdeg
  refine ⟨⟨x, hx⟩, hιinj (by
    rw [map_zero, ← hx0, hpmap]
    exact (Polynomial.eval₂_hom ι (⟨x, hx⟩ : PuiseuxSeries K)).symm.trans
      (Polynomial.eval_map ι x).symm)⟩

/-- **Puiseux's theorem**: for `K` an algebraically closed field of characteristic zero, the
Puiseux series field `⋃ n, K((t ^ (1 / n)))` is an algebraic closure of the Laurent series
field `K((t))`. Algebraicity holds over any field (`PuiseuxSeries.isAlgebraic`); algebraic
closedness is the Newton–Puiseux algorithm (`PuiseuxSeries.isAlgClosed`). -/
instance isAlgClosure (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] :
    IsAlgClosure (LaurentSeries K) (PuiseuxSeries K) :=
  ⟨inferInstance, inferInstance⟩

end PuiseuxSeries
end


/-! Algebraically independent one-parameter formal arcs with prescribed residues. -/
namespace BorderDet.Curve
open PowerSeries MvPolynomial

private noncomputable def expAt (a : ℂ) : PowerSeries ℂ := PowerSeries.rescale a (PowerSeries.exp ℂ)

private theorem expAt_coeff_zero (a : ℂ) : PowerSeries.constantCoeff (expAt a) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [expAt]

private theorem expAt_nonzero (a : ℂ) : expAt a ≠ 0 := by
  intro h
  simpa [h] using (expAt_coeff_zero a)

private theorem expAt_derivative (a : ℂ) :
    PowerSeries.derivative ℂ (expAt a) = a • expAt a := by
  ext n
  have h := congrArg (PowerSeries.coeff n) (PowerSeries.derivative_exp ℂ)
  rw [PowerSeries.coeff_derivative] at h
  rw [PowerSeries.coeff_derivative,map_smul,expAt,PowerSeries.coeff_rescale,PowerSeries.coeff_rescale]
  rw [smul_eq_mul,pow_succ]
  linear_combination a ^ n * a * h

private theorem expAt_independent : LinearIndependent ℂ expAt := by
  apply Module.End.eigenvectors_linearIndependent' (PowerSeries.derivative ℂ).toLinearMap id Function.injective_id
  intro a
  exact ⟨Module.End.mem_eigenspace_iff.mpr (expAt_derivative a), expAt_nonzero a⟩

private theorem expAt_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    expAt (∑ i ∈ s, f i) = ∏ i ∈ s, expAt (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expAt]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.prod_insert hi,← ih]
    exact (PowerSeries.exp_mul_exp_eq_exp_add _ _).symm

private theorem expAt_nsmul (a : ℂ) (n : ℕ) : expAt (n • a) = (expAt a) ^ n := by
  induction n with
  | zero => simp [expAt]
  | succ n ih =>
    rw [succ_nsmul,pow_succ,← ih]
    exact (PowerSeries.exp_mul_exp_eq_exp_add _ _).symm

private theorem algebraicIndependent_expAt {ι : Type*} (a : ι → ℂ) (ha : LinearIndependent ℚ a) :
    AlgebraicIndependent ℂ (fun i => expAt (a i)) := by
  classical
  let weight := Finsupp.linearCombination ℕ a
  have hinj : Function.Injective weight := (ha.restrict_scalars' ℕ).finsuppLinearCombination_injective
  have hw (d : ι →₀ ℕ) : expAt (weight d) = d.prod (fun i k => expAt (a i) ^ k) := by
    change expAt (∑ i ∈ d.support, d i • a i) = ∏ i ∈ d.support, expAt (a i) ^ d i
    rw [expAt_sum]
    simp only [expAt_nsmul]
  have he := (expAt_independent.comp weight hinj).finsuppLinearCombination_injective
  have hEval (p : MvPolynomial ι ℂ) :
      Finsupp.linearCombination ℂ (expAt ∘ weight) (AddMonoidAlgebra.coeff p) =
       aeval (fun i => expAt (a i)) p := by
    change (∑ d ∈ p.support, coeff d p • expAt (weight d)) = p.eval₂ _ _
    rw [eval₂_eq]
    simp only [hw,Algebra.smul_def,Finsupp.prod]
  intro p q h
  exact AddMonoidAlgebra.coeff_injective (he ((hEval p).trans (h.trans (hEval q).symm)))

/-- Translating independent coordinates by arbitrary constants preserves independence. -/
theorem algebraicIndependent_translate {ι : Type*} {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {z : ι → A} (hz : AlgebraicIndependent R z) (t : ι → R) :
    AlgebraicIndependent R (fun i => z i + algebraMap R A (t i)) := by
  let φ := aeval (R := R) (fun i => MvPolynomial.X i + MvPolynomial.C (t i))
  let ψ := aeval (R := R) (fun i => MvPolynomial.X i - MvPolynomial.C (t i))
  have hinv : ψ.comp φ = AlgHom.id _ _ := by
    ext i
    simp [ψ,φ]
  have hcomp : (aeval z).comp φ = aeval (fun i => z i + algebraMap R A (t i)) := by
    ext i
    simp [φ]
  intro p q h
  have hh : φ p = φ q := hz (by simpa only [← hcomp,AlgHom.comp_apply] using h)
  simpa only [← AlgHom.comp_apply,hinv,AlgHom.id_apply] using congrArg ψ hh

theorem exists_independent_zero_series (n : ℕ) :
    ∃ x : Fin n → PowerSeries ℂ, AlgebraicIndependent ℂ x ∧ ∀ i, PowerSeries.constantCoeff (x i) = 0 := by
  have hn : (n : Cardinal) ≤ Module.rank ℚ ℂ := by
    rw [Complex.rank_rat_complex]
    exact Cardinal.natCast_le_aleph0.trans Cardinal.aleph0_le_continuum
  obtain ⟨a, ha⟩ := exists_linearIndependent_of_le_rank hn
  refine ⟨fun i => expAt (a i) + algebraMap ℂ _ (-1), algebraicIndependent_translate (algebraicIndependent_expAt a ha) _, ?_⟩
  intro i
  simp [expAt_coeff_zero]

/-- A dominant formal arc through a prescribed complex point of affine space. -/
theorem exists_independent_residue {ι : Type*} [Fintype ι] (y : ι → ℂ) :
    ∃ x : ι → PowerSeries ℂ, AlgebraicIndependent ℂ x ∧
      ∀ i, PowerSeries.constantCoeff (x i) = y i := by
  classical
  obtain ⟨s, hs, h0⟩ := exists_independent_zero_series (Fintype.card ι)
  let e := Fintype.equivFin ι
  refine ⟨fun i => s (e i) + algebraMap ℂ _ (y i),
    algebraicIndependent_translate (hs.comp e e.injective) y, ?_⟩
  intro i
  simp [h0,PowerSeries.algebraMap_apply]

end BorderDet.Curve

namespace BorderDet.Curve

/-- To lift a full closed point among finitely many conjugate branches, it suffices to lift
every individual regular function on one of them. -/
theorem exists_branch_of_pointwise {k A K I : Type} [Field k] [Infinite k]
    [CommRing A] [Algebra k A] [Field K] [Algebra k K] [Finite I]
    (b : I → A →ₐ[k] K) (y : A →ₐ[k] K)
    (h : ∀ a, ∃ i, b i a = y a) : ∃ i, b i = y := by
  classical
  by_contra! hn
  let E (i : I) := LinearMap.ker ((b i).toLinearMap - y.toLinearMap)
  have hE (i : I) : E i ≠ ⊤ := by
    intro hi
    apply hn i
    ext a
    have ha : a ∈ E i := hi ▸ Submodule.mem_top
    exact sub_eq_zero.mp (LinearMap.mem_ker.mp ha)
  obtain ⟨a,ha⟩ := Submodule.exists_forall_notMem_of_forall_ne_top E hE
  obtain ⟨i,hi⟩ := h a
  exact ha i (LinearMap.mem_ker.mpr (sub_eq_zero.mpr hi))

end BorderDet.Curve






namespace BorderDet.Curve
open Polynomial

theorem lift_residue_root {O P K : Type} [CommRing O] [IsDomain O] [Field P] [IsAlgClosed P]
    [Algebra O P] [IsFractionRing O P] [IsIntegrallyClosed O]
    [Field K] (ρ : O →+* K) {p : Polynomial O} (hm : p.Monic) {z : K}
    (hz : (p.map ρ).IsRoot z) : ∃ w : O, p.IsRoot w ∧ ρ w = z := by
  have hs : p.Splits := by
    apply Splits.of_splits_map_of_injective (IsFractionRing.injective O P) (IsAlgClosed.splits _)
    intro a ha
    apply IsIntegrallyClosed.algebraMap_eq_of_integral
    exact ⟨p,hm,(mem_aroots'.1 ha).2⟩
  have hr := (mem_roots ((hm.map ρ).ne_zero)).2 hz
  rw [hs.roots_map_of_ne_zero (hm.map ρ).ne_zero] at hr
  obtain ⟨w,hw,hh⟩ := Multiset.mem_map.1 hr
  exact ⟨w,(mem_roots hm.ne_zero).1 hw,hh⟩

/-- Every residue of an integral element along a character extends to a conjugate
of that element in the algebraically closed fraction field. The integrally
closed normalization ring ensures that the ring and field minpolys agree. -/
theorem branch_element {B A E L O P k : Type}
    [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [CommRing A] [IsDomain A]
    [Field E] [Field L] [Field P] [IsAlgClosed P] [Field k] [CommRing O] [IsDomain O] [IsIntegrallyClosed O]
    [Algebra B A] [Algebra B E] [IsFractionRing B E] [Algebra A L] [IsFractionRing A L]
    [Algebra B L] [IsScalarTower B A L] [Algebra E L] [IsScalarTower B E L] [FiniteDimensional E L]
    [Algebra B P] [Algebra E P] [IsScalarTower B E P] [Algebra O P] [IsFractionRing O P]
    (δ : B →+* O) (ρ : O →+* k) (y : A →+* k)
    (hδ : (algebraMap O P).comp δ = algebraMap B P)
    (hy : ρ.comp δ = y.comp (algebraMap B A))
    (a : A) (ha : IsIntegral B a) :
    ∃ (τ : L →ₐ[E] P) (w : O), τ (algebraMap A L a) = algebraMap O P w ∧ ρ w = y a := by
  let f := minpoly B a
  have hfm : f.Monic := minpoly.monic ha
  have hz : ((f.map δ).map ρ).IsRoot (y a) := by
    rw [IsRoot.def, Polynomial.map_map,hy,Polynomial.eval_map,← Polynomial.hom_eval₂,← Polynomial.aeval_def, minpoly.aeval, map_zero]
  obtain ⟨w,hw,hwy⟩ := lift_residue_root (P:=P) ρ (hfm.map δ) hz
  have hmin : (minpoly E (algebraMap A L a)) = f.map (algebraMap B E) :=
    minpoly.isIntegrallyClosed_eq_field_fractions E L ha
  have hroot : Polynomial.aeval (algebraMap O P w) (minpoly E (algebraMap A L a)) = 0 := by
    rw [hmin,Polynomial.aeval_def,Polynomial.eval₂_map,← IsScalarTower.algebraMap_eq B E P,← hδ]
    rw [← Polynomial.hom_eval₂, ← Polynomial.eval_map, hw, map_zero]
  obtain ⟨τ,hτ⟩ := IntermediateField.exists_algHom_of_splits_of_aeval
    (fun z : L => ⟨Algebra.IsIntegral.isIntegral z, IsAlgClosed.splits _⟩) hroot
  exact ⟨τ,w,hτ,hwy⟩
end BorderDet.Curve



namespace BorderDet.Curve

theorem whole_branch {B A E L O P k : Type}
    [Field k] [Infinite k] [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [CommRing A] [IsDomain A]
    [Field E] [Field L] [Field P] [IsAlgClosed P] [CommRing O] [IsDomain O] [IsIntegrallyClosed O]
    [Algebra B A] [Algebra B E] [IsFractionRing B E] [Algebra A L] [IsFractionRing A L]
    [Algebra B L] [IsScalarTower B A L] [Algebra E L] [IsScalarTower B E L] [FiniteDimensional E L]
    [Algebra B P] [Algebra E P] [IsScalarTower B E P] [Algebra O P] [IsFractionRing O P]
    [Algebra k A] [Algebra k O] [Algebra k P] [Algebra k E] [Algebra k L]
    [IsScalarTower k A L] [IsScalarTower k E L] [IsScalarTower k E P] [IsScalarTower k O P]
    (δ : B →+* O) (ρ : O →ₐ[k] k) (y : A →ₐ[k] k)
    (hδ : (algebraMap O P).comp δ = algebraMap B P)
    (hy : ρ.toRingHom.comp δ = y.toRingHom.comp (algebraMap B A))
    (hA : ∀ a : A, IsIntegral B a) :
    ∃ e : A →ₐ[k] P, Function.Injective e ∧
      ∀ a, ∃ w : O, algebraMap O P w = e a ∧ ρ w = y a := by
  classical
  let e (τ : L →ₐ[E] P) := (τ.restrictScalars k).comp (IsScalarTower.toAlgHom k A L)
  have hcomp (τ : L →ₐ[E] P) : (algebraMap O P).comp δ = (e τ).toRingHom.comp (algebraMap B A) := by
    rw [hδ]
    ext b
    change algebraMap B P b = τ (algebraMap A L (algebraMap B A b))
    rw [← IsScalarTower.algebraMap_apply B A L, IsScalarTower.algebraMap_apply B E L,
      τ.commutes, ← IsScalarTower.algebraMap_apply B E P]
  have integral (τ : L →ₐ[E] P) (a : A) : IsIntegral O (e τ a) :=
    IsIntegral.map_of_comp_eq δ (e τ).toRingHom (hcomp τ) (hA a)
  choose g hg using fun (τ : L →ₐ[E] P) (a : A) =>
    IsIntegrallyClosed.algebraMap_eq_of_integral (integral τ a)
  have inj := IsFractionRing.injective O P
  let G (τ : L →ₐ[E] P) : A →ₐ[k] O := {
    toFun := g τ
    map_zero' := inj (by rw [hg,map_zero,map_zero])
    map_one' := inj (by rw [hg,map_one,map_one])
    map_add' := fun a b => inj (by rw [hg,map_add,map_add,hg,hg])
    map_mul' := fun a b => inj (by rw [hg,map_mul,map_mul,hg,hg])
    commutes' := fun r => inj (by rw [hg, (e τ).commutes, ← IsScalarTower.algebraMap_apply k O P]) }
  have pointwise (a : A) : ∃ τ : L →ₐ[E] P, (ρ.comp (G τ)) a = y a := by
    obtain ⟨τ,w,hw,hy⟩ := branch_element (E:=E) (L:=L) (P:=P) δ ρ.toRingHom y.toRingHom hδ hy a (hA a)
    have hgw : g τ a = w := inj ((hg τ a).trans hw)
    exact ⟨τ, (congrArg ρ hgw).trans hy⟩
  obtain ⟨τ,hτ⟩ := exists_branch_of_pointwise (fun τ => ρ.comp (G τ)) y pointwise
  refine ⟨e τ, τ.injective.comp (IsFractionRing.injective A L),fun a => ?_⟩
  exact ⟨g τ a, hg τ a, DFunLike.congr_fun hτ a⟩

end BorderDet.Curve




namespace BorderDet.Curve.Puiseux
open HahnSeries
variable (K : Type) [Field K]
noncomputable def v : Valuation (PuiseuxSeries K) (Multiplicative (WithTop ℚ)ᵒᵈ) := ((HahnSeries.addVal ℚ K).toValuation).comap (PuiseuxSeries.subfield K).subtype
noncomputable abbrev O := (v K).integer

theorem mem_O (x : PuiseuxSeries K) : x ∈ O K ↔ 0 ≤ x.val.orderTop := Iff.rfl

theorem coeff_neg (x : O K) (i : ℚ) (hi : i < 0) : x.val.val.coeff i = 0 :=
  HahnSeries.le_orderTop_iff_forall.1 ((mem_O K x.val).1 x.property) i (by exact_mod_cast hi)

noncomputable def res : O K →+* K where
  toFun a := a.val.val.coeff 0
  map_one' := by change (1 : HahnSeries ℚ K).coeff 0 = 1; simp
  map_mul' a b := by
    change (a.val.val * b.val.val).coeff 0 = _
    rw [HahnSeries.coeff_mul]
    apply Finset.sum_eq_single (0,0)
    · intro ij hij hne
      have he := (Finset.mem_antidiagonal.1 hij).2.2
      by_cases hi : ij.1 < 0
      · rw [coeff_neg _ a _ hi,zero_mul]
      · have hj : ij.2 < 0 := by
          by_contra! h
          apply hne
          ext <;> linarith
        rw [coeff_neg _ b _ hj,mul_zero]
    · intro h
      by_contra hx
      apply h
      exact Finset.mem_antidiagonal.2 ⟨(mul_ne_zero_iff.1 hx).1,(mul_ne_zero_iff.1 hx).2,zero_add _⟩
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable def liftPS : PowerSeries K →+* O K :=
  ((algebraMap (LaurentSeries K) (PuiseuxSeries K)).comp (HahnSeries.ofPowerSeries ℤ K)).codRestrict _ (by
    intro a
    apply (mem_O K _).2
    apply HahnSeries.le_orderTop_iff_forall.2
    intro j hj
    change (LaurentSeries.toHahn K 1 (↑a : LaurentSeries K)).coeff j = 0
    by_cases h : ∃ i : ℤ, j = (i:ℚ)/(1:ℕ)
    · obtain ⟨i,rfl⟩ := h
      rw [show (LaurentSeries.toHahn K 1 (↑a : LaurentSeries K)).coeff ((i:ℚ)/(1:ℕ)) =
        (↑a : LaurentSeries K).coeff i from HahnSeries.embDomain_coeff, PowerSeries.coeff_coe, if_pos]
      simpa using hj
    · exact HahnSeries.embDomain_of_notMem_range (fun ⟨i,hi⟩ => h ⟨i,hi.symm⟩))

theorem res_liftPS : (res K).comp (liftPS K) = PowerSeries.constantCoeff := by
  ext a
  change (LaurentSeries.toHahn K 1 (↑a : LaurentSeries K)).coeff 0 = _
  have h : (LaurentSeries.toHahn K 1 (↑a : LaurentSeries K)).coeff ((0:ℤ)/((1:ℕ):ℚ)) =
      (↑a : LaurentSeries K).coeff (0:ℤ) := HahnSeries.embDomain_coeff
  simpa [PowerSeries.coeff_coe] using h

theorem inj_liftPS : Function.Injective (liftPS K) := by
  intro a b he
  have := congrArg Subtype.val he
  exact HahnSeries.ofPowerSeries_injective ((algebraMap (LaurentSeries K) (PuiseuxSeries K)).injective this)

end BorderDet.Curve.Puiseux



open MvPolynomial
namespace BorderDet.Curve

noncomputable def puiseuxC (K : Type) [Field K] : K →+* PuiseuxSeries K :=
  (algebraMap (LaurentSeries K) (PuiseuxSeries K)).comp HahnSeries.C

theorem puiseuxC_val {K : Type} [Field K] (k : K) :
    (puiseuxC K k).val = HahnSeries.C k := by
  change LaurentSeries.toHahn K 1 (HahnSeries.single 0 k) = HahnSeries.single 0 k
  simp

theorem toHahn_coeff {K : Type} [Field K] (N : ℕ+) (x : LaurentSeries K) (i : ℤ) :
    (LaurentSeries.toHahn K N x).coeff ((i : ℚ) / (N : ℕ)) = x.coeff i :=
  HahnSeries.embDomain_coeff

theorem common_laurent {K I : Type} [Field K] [Fintype I] (x : I → PuiseuxSeries K) :
    ∃ (N : ℕ+) (z : I → LaurentSeries K), ∀ i, LaurentSeries.toHahn K N (z i) = (x i).val := by
  classical
  let s := Finset.univ.image fun i => (x i).val
  obtain ⟨N,h⟩ := PuiseuxSeries.exists_common_index K s (by
    intro b hb
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.1 hb
    exact (x i).property)
  choose z hz using fun i => h (x i).val (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  exact ⟨N,z,hz⟩

theorem laurent_regular {K : Type} [Field K] (z : LaurentSeries K) (hz : ∀ i < 0, z.coeff i = 0) :
    ∃ q : PowerSeries K, HahnSeries.ofPowerSeries ℤ K q = z ∧ PowerSeries.constantCoeff q = z.coeff 0 := by
  let q := PowerSeries.mk fun i => z.coeff (i:ℤ)
  refine ⟨q,?_,?_⟩
  · ext i
    change (↑q : LaurentSeries K).coeff i = z.coeff i
    rw [PowerSeries.coeff_coe]
    cases i with
    | ofNat i => simp [q]
    | negSucc i => simp [hz _ (Int.negSucc_lt_zero _)]
  · simp [q,← PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem select_common_parameter {k K I J : Type} [Field k] [Field K] [Fintype I]
    (c : k →+* K) (F : J → MvPolynomial I k) (x : I → PuiseuxSeries K) (y : J → K)
    (hreg : ∀ j i, i < 0 → ((eval₂Hom ((puiseuxC K).comp c) x (F j)).val).coeff i = 0)
    (hres : ∀ j, ((eval₂Hom ((puiseuxC K).comp c) x (F j)).val).coeff 0 = y j) :
    ∃ (z : I → LaurentSeries K) (q : J → PowerSeries K), ∀ j,
      eval₂Hom (HahnSeries.C.comp c) z (F j) = HahnSeries.ofPowerSeries ℤ K (q j) ∧
      PowerSeries.constantCoeff (q j) = y j := by
  classical
  obtain ⟨N,z,hz⟩ := common_laurent x
  let A := eval₂Hom (HahnSeries.C.comp c) z
  let B := eval₂Hom ((puiseuxC K).comp c) x
  let ν : PuiseuxSeries K →+* HahnSeries ℚ K := (PuiseuxSeries.subfield K).subtype
  have he : (LaurentSeries.toHahn K N).comp A = ν.comp B := by
    apply ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, A, B, eval₂Hom_C]
      change LaurentSeries.toHahn K N (HahnSeries.C (c a)) = (puiseuxC K (c a)).val
      rw [puiseuxC_val, HahnSeries.C_apply, LaurentSeries.toHahn_single]
      simp
    · intro i
      simp only [RingHom.comp_apply,A,B,eval₂Hom_X']
      exact hz i
  have he' (j : J) (i : ℤ) : (A (F j)).coeff i = (B (F j)).val.coeff ((i:ℚ)/(N:ℕ)) := by
    rw [← toHahn_coeff N (A (F j)) i]
    have := DFunLike.congr_fun he (F j)
    exact congrArg (fun w : HahnSeries ℚ K => w.coeff ((i:ℚ)/(N:ℕ))) this
  have hr (j : J) (i : ℤ) (hi : i < 0) : (A (F j)).coeff i = 0 := by
    rw [he']
    exact hreg j _ (div_neg_of_neg_of_pos (by exact_mod_cast hi) (by positivity))
  choose q hq hc using fun j => laurent_regular (A (F j)) (hr j)
  exact ⟨z,q,fun j => ⟨(hq j).symm,(hc j).trans ((he' j 0).trans (by simpa [B] using hres j))⟩⟩
end BorderDet.Curve







namespace BorderDet.Curve
open MvPolynomial
open Puiseux

noncomputable instance puiseuxAlgebra (K : Type) [Field K] : Algebra K (PuiseuxSeries K) :=
  (puiseuxC K).toAlgebra

noncomputable instance puiseuxIntegerAlgebra (K : Type) [Field K] : Algebra K (O K) :=
  ((liftPS K).comp PowerSeries.C).toAlgebra

instance puiseuxIntegerTower (K : Type) [Field K] : IsScalarTower K (O K) (PuiseuxSeries K) :=
  IsScalarTower.of_algebraMap_eq fun r => by
    change puiseuxC K r = algebraMap (LaurentSeries K) (PuiseuxSeries K) (HahnSeries.ofPowerSeries ℤ K (PowerSeries.C r))
    rw [HahnSeries.ofPowerSeries_C]
    rfl

noncomputable def residueAlg (K : Type) [Field K] : O K →ₐ[K] K :=
  { res K with
    commutes' := fun r => by
      change ((res K).comp (liftPS K)) (PowerSeries.C r) = r
      rw [res_liftPS,PowerSeries.constantCoeff_C] }

theorem normalized_arc {A : Type} [CommRing A] [IsDomain A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] (y : A →ₐ[ℂ] ℂ) :
    ∃ e : A →ₐ[ℂ] PuiseuxSeries ℂ, Function.Injective e ∧ ∀ a,
      (∀ i : ℚ, i < 0 → (e a).val.coeff i = 0) ∧ (e a).val.coeff 0 = y a := by
  classical
  obtain ⟨n,g,hg,hfin⟩ := exists_finite_inj_algHom_of_fg ℂ A
  let B := MvPolynomial (Fin n) ℂ
  letI : Algebra B A := g.toRingHom.toAlgebra
  letI : IsScalarTower ℂ B A := IsScalarTower.of_algebraMap_eq fun r => (g.commutes r).symm
  letI : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).2 hg
  letI : Module.Finite B A := hfin
  let E := FractionRing B
  let L := FractionRing A
  let P := PuiseuxSeries ℂ
  let D := O ℂ
  letI : Algebra E L := FractionRing.liftAlgebra B L
  letI : IsScalarTower B E L := FractionRing.isScalarTower_liftAlgebra ..
  letI : IsScalarTower ℂ E L := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply ℂ B E, ← IsScalarTower.algebraMap_apply B E L,← IsScalarTower.algebraMap_apply ℂ B L]
  obtain ⟨x,hx,hres⟩ := exists_independent_residue (fun i : Fin n => y (g (X i)))
  let d : B →+* D := (liftPS ℂ).comp (aeval x).toRingHom
  let j : B →+* P := (algebraMap D P).comp d
  letI : Algebra B P := j.toAlgebra
  letI : FaithfulSMul B P := (faithfulSMul_iff_algebraMap_injective B P).2
    ((IsFractionRing.injective D P).comp ((inj_liftPS ℂ).comp hx))
  letI : Algebra E P := FractionRing.liftAlgebra B P
  letI : IsScalarTower B E P := FractionRing.isScalarTower_liftAlgebra ..
  letI : IsScalarTower ℂ B P := IsScalarTower.of_algebraMap_eq fun r => by
    change puiseuxC ℂ r = algebraMap D P (liftPS ℂ (aeval x (C r)))
    rw [aeval_C]
    exact IsScalarTower.algebraMap_apply ℂ D P r
  letI : IsScalarTower ℂ E P := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply ℂ B E, ← IsScalarTower.algebraMap_apply B E P,← IsScalarTower.algebraMap_apply ℂ B P]
  have hdy : (residueAlg ℂ).toRingHom.comp d = y.toRingHom.comp (algebraMap B A) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change ((res ℂ).comp (liftPS ℂ)) (aeval x (C r)) = y (g (C r))
      rw [res_liftPS]
      simp
    · intro i
      change ((res ℂ).comp (liftPS ℂ)) (aeval x (X i)) = y (g (X i))
      rw [res_liftPS,aeval_X]
      exact hres i
  obtain ⟨e,he,hw⟩ := whole_branch (E:=E) (L:=L) (P:=P) d (residueAlg ℂ) y rfl hdy
    (fun a => Algebra.IsIntegral.isIntegral a)
  refine ⟨e,he,fun a => ?_⟩
  obtain ⟨w,hw,hval⟩ := hw a
  rw [← hw]
  exact ⟨coeff_neg ℂ w,hval⟩
end BorderDet.Curve


/-

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/

open MvPolynomial
open scoped TensorProduct
namespace BorderDet.Curve

private theorem fields_tensor_nontrivial (k L P : Type) [Field k] [Field L] [Field P]
    [Algebra k L] [Algebra k P] : Nontrivial (L ⊗[k] P) := inferInstance

/-- An embedding of a polynomial image's coordinate ring into an algebraically closed
field lifts to a point of the source. The embedding makes the generic fiber nonempty,
and the weak Nullstellensatz gives a rational point in its scalar extension. -/
theorem extend_image_point {I k P : Type} [Fintype I] [Field k] [Field P]
    [Algebra k P] [IsAlgClosed P] (A : Subalgebra k (MvPolynomial I k))
    (e : A →ₐ[k] P) (he : Function.Injective e) :
    ∃ x : I → P, ∀ a : A, aeval x (a : MvPolynomial I k) = e a := by
  classical
  let B := MvPolynomial I k
  let L := FractionRing B
  let K := FractionRing A
  let i : A →+* L := (algebraMap B L).comp A.val.toRingHom
  have hi : Function.Injective i := (IsFractionRing.injective B L).comp Subtype.val_injective
  let f : K →+* L := IsFractionRing.lift hi
  let g : K →+* P := IsFractionRing.lift he
  letI : Algebra K L := f.toAlgebra
  letI : Algebra K P := g.toAlgebra
  let T := L ⊗[K] P
  letI : Nontrivial T := fields_tensor_nontrivial K L P
  let l : L →ₐ[K] T := Algebra.TensorProduct.includeLeft
  let r : P →ₐ[K] T := Algebra.TensorProduct.includeRight
  have agree (a : A) : l (i a) = r (e a) := by
    have hf : algebraMap K L (algebraMap A K a) = i a := IsFractionRing.lift_algebraMap hi a
    have hg : algebraMap K P (algebraMap A K a) = e a := IsFractionRing.lift_algebraMap he a
    rw [← hf, ← hg, l.commutes, r.commutes]
  let z (v : I) := l (algebraMap B L (X v))
  let φ : MvPolynomial I P →+* T := eval₂Hom r.toRingHom z
  have hm : φ.comp (map (algebraMap k P)) = l.toRingHom.comp (algebraMap B L) := by
    apply MvPolynomial.ringHom_ext
    · intro b
      have h := (agree (algebraMap k A b)).symm
      rw [e.commutes] at h
      simp only [RingHom.comp_apply, map_C, φ, eval₂Hom_C]
      exact h
    · intro v
      simp only [RingHom.comp_apply, map_X, φ, eval₂Hom_X']
      rfl
  obtain ⟨M,hM,hker⟩ := Ideal.exists_le_maximal (RingHom.ker φ) (RingHom.ker_ne_top φ)
  obtain ⟨x,rfl⟩ := isMaximal_iff_eq_vanishingIdeal_singleton.1 hM
  refine ⟨x,fun a => ?_⟩
  let u := map (algebraMap k P) (a : B) - C (e a)
  have hu : u ∈ RingHom.ker φ := by
    apply RingHom.mem_ker.2
    rw [show φ u = φ (map (algebraMap k P) (a : B)) - φ (C (e a)) from map_sub _ _ _]
    rw [← RingHom.comp_apply,hm,RingHom.comp_apply,sub_eq_zero]
    rw [show φ (C (e a)) = r (e a) from eval₂Hom_C _ _ _]
    exact agree a
  have hz := mem_vanishingIdeal_iff.1 (hker hu) x (Set.mem_singleton x)
  change aeval x u = 0 at hz
  rw [show aeval x u = aeval x (map (algebraMap k P) (a : B)) - aeval x (C (e a)) from map_sub _ _ _, aeval_C, sub_eq_zero] at hz
  exact (show aeval x (map (algebraMap k P) (a : B)) = aeval x (a : B) by
    rw [aeval_def,eval₂_map]
    rfl).symm.trans hz

end BorderDet.Curve

open MvPolynomial
open BorderDet.Curve

theorem solution :
  ∀ (I J : Type) [Fintype I] [Fintype J] (F : J → MvPolynomial I ℂ) (p : J → ℂ),
    (∀ g : MvPolynomial J ℂ, aeval F g = 0 → eval p g = 0) →
    ∃ (K : Type) (_ : Field K) (j : ℂ →+* K)
      (x : I → LaurentSeries K) (q : J → PowerSeries K),
      ∀ i, eval₂Hom ((algebraMap K (LaurentSeries K)).comp j) x (F i) = HahnSeries.ofPowerSeries ℤ K (q i) ∧
        PowerSeries.constantCoeff (q i) = j (p i) := by
  intro I J _ _ F p h
  let A := (aeval (R := ℂ) F).range
  let φ : MvPolynomial J ℂ →ₐ[ℂ] A := (aeval (R := ℂ) F).rangeRestrict
  have hsurj : Function.Surjective φ := (aeval (R := ℂ) F).rangeRestrict_surjective
  have hker : RingHom.ker φ.toRingHom ≤ RingHom.ker (aeval p).toRingHom := by
    intro g hg
    exact h g (congrArg Subtype.val (RingHom.mem_ker.1 hg))
  let y := φ.liftOfSurjective hsurj (aeval p) hker
  have hy (g) : y (φ g) = aeval p g := AlgHom.liftOfSurjective_apply φ hsurj (aeval p) hker g
  letI : Algebra.FiniteType ℂ A := Algebra.FiniteType.of_surjective φ hsurj
  obtain ⟨e,he,hreg⟩ := normalized_arc y
  obtain ⟨t,ht⟩ := extend_image_point A e he
  have hφ (i : J) : (φ (X i) : MvPolynomial I ℂ) = F i := aeval_X _ _
  have houtput (i : J) : aeval t (F i) = e (φ (X i)) := by rw [← hφ]; exact ht (φ (X i))
  have hp (i : J) : y (φ (X i)) = p i := (hy (X i)).trans (aeval_X _ _)
  have hz (i : J) : (∀ r : ℚ, r < 0 → (aeval t (F i)).val.coeff r = 0) ∧
      (aeval t (F i)).val.coeff 0 = p i := by
    rw [houtput]; exact ⟨(hreg _).1,(hreg _).2.trans (hp i)⟩
  obtain ⟨z,q,hz⟩ := select_common_parameter (RingHom.id ℂ) F t p
    (fun i => (hz i).1) (fun i => (hz i).2)
  refine ⟨ℂ,inferInstance,RingHom.id ℂ,z,q,?_⟩
  have hs : algebraMap ℂ (LaurentSeries ℂ) = HahnSeries.C := by
    apply RingHom.ext
    intro a
    change HahnSeries.ofPowerSeries ℤ ℂ (algebraMap ℂ (PowerSeries ℂ) a) = HahnSeries.C a
    simp [PowerSeries.algebraMap_apply]
  simpa only [hs, RingHom.id_apply] using hz
