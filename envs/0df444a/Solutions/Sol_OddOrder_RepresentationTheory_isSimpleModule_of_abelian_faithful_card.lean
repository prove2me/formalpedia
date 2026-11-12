-- Prove2me | solution 1 for OddOrder.RepresentationTheory.isSimpleModule_of_abelian_faithful_card
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T04:45:22.692216+00:00
-- url     : https://prove2.me/submissions/7939498c-9fe7-40f0-8cc0-3c7c789c3154

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/PrimitivePrimeDivisor.lean
--   OddOrder/GroupTheory/RepresentationTheory/SingerField.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SingerField
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.RepresentationTheory.Maschke
import Mathlib.GroupTheory.SpecificGroups.Cyclic

-- ===== OddOrder/GroupTheory/PrimitivePrimeDivisor.lean =====
namespace OddOrder.NumberTheory

open Finset

/-- **Any prime factor `r ≠ q` of `∑_{i<q} p^i` is a primitive prime divisor of `p^q - 1`**:
`orderOf (p : ZMod r) = q`.  (The `q`-part of the geometric sum is handled separately; here `r ≠ q`
is the hypothesis.)  From `r ∣ ∑_{i<q} p^i ∣ p^q - 1` the order divides the prime `q`; and it cannot
be `1`, since `(p : ZMod r) = 1` would give `0 = ∑ (p:ZMod r)^i = q` in `ZMod r`, i.e. `r ∣ q`. -/
theorem orderOf_eq_of_prime_dvd_geomSum {p q r : ℕ} (hq : q.Prime)
    (hr : r.Prime) (hrq : r ≠ q) (hrn : r ∣ ∑ i ∈ range q, p ^ i) :
    orderOf (p : ZMod r) = q := by
  have : Fact r.Prime := ⟨hr⟩
  -- In `ZMod r`, the geometric sum vanishes: `∑ (p:ZMod r)^i = 0`.
  have hsum0 : ∑ i ∈ range q, (p : ZMod r) ^ i = 0 := by
    have : ((∑ i ∈ range q, p ^ i : ℕ) : ZMod r) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hrn
    push_cast at this
    exact this
  -- Hence `(p:ZMod r)^q = 1`, so `orderOf (p:ZMod r) ∣ q`.
  have hpow : (p : ZMod r) ^ q = 1 := by
    have hgm := geom_sum_mul (p : ZMod r) q
    rw [hsum0, zero_mul] at hgm
    exact sub_eq_zero.mp hgm.symm
  have hdvd : orderOf (p : ZMod r) ∣ q := orderOf_dvd_of_pow_eq_one hpow
  -- `orderOf ≠ 1`: else `(p:ZMod r) = 1`, forcing `q = 0` in `ZMod r`, i.e. `r ∣ q`.
  have hne1 : orderOf (p : ZMod r) ≠ 1 := by
    intro h1
    have hp1 : (p : ZMod r) = 1 := orderOf_eq_one_iff.mp h1
    have : ((q : ℕ) : ZMod r) = 0 := by
      have : ∑ i ∈ range q, (p : ZMod r) ^ i = ∑ _i ∈ range q, (1 : ZMod r) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hp1, one_pow]
      rw [this, Finset.sum_const, card_range, nsmul_eq_mul, mul_one] at hsum0
      exact hsum0
    have hrdvdq : r ∣ q := (ZMod.natCast_eq_zero_iff _ _).mp this
    exact hrq ((Nat.prime_dvd_prime_iff_eq hr hq).mp hrdvdq)
  -- `orderOf ∣ q` (prime) and `≠ 1` ⟹ `= q`.
  rcases (Nat.Prime.eq_one_or_self_of_dvd hq _ hdvd) with h | h
  · exact absurd h hne1
  · exact h

/-- If the odd prime `q` divides `∑_{i<q} p^i`, then `q ∣ p - 1`.  In `ZMod q` the geometric sum
vanishes, so `(p:ZMod q)^q = 1`; but `(p:ZMod q)^q = (p:ZMod q)` (Frobenius), giving
`(p:ZMod q) = 1`. -/
theorem dvd_sub_one_of_dvd_geomSum {p q : ℕ} (hp : 2 ≤ p) (hq : q.Prime)
    (hqn : q ∣ ∑ i ∈ range q, p ^ i) : q ∣ p - 1 := by
  have : Fact q.Prime := ⟨hq⟩
  have hsum0 : ∑ i ∈ range q, (p : ZMod q) ^ i = 0 := by
    have : ((∑ i ∈ range q, p ^ i : ℕ) : ZMod q) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hqn
    push_cast at this; exact this
  have hpow : (p : ZMod q) ^ q = 1 := by
    have hgm := geom_sum_mul (p : ZMod q) q
    rw [hsum0, zero_mul] at hgm
    exact sub_eq_zero.mp hgm.symm
  have hp1 : (p : ZMod q) = 1 := by
    have hfrob : (p : ZMod q) ^ q = (p : ZMod q) := ZMod.pow_card _
    rw [hfrob] at hpow; exact hpow
  have : ((p - 1 : ℕ) : ZMod q) = 0 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ p), hp1]; ring
  exact (ZMod.natCast_eq_zero_iff _ _).mp this

/-- `q² ∤ ∑_{i<q} p^i` for `q` an odd prime, `p ≥ 2`.  If `q ∤ n` this is trivial; if `q ∣ n` then
`q ∣ p - 1`, and lifting the exponent gives `v_q(p^q - 1) = v_q(p - 1) + 1`, so as
`n·(p-1) = p^q - 1` we get `v_q(n) = 1`. -/
theorem not_sq_dvd_geomSum {p q : ℕ} (hp : 2 ≤ p) (hq : q.Prime) (hq2 : q ≠ 2) :
    ¬ q ^ 2 ∣ ∑ i ∈ range q, p ^ i := by
  have : Fact q.Prime := ⟨hq⟩
  by_cases hqn : q ∣ ∑ i ∈ range q, p ^ i
  · -- `q ∣ n`: LTE ⟹ `v_q(n) = 1`.
    have hqp1 : q ∣ p - 1 := dvd_sub_one_of_dvd_geomSum hp hq hqn
    -- `n * (p - 1) = p^q - 1`
    have hdvd : (p - 1) ∣ p ^ q - 1 := by
      have h1 : (1 : ℕ) ≡ p ^ q [MOD p - 1] := by
        have hp1 : (1 : ℕ) ≡ p [MOD p - 1] := (Nat.modEq_iff_dvd' (by omega)).mpr dvd_rfl
        simpa using hp1.pow q
      exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp h1
    have hfact : (∑ i ∈ range q, p ^ i) * (p - 1) = p ^ q - 1 := by
      rw [Nat.geomSum_eq hp q, Nat.div_mul_cancel hdvd]
    have hqodd : Odd q := hq.odd_of_ne_two hq2
    -- `q ∤ p` (else `q ∣ p` with `q ∣ p-1` gives `q ∣ 1`).
    have hqp : ¬ q ∣ p := by
      intro h
      have h1 : p ≡ 1 [MOD q] := ((Nat.modEq_iff_dvd' (by omega : 1 ≤ p)).mpr hqp1).symm
      have h0 : p ≡ 0 [MOD q] := (Nat.modEq_zero_iff_dvd).mpr h
      have hd : q ∣ 1 := (Nat.modEq_iff_dvd' (by norm_num : (0 : ℕ) ≤ 1)).mp (h0.symm.trans h1)
      exact absurd (Nat.le_of_dvd one_pos hd) (by have := hq.two_le; omega)
    -- lifting the exponent: `v_q(p^q - 1) = v_q(p-1) + v_q(q) = v_q(p-1) + 1`.
    have hself : emultiplicity q q = 1 :=
      (Nat.finiteMultiplicity_iff.mpr ⟨hq.ne_one, hq.pos⟩).emultiplicity_self
    have hLTE : emultiplicity q (p ^ q - 1) = emultiplicity q (p - 1) + 1 := by
      have h := Nat.emultiplicity_pow_sub_pow hq hqodd hqp1 hqp q
      rwa [one_pow, hself] at h
    -- `v_q(n) + v_q(p-1) = v_q(p^q-1) = v_q(p-1) + 1`, cancel to `v_q(n) = 1`.
    have hfin : emultiplicity q (p - 1) ≠ ⊤ :=
      finiteMultiplicity_iff_emultiplicity_ne_top.mp
        (Nat.finiteMultiplicity_iff.mpr ⟨hq.ne_one, by omega⟩)
    have hn1 : emultiplicity q (∑ i ∈ range q, p ^ i) = 1 := by
      have hmul : emultiplicity q (∑ i ∈ range q, p ^ i) + emultiplicity q (p - 1)
          = emultiplicity q (p - 1) + 1 := by
        rw [← emultiplicity_mul hq.prime, hfact, hLTE]
      rw [add_comm (emultiplicity q (p - 1)) 1] at hmul
      exact WithTop.add_right_cancel hfin hmul
    rw [pow_dvd_iff_le_emultiplicity, hn1]
    decide
  · exact fun h => hqn (dvd_trans (dvd_pow_self q (by norm_num)) h)

/-- **Primitive prime divisor** (Zsygmondy, `n = q` prime case): for `q` an odd prime and `p ≥ 2`,
`∑_{i<q} p^i = (p^q-1)/(p-1)` has a prime divisor `r` with `orderOf (p : ZMod r) = q`. -/
theorem exists_prime_orderOf_eq {p q : ℕ} (hp : 2 ≤ p) (hq : q.Prime) (hq2 : q ≠ 2) :
    ∃ r : ℕ, r.Prime ∧ r ∣ (∑ i ∈ range q, p ^ i) ∧ orderOf (p : ZMod r) = q := by
  set n := ∑ i ∈ range q, p ^ i with hndef
  -- `q < n`: the sum of `q` terms `p^i ≥ 1`, with the `i=1` term `p ≥ 2` strict.
  have hqn : q < n := by
    calc q = ∑ _i ∈ range q, 1 := by
            rw [Finset.sum_const, card_range, smul_eq_mul, mul_one]
      _ < ∑ i ∈ range q, p ^ i := by
            refine Finset.sum_lt_sum (fun i _ => Nat.one_le_pow _ _ (by omega)) ?_
            exact ⟨1, Finset.mem_range.mpr (by have := hq.two_le; omega),
              by rw [pow_one]; omega⟩
  have hnsq : ¬ q ^ 2 ∣ n := not_sq_dvd_geomSum hp hq hq2
  -- Extract a prime factor `r ≠ q` of `n`.
  by_cases hqdvd : q ∣ n
  · -- `q ∣ n`: write `n = q·m`; then `q ∤ m` (else `q² ∣ n`) and `m > 1` (else `n = q`).
    obtain ⟨m, hm⟩ := hqdvd
    have hqm : ¬ q ∣ m := by
      rintro ⟨t, rfl⟩
      exact hnsq ⟨t, by rw [hm]; ring⟩
    have hm1 : m ≠ 1 := by rintro rfl; rw [mul_one] at hm; omega
    obtain ⟨r, hr, hrm⟩ := Nat.exists_prime_and_dvd hm1
    have hrn : r ∣ n := by rw [hm]; exact Dvd.dvd.mul_left hrm q
    have hrq : r ≠ q := by rintro rfl; exact hqm hrm
    exact ⟨r, hr, hrn, orderOf_eq_of_prime_dvd_geomSum hq hr hrq hrn⟩
  · -- `q ∤ n`: any prime factor of `n` works (it is automatically `≠ q`).
    obtain ⟨r, hr, hrn⟩ := Nat.exists_prime_and_dvd (by have := hq.two_le; omega : n ≠ 1)
    have hrq : r ≠ q := by rintro rfl; exact hqdvd hrn
    exact ⟨r, hr, hrn, orderOf_eq_of_prime_dvd_geomSum hq hr hrq hrn⟩

end OddOrder.NumberTheory

-- ===== OddOrder/GroupTheory/RepresentationTheory/SingerField.lean =====
namespace OddOrder.RepresentationTheory

universe u

variable {p : ℕ} {C M : Type u} [CommGroup C] [AddCommGroup M]
  [Module (MonoidAlgebra (ZMod p) C) M]

namespace SingerFieldData

/-- The additive isomorphism transports cardinality: `|K| = |M|`. -/
theorem card_K_eq [Fintype M] (data : SingerFieldData (p := p) (C := C) (M := M)) :
    Fintype.card data.K = Fintype.card M :=
  (Fintype.card_congr data.e.toEquiv).symm

end SingerFieldData

/-- **Singer mechanism (abelian case).**  If the finite abelian group `C` acts
`𝔽_p`-linearly and irreducibly (`M` is simple over `𝔽_p[C]`) on the finite module `M`,
then `M` is a field and `C` acts by multiplication: there is a `SingerFieldData`.

The construction: a simple module over the *commutative* ring `R = 𝔽_p[C]` is `R ⧸ I`
for a maximal ideal `I` (`isSimpleModule_iff_quot_maximal`), and `R ⧸ I` is a field
because `R` is commutative (`Ideal.Quotient.field`).  Under the additive identification
`M ≃+ R ⧸ I`, the action of `MonoidAlgebra.of _ _ c` is multiplication by the unit
`mk (of c)`. -/
theorem nonempty_singerFieldData [Finite M]
    [IsSimpleModule (MonoidAlgebra (ZMod p) C) M] :
    Nonempty (SingerFieldData (p := p) (C := C) (M := M)) := by
  classical
  obtain ⟨I, hImax, ⟨lequiv⟩⟩ :=
    (isSimpleModule_iff_quot_maximal (R := MonoidAlgebra (ZMod p) C) (M := M)).mp ‹_›
  have : I.IsMaximal := hImax
  let : Field (MonoidAlgebra (ZMod p) C ⧸ I) := Ideal.Quotient.field I
  have : Finite (MonoidAlgebra (ZMod p) C ⧸ I) := Finite.of_equiv _ lequiv.toEquiv
  let : Fintype (MonoidAlgebra (ZMod p) C ⧸ I) := Fintype.ofFinite _
  refine ⟨{
    K := MonoidAlgebra (ZMod p) C ⧸ I
    e := lequiv.toAddEquiv
    μ := (Units.map
            (Ideal.Quotient.mk I : MonoidAlgebra (ZMod p) C →+* _).toMonoidHom).comp
          (MonoidAlgebra.of (ZMod p) C).toHomUnits
    compat := ?_ }⟩
  intro c m
  change lequiv (MonoidAlgebra.of (ZMod p) C c • m) = _
  rw [map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  rfl

/-- If `a ∣ b` then `p^a - 1 ∣ p^b - 1` (a divisor of exponents lifts to a divisor of
`p^· - 1`).  Derived from `gcd(p^a-1, p^b-1) = p^{gcd a b}-1` with `gcd a b = a`. -/
theorem pow_sub_one_dvd_of_dvd {p a b : ℕ} (h : a ∣ b) : p ^ a - 1 ∣ p ^ b - 1 := by
  have hg : Nat.gcd (p ^ a - 1) (p ^ b - 1) = p ^ a - 1 := by
    rw [Nat.pow_sub_one_gcd_pow_sub_one, Nat.gcd_eq_left h]
  rw [← hg]
  exact Nat.gcd_dvd_right _ _

/-- A prime `q` does not divide `(q-1)!`. -/
theorem not_dvd_factorial_pred {q : ℕ} (hq : q.Prime) : ¬ q ∣ (q - 1).factorial := by
  rw [Nat.Prime.dvd_factorial hq]
  have := hq.two_le
  omega

section Irreducibility

variable {p : ℕ} [Fact p.Prime] {C M : Type u}
  [CommGroup C] [IsCyclic C] [Finite C]
  [AddCommGroup M] [Module (MonoidAlgebra (ZMod p) C) M] [Finite M]

omit [IsCyclic C] in
/-- **Singer irreducibility, abelian form.**  A faithful action of an abelian group `C` of order
`(p^q-1)/(p-1)` on an `F_p`-module `M` of order `p^q` (`q` an *odd* prime) is irreducible —
**without assuming `C` cyclic**.  This is the input that lets one *deduce* `C` cyclic (via the
Singer embedding), rather than assuming it (Peterfalvi (13.2.a) `U`/`V`-cyclic).

The cyclic proof uses the generator only to derive `card C ∣ N` from `g^N = 1`.  Here we instead
take a **primitive prime divisor** `r` of `p^q - 1` dividing `card C = ∑_{i<q} p^i`
(`exists_prime_orderOf_eq`), a Cauchy element `a` of order `r`, and the same fixed-point argument:
`a^N = 1`, so `r ∣ N = p^{(q-1)!} - 1`, i.e. `q = orderOf (p : ZMod r) ∣ (q-1)!`, contradicting
Wilson (`not_dvd_factorial_pred`). -/
theorem _root_.solution {q : ℕ} (hq : q.Prime) (hqodd : Odd q)
    [NeZero (Nat.card C : ZMod p)]
    (hcardM : Nat.card M = p ^ q)
    (hcardC : Nat.card C = (p ^ q - 1) / (p - 1))
    (hfaith : ∀ c : C, (∀ x : M, MonoidAlgebra.of (ZMod p) C c • x = x) → c = 1) :
    IsSimpleModule (MonoidAlgebra (ZMod p) C) M := by
  classical
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have hq2 : 2 ≤ q := hq.two_le
  have hq2ne : q ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hqodd
  have hMpos : 0 < Nat.card M := by rw [hcardM]; positivity
  have : IsSemisimpleModule (MonoidAlgebra (ZMod p) C) M := inferInstance
  have : Nontrivial M := by
    have hp2q : 2 ≤ p ^ q := le_trans hp2 (Nat.le_self_pow hq.pos.ne' p)
    have : 1 < Nat.card M := by rw [hcardM]; omega
    exact (Finite.one_lt_card_iff_nontrivial).mp this
  by_contra hns
  obtain ⟨s, _hindep, hsup, hsimple⟩ :=
    IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top (MonoidAlgebra (ZMod p) C) M
  set D := (q - 1).factorial with hDdef
  set N := p ^ D - 1 with hNdef
  -- For **any** `c`, `c^N` fixes every simple constituent `m ∈ s`.
  have hfix : ∀ (c : C), ∀ m ∈ s, ∀ x : M, x ∈ m →
      MonoidAlgebra.of (ZMod p) C (c ^ N) • x = x := by
    intro c m hm x hxm
    have hsm : IsSimpleModule (MonoidAlgebra (ZMod p) C) ↥m := hsimple m hm
    have : Fintype ↥m := Fintype.ofFinite _
    obtain ⟨data⟩ := nonempty_singerFieldData (p := p) (C := C) (M := ↥m)
    have hmdvd : Nat.card ↥m ∣ Nat.card M :=
      AddSubgroup.card_addSubgroup_dvd_card m.toAddSubgroup
    obtain ⟨d, hdq, hmcard⟩ := (Nat.dvd_prime_pow (Fact.out (p := p.Prime))).mp (hcardM ▸ hmdvd)
    have hmne : m ≠ ⊤ := by
      rintro rfl
      exact hns (IsSimpleModule.congr Submodule.topEquiv.symm)
    have hcard_ne : Nat.card ↥m ≠ Nat.card M := by
      intro heq
      apply hmne
      have hAtop : m.toAddSubgroup = ⊤ := AddSubgroup.eq_top_of_card_eq m.toAddSubgroup heq
      rwa [Submodule.toAddSubgroup_eq_top] at hAtop
    have hmlt : Nat.card ↥m < Nat.card M :=
      lt_of_le_of_ne (Nat.le_of_dvd hMpos hmdvd) hcard_ne
    have hdltq : d < q := by
      rw [hmcard, hcardM] at hmlt
      exact (Nat.pow_lt_pow_iff_right (by omega : 1 < p)).mp hmlt
    have hd1 : 1 ≤ d := by
      have h2 : 2 ≤ Nat.card ↥m :=
        (Finite.one_lt_card_iff_nontrivial).mpr
          (IsSimpleModule.nontrivial (MonoidAlgebra (ZMod p) C) ↥m)
      rcases Nat.eq_zero_or_pos d with h0 | h
      · rw [h0, pow_zero] at hmcard; omega
      · exact h
    have hdD : d ∣ D := Nat.dvd_factorial hd1 (by omega)
    have hKcard : Fintype.card data.K = p ^ d := by
      rw [data.card_K_eq, ← Nat.card_eq_fintype_card, hmcard]
    have hμpow : (data.μ c) ^ (p ^ d - 1) = 1 := by
      have hu : (data.μ c) ^ (Fintype.card data.Kˣ) = 1 := pow_card_eq_one
      rwa [Fintype.card_units, hKcard] at hu
    have hμN : (data.μ c) ^ N = 1 := by
      obtain ⟨k, hk⟩ := pow_sub_one_dvd_of_dvd (p := p) hdD
      rw [hNdef, hk, pow_mul, hμpow, one_pow]
    have hcompat := data.compat (c ^ N) ⟨x, hxm⟩
    have hμcoe : ((data.μ (c ^ N) : data.K)) = 1 := by
      rw [map_pow, hμN, Units.val_one]
    rw [hμcoe, one_mul] at hcompat
    have hfixsub : MonoidAlgebra.of (ZMod p) C (c ^ N) • (⟨x, hxm⟩ : ↥m) = ⟨x, hxm⟩ :=
      data.e.injective hcompat
    simpa using congrArg (Subtype.val) hfixsub
  have hfixM : ∀ (c : C), ∀ x : M, MonoidAlgebra.of (ZMod p) C (c ^ N) • x = x := by
    intro c
    have hle : (⊤ : Submodule (MonoidAlgebra (ZMod p) C) M) ≤
        LinearMap.eqLocus
          (LinearMap.lsmul (MonoidAlgebra (ZMod p) C) M
            (MonoidAlgebra.of (ZMod p) C (c ^ N))) LinearMap.id := by
      rw [← hsup]
      refine sSup_le fun m hm => ?_
      intro x hx
      simpa [LinearMap.mem_eqLocus] using hfix c m hm x hx
    intro x
    have hx : x ∈ LinearMap.eqLocus _ _ := hle Submodule.mem_top
    simpa [LinearMap.mem_eqLocus] using hx
  -- A **primitive prime divisor** `r ∣ card C` with `orderOf (p : ZMod r) = q`.
  obtain ⟨r, hr, hrn, hord⟩ := OddOrder.NumberTheory.exists_prime_orderOf_eq hp2 hq hq2ne
  have : Fact r.Prime := ⟨hr⟩
  have : Fintype C := Fintype.ofFinite _
  have hrdvdC : r ∣ Fintype.card C := by
    rw [← Nat.card_eq_fintype_card, hcardC, ← Nat.geomSum_eq hp2 q]; exact hrn
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card r hrdvdC
  -- `a^N = 1` (faithful), so `r = orderOf a ∣ N`; but `r ∤ N` by Wilson.
  have haN : a ^ N = 1 := hfaith _ (hfixM a)
  have hrN : r ∣ N := ha ▸ orderOf_dvd_of_pow_eq_one haN
  have hnotdvd : ¬ r ∣ N := by
    rw [hNdef]
    intro hdvd
    have hpD1 : (p : ZMod r) ^ D = 1 := by
      have h0 : ((p ^ D - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
      have hle1 : 1 ≤ p ^ D := Nat.one_le_pow _ _ (by omega)
      push_cast [Nat.cast_sub hle1] at h0
      exact sub_eq_zero.mp h0
    have hqdvdD : q ∣ D := by
      rw [← hord]; exact orderOf_dvd_of_pow_eq_one hpD1
    rw [hDdef] at hqdvdD
    exact not_dvd_factorial_pred hq hqdvdD
  exact hnotdvd hrN

end Irreducibility

end OddOrder.RepresentationTheory
