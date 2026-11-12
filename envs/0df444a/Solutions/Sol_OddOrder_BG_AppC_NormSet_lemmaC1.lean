-- Prove2me | solution 1 for OddOrder.BG.AppC.NormSet.lemmaC1
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T04:47:52.202393+00:00
-- url     : https://prove2.me/submissions/ffcfc4b7-3a39-4ff5-b493-a2c082e618e4

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppC_NormSetBasic.lean
--   OddOrder/BG/AppC_NormSet.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_NormSetBasic
import Definitions.Def_OddOrder_BG_AppC_NormSet
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Ring.AddAut
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.ZMod

-- ===== OddOrder/BG/AppC_NormSetBasic.lean =====
namespace OddOrder.BG.AppC.NormSet

open scoped Pointwise

open Polynomial Finset

variable (p q : ℕ)

/-- The norm is multiplicative (it is a product of multiplicative maps). -/
lemma normN_mul [Fact p.Prime] (x y : GaloisField p q) :
    normN p q (x * y) = normN p q x * normN p q y := by
  simp only [normN, mul_pow, Finset.prod_mul_distrib]

/-- If `E` has at least two elements then it contains an element `≠ 1` — the
`a ∈ E^#` with which the Lemma C.1 argument begins. -/
lemma exists_mem_normSetE_ne_one [Fact p.Prime]
    (hcard : 2 ≤ (normSetE p q).ncard) :
    ∃ a ∈ normSetE p q, a ≠ 1 := by
  by_contra h
  push Not at h
  have hsub : normSetE p q ⊆ {1} := fun a ha => h a ha
  have hle : (normSetE p q).ncard ≤ ({1} : Set (GaloisField p q)).ncard :=
    Set.ncard_le_ncard hsub (Set.finite_singleton 1)
  rw [Set.ncard_singleton] at hle
  omega

end OddOrder.BG.AppC.NormSet

-- ===== OddOrder/BG/AppC_NormSet.lean =====
namespace OddOrder.BG.AppC.NormSet

open scoped Pointwise

open Polynomial Finset

variable (p q : ℕ)

/-- For `a ∈ E`, `2 - a ≠ 0` (its norm is `1 ≠ 0`), so `(2-a)⁻¹` is genuine. -/
lemma two_sub_ne_zero_of_mem_normSetE [Fact p.Prime] (hq : 0 < q) {a : GaloisField p q}
    (ha : a ∈ normSetE p q) : (2 : GaloisField p q) - a ≠ 0 := by
  intro h
  have := ha.2
  rw [h, normN_zero p q hq] at this
  exact zero_ne_one this

lemma dSeq_one [Fact p.Prime] (a : GaloisField p q) : dSeq p q a 1 = 2 - a := by
  simp only [dSeq, Nat.cast_one, one_mul]; ring

/-- The three-term recurrence `d_{k+2} = 2·d_{k+1} - d_k`. -/
lemma dSeq_recurrence [Fact p.Prime] (a : GaloisField p q) (k : ℕ) :
    dSeq p q a (k + 2) = 2 * dSeq p q a (k + 1) - dSeq p q a k := by
  simp only [dSeq]
  push_cast
  ring

lemma tauIter_succ [Fact p.Prime] (a : GaloisField p q) (k : ℕ) :
    tauIter p q a (k + 1) = (2 - tauIter p q a k)⁻¹ := rfl

/-- Every iterate `aₖ` lies in `E` (using `E = E⁻¹`). -/
lemma tauIter_mem [Fact p.Prime] {a : GaloisField p q}
    (hEinv : normSetE p q = (normSetE p q)⁻¹) (ha : a ∈ normSetE p q) :
    ∀ k, tauIter p q a k ∈ normSetE p q := by
  intro k
  induction k with
  | zero => simpa using ha
  | succ k ih =>
    rw [tauIter_succ]
    have h2 : (2 - tauIter p q a k) ∈ normSetE p q := two_sub_mem_normSetE p q ih
    rw [hEinv] at h2
    rwa [Set.mem_inv] at h2

/-- Closed form of the iterate: `a_{k+1} = d_k / d_{k+1}`, with `d_{k+1} ≠ 0`. -/
lemma tauIter_eq_dSeq_div [Fact p.Prime] (hq : 0 < q) {a : GaloisField p q}
    (hEinv : normSetE p q = (normSetE p q)⁻¹) (ha : a ∈ normSetE p q) :
    ∀ k, dSeq p q a (k + 1) ≠ 0 ∧
      tauIter p q a (k + 1) = dSeq p q a k / dSeq p q a (k + 1) := by
  intro k
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [dSeq_one]; exact two_sub_ne_zero_of_mem_normSetE p q hq ha
    · rw [tauIter_succ, tauIter_zero, dSeq_zero, dSeq_one, one_div]
  | succ k ih =>
    obtain ⟨hd1, htau⟩ := ih
    have hmem : tauIter p q a (k + 1) ∈ normSetE p q := tauIter_mem p q hEinv ha (k + 1)
    have hne : (2 : GaloisField p q) - tauIter p q a (k + 1) ≠ 0 :=
      two_sub_ne_zero_of_mem_normSetE p q hq hmem
    have hkey : (2 : GaloisField p q) - tauIter p q a (k + 1)
        = dSeq p q a (k + 2) / dSeq p q a (k + 1) := by
      rw [htau, dSeq_recurrence]
      field_simp
    refine ⟨?_, ?_⟩
    · intro hcontra
      apply hne
      rw [hkey, hcontra, zero_div]
    · rw [tauIter_succ, hkey, inv_div]

/-- The multiplied form `a_{k+1} · d_{k+1} = d_k`. -/
lemma tauIter_mul_dSeq [Fact p.Prime] (hq : 0 < q) {a : GaloisField p q}
    (hEinv : normSetE p q = (normSetE p q)⁻¹) (ha : a ∈ normSetE p q) (k : ℕ) :
    tauIter p q a (k + 1) * dSeq p q a (k + 1) = dSeq p q a k := by
  obtain ⟨hd1, htau⟩ := tauIter_eq_dSeq_div p q hq hEinv ha k
  rw [htau, div_mul_cancel₀ _ hd1]

/-- **Key telescoping output**: `N(d_k) = 1` for every `k`, since each
`a_{k+1} = d_k/d_{k+1} ∈ E` has norm `1` and the norm is multiplicative. -/
lemma normN_dSeq_eq_one [Fact p.Prime] (hq : 0 < q) {a : GaloisField p q}
    (hEinv : normSetE p q = (normSetE p q)⁻¹) (ha : a ∈ normSetE p q) :
    ∀ k, normN p q (dSeq p q a k) = 1 := by
  intro k
  induction k with
  | zero => rw [dSeq_zero]; exact normN_one p q
  | succ k ih =>
    have hmul := tauIter_mul_dSeq p q hq hEinv ha k
    have h1 : normN p q (tauIter p q a (k + 1)) = 1 := (tauIter_mem p q hEinv ha (k + 1)).1
    have hcong := congrArg (normN p q) hmul
    rw [normN_mul, h1, one_mul] at hcong
    rw [hcong]; exact ih

/-- Elements of the prime field `𝔽_p ⊆ 𝔽_{p^q}` are fixed by every power of the
Frobenius: `(k : 𝔽_{p^q})^{p^i} = (k : 𝔽_{p^q})`. -/
lemma natCast_pow_pPow [Fact p.Prime] (k i : ℕ) :
    ((k : GaloisField p q)) ^ (p ^ i) = (k : GaloisField p q) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, pow_mul, ih]
    have hk : ((k : ℕ) : GaloisField p q)
        = algebraMap (ZMod p) (GaloisField p q) (k : ZMod p) := (map_natCast _ k).symm
    rw [hk, ← map_pow, ZMod.pow_card]

/-- **BG Appendix C, Lemma C.1** (mmd L4911): if the norm set is closed under
inversion and has at least two elements, then `p ≤ q`.

Proof: for `a ∈ E^#`, the map `τ(a) = 1/(2-a)`
sends `E` to `E` (using `E = E⁻¹`), and `∏_{j≤k} τ^j(a) = 1/((k+1)-ka)`
telescopes, giving `N((1-a)k+1) = 1` for all `k ∈ 𝔽_p`. The degree-`q` polynomial
`∏_{i<q} ((1-a)^{p^i} X + 1) - 1` (leading coefficient `N(1-a) ≠ 0`) then has all
`p` elements of `𝔽_p` as roots, so `p ≤ q`. -/
theorem _root_.solution [Fact p.Prime] (hq : q.Prime)
    (hEinv : normSetE p q = (normSetE p q)⁻¹)
    (hcard : 2 ≤ (normSetE p q).ncard) :
    p ≤ q := by
  classical
  -- Start from `a ∈ E^#`.
  obtain ⟨a, ha, hane⟩ := exists_mem_normSetE_ne_one p q hcard
  have h1a : (1 : GaloisField p q) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hane)
  have : CharP (GaloisField p q) p := by
    rw [← Algebra.charP_iff (ZMod p) (GaloisField p q) p]; exact ZMod.charP p
  -- The norm polynomial `P(X) = ∏_{i<q} ((1-a)^{p^i} X + 1) - 1`.
  set P : (GaloisField p q)[X] :=
    (∏ i ∈ Finset.range q, (C ((1 - a) ^ (p ^ i)) * X + C 1)) - C 1 with hP_def
  have hcne : ∀ i, ((1 - a) ^ (p ^ i) : GaloisField p q) ≠ 0 := fun i => pow_ne_zero _ h1a
  have hfac_ne : ∀ i ∈ Finset.range q,
      (C ((1 - a) ^ (p ^ i)) * X + C 1 : (GaloisField p q)[X]) ≠ 0 := by
    intro i _ hz
    have hd1 := natDegree_linear (a := (1 - a) ^ (p ^ i)) (b := (1 : GaloisField p q)) (hcne i)
    rw [hz, natDegree_zero] at hd1
    exact one_ne_zero hd1.symm
  -- `P` has degree exactly `q`.
  have hdeg : P.natDegree = q := by
    rw [hP_def, natDegree_sub_C, natDegree_prod _ _ hfac_ne,
      Finset.sum_congr rfl (fun i _ => natDegree_linear (b := (1 : GaloisField p q)) (hcne i)),
      Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  -- Hence `P ≠ 0`.
  have hPne : P ≠ 0 := by
    intro hz
    have h0 := hdeg
    rw [hz, natDegree_zero] at h0
    have := hq.pos
    omega
  -- Every element of `𝔽_p` is a root of `P`.
  have heval : ∀ k : ℕ, P.eval ((k : ℕ) : GaloisField p q) = 0 := by
    intro k
    rw [hP_def, eval_sub, eval_C, eval_prod]
    have hprod : ∏ i ∈ Finset.range q,
        (C ((1 - a) ^ (p ^ i)) * X + C 1 : (GaloisField p q)[X]).eval ((k : ℕ) : GaloisField p q)
          = 1 := by
      have hstep : ∀ i ∈ Finset.range q,
          (C ((1 - a) ^ (p ^ i)) * X + C 1 : (GaloisField p q)[X]).eval
            ((k : ℕ) : GaloisField p q)
            = ((1 - a) * ((k : ℕ) : GaloisField p q) + 1) ^ (p ^ i) := by
        intro i _
        simp only [eval_add, eval_mul, eval_C, eval_X]
        rw [add_pow_char_pow, mul_pow, one_pow, natCast_pow_pPow]
      rw [Finset.prod_congr rfl hstep, ← normN]
      have hd : (1 - a) * ((k : ℕ) : GaloisField p q) + 1 = dSeq p q a k := by
        rw [dSeq]; ring
      rw [hd]
      exact normN_dSeq_eq_one p q hq.pos hEinv ha k
    rw [hprod]; ring
  -- `𝔽_p` is a `p`-element finset of roots, and `#roots ≤ deg P = q`.
  have hinj : Set.InjOn ((Nat.cast : ℕ → GaloisField p q))
      (↑(Finset.range p)) := by
    rw [Finset.coe_range]; exact CharP.natCast_injOn_Iio (GaloisField p q) p
  have hScard : ((Finset.range p).image ((Nat.cast : ℕ → GaloisField p q))).card = p := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hSsub : (Finset.range p).image ((Nat.cast : ℕ → GaloisField p q))
      ⊆ P.roots.toFinset := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨k, _, rfl⟩ := hx
    rw [Multiset.mem_toFinset, mem_roots']
    exact ⟨hPne, heval k⟩
  calc p = ((Finset.range p).image ((Nat.cast : ℕ → GaloisField p q))).card := hScard.symm
    _ ≤ P.roots.toFinset.card := Finset.card_le_card hSsub
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' P
    _ = q := hdeg

end OddOrder.BG.AppC.NormSet
