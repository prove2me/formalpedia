-- Prove2me | solution 1 for PrimePairSieve_squarefree_primitive_fourier_energy
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:20:31.912548+00:00
-- url     : https://prove2.me/submissions/70bc5017-e70d-487c-b41d-a3a19e3ee408

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option maxHeartbeats 100000
open scoped BigOperators ComplexConjugate

namespace PrimitiveSieve

lemma conj_char {p : ℕ} [NeZero p] (χ : AddChar (ZMod p) ℂ) (x : ZMod p) :
    conj (χ x) = χ (-x) := by
  exact (AddChar.map_neg_eq_conj χ x).symm

lemma char_pair {p : ℕ} [NeZero p] (χ : AddChar (ZMod p) ℂ) (k x y : ZMod p) :
    χ (k*x) * conj (χ (k*y)) =
      χ (k*(x-y)) := by
  rw [conj_char, ← AddChar.map_add_eq_mul]
  congr 1
  ring

lemma nonzero_char_sum {p : ℕ} [NeZero p] (χ : AddChar (ZMod p) ℂ) (hχ : Function.Injective χ) (x : ZMod p) :
    (∑ k : {k : ZMod p // k ≠ 0}, χ (k.val*x)) =
      if x = 0 then (p : ℂ)-1 else -1 := by
  classical
  have hfull : (∑ k : ZMod p, χ (k*x)) =
      if x = 0 then (p : ℂ) else 0 := by
    by_cases hx : x = 0
    · simp [hx, ZMod.card]
    · have hn : χ.mulShift x ≠ 0 := by
        intro he
        have hh := congrArg (fun f : AddChar (ZMod p) ℂ => f 1) he
        have hz : χ x = χ 0 := by simpa using hh
        exact hx (hχ hz)
      simpa only [if_neg hx, AddChar.mulShift_apply, mul_comm] using
        (AddChar.sum_eq_zero_iff_ne_zero).mpr hn
  have hs : (∑ k : {k : ZMod p // k ≠ 0}, χ (k.val*x)) + 1 =
      ∑ k : ZMod p, χ (k*x) := by
    rw [← Finset.sum_subtype (p := fun k : ZMod p => k ≠ 0)
      (Finset.univ.erase (0 : ZMod p)) (by simp) (fun k => χ (k*x))]
    simpa using Finset.sum_erase_add (Finset.univ) (fun k : ZMod p =>
      χ (k*x)) (Finset.mem_univ (0 : ZMod p))
  rw [hfull] at hs
  split_ifs at hs ⊢ <;> linear_combination hs

noncomputable def localWitness {p : ℕ} [NeZero p]
    (χ : AddChar (ZMod p) ℂ) (Ω : Finset (ZMod p)) (k : {k : ZMod p // k ≠ 0}) : ℂ :=
  ∑ a ∈ Ω, conj (χ (k.val*a))

lemma local_evaluation {p : ℕ} [NeZero p] (χ : AddChar (ZMod p) ℂ) (hχ : Function.Injective χ) (Ω : Finset (ZMod p))
    (x : ZMod p) (hx : x ∉ Ω) :
    (∑ k : {k : ZMod p // k ≠ 0}, localWitness χ Ω k * χ (k.val*x)) =
      -(Ω.card : ℂ) := by
  classical
  simp only [localWitness, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm (a : ZMod p) (ha : a ∈ Ω) :
      (∑ k : {k : ZMod p // k ≠ 0},
        conj (χ (k.val*a)) * χ (k.val*x)) = -1 := by
    simp_rw [mul_comm (conj _), char_pair]
    rw [nonzero_char_sum χ hχ, if_neg]
    exact sub_ne_zero.mpr (fun h => hx (h ▸ ha))
  rw [Finset.sum_congr rfl (fun a ha => hterm a ha)]
  simp

lemma local_energy {p : ℕ} [NeZero p] (χ : AddChar (ZMod p) ℂ) (hχ : Function.Injective χ) (Ω : Finset (ZMod p)) :
    (∑ k : {k : ZMod p // k ≠ 0}, ‖localWitness χ Ω k‖^2) =
      (Ω.card : ℝ) * ((p : ℝ)-Ω.card) := by
  classical
  have hgram (k : {k : ZMod p // k ≠ 0}) :
      (‖localWitness χ Ω k‖ : ℂ)^2 =
        ∑ a ∈ Ω, ∑ b ∈ Ω, χ (k.val*(a-b)) := by
    rw [← Complex.mul_conj']
    simp only [localWitness, map_sum, starRingEnd_self_apply, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [mul_comm, char_pair]
  have hrow (a : ZMod p) (ha : a ∈ Ω) :
      (∑ b ∈ Ω, if a-b=0 then (p : ℂ)-1 else -1) = (p : ℂ)-Ω.card := by
    have ht (b : ZMod p) :
        (if a-b=0 then (p : ℂ)-1 else -1) = (if a=b then (p : ℂ) else 0)-1 := by
      simp only [sub_eq_zero]
      split_ifs <;> ring
    simp_rw [ht]
    simp [Finset.sum_sub_distrib, ha]
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_pow, hgram,
    Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_natCast]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := Ω), nonzero_char_sum χ hχ]
  rw [Finset.sum_congr rfl (fun a ha => hrow a ha)]
  simp
  ring

noncomputable def productChar {ι : Type} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] (χ : ∀ i, AddChar (ZMod (p i)) ℂ)
    (k : ∀ i, {k : ZMod (p i) // k ≠ 0}) (x : ∀ i, ZMod (p i)) : ℂ :=
  ∏ i, χ i ((k i).val*x i)

noncomputable def productWitness {ι : Type} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] (χ : ∀ i, AddChar (ZMod (p i)) ℂ) (Ω : ∀ i, Finset (ZMod (p i)))
    (k : ∀ i, {k : ZMod (p i) // k ≠ 0}) : ℂ :=
  ∏ i, localWitness (χ i) (Ω i) (k i)

lemma product_evaluation {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] (χ : ∀ i, AddChar (ZMod (p i)) ℂ) (Ω : ∀ i, Finset (ZMod (p i))) (hχ : ∀ i, Function.Injective (χ i))
    (x : ∀ i, ZMod (p i)) (hx : ∀ i, x i ∉ Ω i) :
    (∑ k : ∀ i, {k : ZMod (p i) // k ≠ 0},
      productWitness p χ Ω k * productChar p χ k x) = ∏ i, -((Ω i).card : ℂ) := by
  simp only [productWitness, productChar, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (k : {k : ZMod (p i) // k ≠ 0}) =>
    localWitness (χ i) (Ω i) k * χ i (k.val*x i))]
  exact Finset.prod_congr rfl (fun i hi => local_evaluation (χ i) (hχ i) (Ω i) (x i) (hx i))

lemma product_energy {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] (χ : ∀ i, AddChar (ZMod (p i)) ℂ) (Ω : ∀ i, Finset (ZMod (p i))) (hχ : ∀ i, Function.Injective (χ i)) :
    (∑ k : ∀ i, {k : ZMod (p i) // k ≠ 0}, ‖productWitness p χ Ω k‖^2) =
      (∏ i, ((Ω i).card : ℝ)) * ∏ i, ((p i : ℝ)-(Ω i).card) := by
  simp only [productWitness, norm_prod, ← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun i (k : {k : ZMod (p i) // k ≠ 0}) =>
    ‖localWitness (χ i) (Ω i) k‖^2)]
  simp_rw [local_energy _ (hχ _)]
  rw [Finset.prod_mul_distrib]

/-- The primitive-coordinate Fourier energy of points avoiding prescribed residues.
The point map need not be injective, so intervals longer than the product modulus are allowed. -/
theorem excluded_product_energy {ι α : Type} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] (χ : ∀ i, AddChar (ZMod (p i)) ℂ) (Ω : ∀ i, Finset (ZMod (p i))) (hχ : ∀ i, Function.Injective (χ i))
    (hpos : ∀ i, 0 < (Ω i).card) (hlt : ∀ i, (Ω i).card < p i)
    (A : Finset α) (x : α → ∀ i, ZMod (p i))
    (havoid : ∀ n ∈ A, ∀ i, x n i ∉ Ω i) :
    (∏ i, ((Ω i).card : ℝ) / ((p i : ℝ)-(Ω i).card)) * (A.card : ℝ)^2 ≤
      ∑ k : ∀ i, {k : ZMod (p i) // k ≠ 0}, ‖∑ n ∈ A, productChar p χ k (x n)‖^2 := by
  classical
  let R : ℝ := ∏ i, ((Ω i).card : ℝ)
  let V : ℝ := ∏ i, ((p i : ℝ)-(Ω i).card)
  let S (k : ∀ i, {k : ZMod (p i) // k ≠ 0}) : ℂ := ∑ n ∈ A, productChar p χ k (x n)
  have hR : 0 < R := Finset.prod_pos (fun i hi => by exact_mod_cast hpos i)
  have hV : 0 < V := Finset.prod_pos (fun i hi => sub_pos.mpr (by exact_mod_cast hlt i))
  have hpair : (∑ k, productWitness p χ Ω k * S k) =
      (A.card : ℂ) * ∏ i, -((Ω i).card : ℂ) := by
    simp only [S, Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun n hn => product_evaluation p χ Ω hχ (x n) (havoid n hn))]
    simp
  have hn : ‖∑ k, productWitness p χ Ω k * S k‖ = (A.card : ℝ)*R := by
    rw [hpair, norm_mul, norm_prod]
    simp [R, Complex.norm_natCast]
  have htri : ‖∑ k, productWitness p χ Ω k * S k‖ ≤
      ∑ k, ‖productWitness p χ Ω k‖ * ‖S k‖ := by
    simpa only [norm_mul] using norm_sum_le Finset.univ (fun k => productWitness p χ Ω k * S k)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun k => ‖productWitness p χ Ω k‖) (fun k => ‖S k‖)
  rw [hn] at hsq
  rw [product_energy p χ Ω hχ] at hcs
  change (_)^2 ≤ (R*V)*(∑ k, ‖S k‖^2) at hcs
  have hbound : (A.card : ℝ)^2 * R ≤ V * (∑ k, ‖S k‖^2) := by
    apply (mul_le_mul_iff_right₀ hR).mp
    nlinarith [hsq.trans hcs]
  rw [Finset.prod_div_distrib]
  change (R/V)*(A.card : ℝ)^2 ≤ _
  rw [div_mul_eq_mul_div, div_le_iff₀ hV]
  simpa only [mul_comm] using hbound

end PrimitiveSieve


set_option autoImplicit false
set_option maxHeartbeats 100000
open scoped BigOperators

namespace PrimitiveSieve

lemma exists_unit_shift {q : ℕ} [NeZero q]
    (ψ φ : AddChar (ZMod q) ℂ) (hψ : Function.Injective ψ)
    (hφ : ∀ a : ZMod q, (∀ b, φ (a*b) = 1) → a = 0) :
    ∃ u : (ZMod q)ˣ, φ = ψ.mulShift u.val := by
  classical
  have hinj : Function.Injective ψ.mulShift := by
    intro a b hab
    apply hψ
    simpa using congrArg (fun f : AddChar (ZMod q) ℂ => f 1) hab
  have hcard : Fintype.card (ZMod q) = Fintype.card (AddChar (ZMod q) ℂ) :=
    Nat.le_antisymm (Fintype.card_le_of_injective _ hinj) (AddChar.card_addChar_le (ZMod q) ℂ)
  have hsurj := ((Fintype.bijective_iff_injective_and_card ψ.mulShift).mpr ⟨hinj,hcard⟩).surjective
  obtain ⟨t, ht⟩ := hsurj φ
  have hu : IsUnit t := by
    rw [isUnit_iff_mem_nonZeroDivisors_of_finite, mem_nonZeroDivisors_iff_right]
    intro a ha
    apply hφ a
    intro b
    rw [← ht, AddChar.mulShift_apply]
    have hz : t*(a*b) = 0 := by rw [mul_comm t, mul_assoc, mul_comm b, ← mul_assoc, ha, zero_mul]
    rw [hz, AddChar.map_zero_eq_one]
  obtain ⟨u, hu⟩ := hu
  exact ⟨u, by rw [hu]; exact ht.symm⟩

noncomputable def crtChar {ι : Type} [Fintype ι] {q : ℕ}
    (p : ι → ℕ) (e : ZMod q ≃+* ∀ i, ZMod (p i))
    (χ : ∀ i, AddChar (ZMod (p i)) ℂ) : AddChar (ZMod q) ℂ where
  toFun a := ∏ i, χ i (e a i)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp [AddChar.map_add_eq_mul, Finset.prod_mul_distrib]

lemma crtChar_nondegenerate {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ}
    (p : ι → ℕ) (e : ZMod q ≃+* ∀ i, ZMod (p i))
    (χ : ∀ i, AddChar (ZMod (p i)) ℂ) (hχ : ∀ i, Function.Injective (χ i))
    (a : ZMod q) (ha : ∀ b, crtChar p e χ (a*b) = 1) : a = 0 := by
  apply e.injective
  ext i
  rw [map_zero]
  change e a i = 0
  apply hχ i
  rw [AddChar.map_zero_eq_one]
  have h := ha (e.symm (Pi.single i 1))
  change (∏ j, χ j (e (a * e.symm (Pi.single i 1)) j)) = 1 at h
  simp only [map_mul, e.apply_symm_apply, Pi.mul_apply] at h
  have hf (j : ι) : χ j (e a j * (Pi.single i (1 : ZMod (p i)) : ∀ j, ZMod (p j)) j) =
      if j = i then χ i (e a i) else 1 := by
    by_cases hj : j = i
    · subst j; simp
    · simp [Pi.single_eq_of_ne hj, hj]
  simp_rw [hf] at h
  simpa using h

noncomputable def frequencyEquiv {ι : Type} [Fintype ι] {q : ℕ}
    (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (e : ZMod q ≃+* ∀ i, ZMod (p i)) :
    (ZMod q)ˣ ≃ (∀ i, {k : ZMod (p i) // k ≠ 0}) :=
  (Units.mapEquiv e.toMulEquiv).toEquiv.trans
    (MulEquiv.piUnits.toEquiv.trans (Equiv.piCongrRight (fun i => unitsEquivNeZero)))

lemma frequencyEquiv_apply {ι : Type} [Fintype ι] {q : ℕ}
    (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (e : ZMod q ≃+* ∀ i, ZMod (p i)) (u : (ZMod q)ˣ) (i : ι) :
    (frequencyEquiv p e u i).val = e u.val i := rfl

theorem crt_primitive_energy_identity {ι α : Type} [Fintype ι] [DecidableEq ι]
    {q : ℕ} [NeZero q] (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (e : ZMod q ≃+* ∀ i, ZMod (p i))
    (ψ : AddChar (ZMod q) ℂ) (hψ : Function.Injective ψ)
    (χ : ∀ i, AddChar (ZMod (p i)) ℂ) (hχ : ∀ i, Function.Injective (χ i))
    (A : Finset α) (x : α → ZMod q) :
    (∑ k : ∀ i, {k : ZMod (p i) // k ≠ 0},
      ‖∑ n ∈ A, ∏ i, χ i ((k i).val * e (x n) i)‖^2) =
      ∑ u : (ZMod q)ˣ, ‖∑ n ∈ A, ψ (u.val*x n)‖^2 := by
  classical
  obtain ⟨t, ht⟩ := exists_unit_shift ψ (crtChar p e χ) hψ
    (crtChar_nondegenerate p e χ hχ)
  have hpoint (u : (ZMod q)ˣ) (n : α) :
      (∏ i, χ i ((frequencyEquiv p e u i).val * e (x n) i)) =
        ψ ((t*u).val * x n) := by
    simp only [frequencyEquiv_apply]
    have heval : (∏ i, χ i (e u.val i * e (x n) i)) =
        crtChar p e χ (u.val*x n) := by simp only [crtChar, AddChar.coe_mk, map_mul, Pi.mul_apply]
    rw [heval]
    rw [ht, AddChar.mulShift_apply, Units.val_mul, mul_assoc]
  calc
    _ = ∑ u : (ZMod q)ˣ, ‖∑ n ∈ A,
        ∏ i, χ i ((frequencyEquiv p e u i).val * e (x n) i)‖^2 :=
      (Fintype.sum_equiv (frequencyEquiv p e) _ _ (fun u => rfl)).symm
    _ = ∑ u : (ZMod q)ˣ, ‖∑ n ∈ A, ψ ((t*u).val*x n)‖^2 := by simp_rw [hpoint]
    _ = _ := Fintype.sum_bijective (fun u : (ZMod q)ˣ => t*u)
      (Group.mulLeft_bijective t) _ _ (fun u => rfl)

end PrimitiveSieve


set_option autoImplicit false
open scoped BigOperators

namespace PrimitiveSieve

noncomputable def pairForbidden (p d : ℕ) : Finset (ZMod p) := {0, -(d : ZMod p)}

lemma pairForbidden_card (p d : ℕ) :
    (pairForbidden p d).card = if p ∣ d then 1 else 2 := by
  classical
  by_cases h : p ∣ d
  · have hd : (d : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff d p).mpr h
    simp [pairForbidden, h, hd]
  · have hd : (d : ZMod p) ≠ 0 := fun he => h ((ZMod.natCast_eq_zero_iff d p).mp he)
    have he : (0 : ZMod p) ≠ -(d : ZMod p) := fun he => hd (neg_eq_zero.mp he.symm)
    simp [pairForbidden, h, Finset.card_pair he]

lemma pairForbidden_card_pos_lt (p d : ℕ) (hp : p.Prime) (hd : 2 ∣ d) :
    0 < (pairForbidden p d).card ∧ (pairForbidden p d).card < p := by
  rw [pairForbidden_card]
  by_cases h : p ∣ d
  · simp only [if_pos h]
    exact ⟨by decide, hp.one_lt⟩
  · have hne : p ≠ 2 := fun he => h (he ▸ hd)
    have hp2 := hp.two_le
    simp only [if_neg h]
    constructor <;> omega

lemma pairForbidden_avoided (p d n : ℕ) (h : ¬ p ∣ n*(n+d)) :
    (n : ZMod p) ∉ pairForbidden p d := by
  classical
  intro hn
  have hz : (n : ZMod p)*((n : ZMod p)+(d : ZMod p)) = 0 := by
    simp only [pairForbidden, Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with hn | hn
    · rw [hn, zero_mul]
    · rw [hn, neg_add_cancel, mul_zero]
  apply h
  apply (ZMod.natCast_eq_zero_iff (n*(n+d)) p).mp
  simpa only [Nat.cast_mul, Nat.cast_add] using hz

noncomputable def squarefreeCRT (q : ℕ) (hq : Squarefree q) :
    ZMod q ≃+* ∀ p : q.primeFactors, ZMod p.val := by
  classical
  have he : (∏ p : q.primeFactors, p.val) = q := by
    rw [Finset.prod_coe_sort q.primeFactors (fun p : ℕ => p)]
    exact Nat.prod_primeFactors_of_squarefree hq
  have hc : Pairwise (fun p r : q.primeFactors => Nat.Coprime p.val r.val) := by
    intro p r hpr
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors p.property)
      (Nat.prime_of_mem_primeFactors r.property)).mpr (fun he => hpr (Subtype.ext he))
  exact (ZMod.ringEquivCongr he.symm).trans (ZMod.prodEquivPi (fun p : q.primeFactors => p.val) hc)

end PrimitiveSieve

namespace PrimitiveSieve

theorem excluded_crt_energy {ι α : Type} [Fintype ι] [DecidableEq ι]
    {q : ℕ} [NeZero q] (p : ι → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (p i)]
    (e : ZMod q ≃+* ∀ i, ZMod (p i))
    (ψ : AddChar (ZMod q) ℂ) (hψ : Function.Injective ψ)
    (χ : ∀ i, AddChar (ZMod (p i)) ℂ) (hχ : ∀ i, Function.Injective (χ i))
    (Ω : ∀ i, Finset (ZMod (p i)))
    (hpos : ∀ i, 0 < (Ω i).card) (hlt : ∀ i, (Ω i).card < p i)
    (A : Finset α) (x : α → ZMod q) (ha : ∀ n ∈ A, ∀ i, e (x n) i ∉ Ω i) :
    (∏ i, ((Ω i).card : ℝ) / ((p i : ℝ)-(Ω i).card)) * (A.card : ℝ)^2 ≤
      ∑ u : (ZMod q)ˣ, ‖∑ n ∈ A, ψ (u.val*x n)‖^2 := by
  have h := excluded_product_energy p χ Ω hχ hpos hlt A (fun n => e (x n)) ha
  have hi := crt_primitive_energy_identity p e ψ hψ χ hχ A x
  change _ ≤ (∑ k : ∀ i, {k : ZMod (p i) // k ≠ 0},
    ‖∑ n ∈ A, ∏ i, χ i ((k i).val * e (x n) i)‖^2) at h
  rw [hi] at h
  exact h

end PrimitiveSieve
namespace PrimitiveSieve

theorem squarefree_pair_energy_generic
    (q : ℕ) [NeZero q] (d : ℕ) (hq : Squarefree q) (hd : 2 ∣ d)
    (A : Finset ℕ)
    (hA : ∀ n ∈ A, ∀ p ∈ q.primeFactors, ¬ p ∣ n*(n+d))
    (ψ : AddChar (ZMod q) ℂ) (hψ : Function.Injective ψ)
    (χ₀ : ∀ p : q.primeFactors, AddChar (ZMod p.val) ℂ)
    (hχ₀ : ∀ p, Function.Injective (χ₀ p)) :
    (∏ p ∈ q.primeFactors,
      if p ∣ d then 1 / ((p : ℝ)-1) else 2 / ((p : ℝ)-2)) * (A.card : ℝ)^2 ≤
      ∑ u : (ZMod q)ˣ, ‖∑ n ∈ A, ψ (u.val*(n : ZMod q))‖^2 := by
  classical
  let P := q.primeFactors
  let p : P → ℕ := fun i => i.val
  letI : ∀ i : P, Fact (p i).Prime := fun i => ⟨Nat.prime_of_mem_primeFactors i.property⟩
  letI : ∀ i : P, NeZero (p i) := fun i => ⟨(Nat.prime_of_mem_primeFactors i.property).ne_zero⟩
  let Ω (i : P) := pairForbidden (p i) d
  let e : ZMod q ≃+* ∀ i : P, ZMod (p i) := squarefreeCRT q hq
  let χ (i : P) : AddChar (ZMod (p i)) ℂ := χ₀ i
  have hχ : ∀ i, Function.Injective (χ i) := fun i => hχ₀ i
  have hp (i : P) := pairForbidden_card_pos_lt (p i) d (Nat.prime_of_mem_primeFactors i.property) hd
  have ha (n : ℕ) (hn : n ∈ A) (i : P) : e (n : ZMod q) i ∉ Ω i := by
    simp only [map_natCast, Pi.natCast_apply]
    exact pairForbidden_avoided (p i) d n (hA n hn i.val i.property)
  have h := excluded_crt_energy p e ψ hψ
    χ hχ Ω (fun i => (hp i).1) (fun i => (hp i).2) A (fun n : ℕ => (n : ZMod q)) ha
  have hprod : (∏ i : P, ((Ω i).card : ℝ) / ((p i : ℝ)-(Ω i).card)) =
      ∏ l ∈ q.primeFactors, if l ∣ d then 1 / ((l : ℝ)-1) else 2 / ((l : ℝ)-2) := by
    rw [← Finset.prod_coe_sort q.primeFactors (fun l : ℕ =>
      if l ∣ d then 1 / ((l : ℝ)-1) else 2 / ((l : ℝ)-2))]
    apply Finset.prod_congr rfl
    intro i hi
    dsimp only [Ω]
    rw [pairForbidden_card]
    split_ifs <;> norm_num [p]
  rw [hprod] at h
  exact h

end PrimitiveSieve


theorem solution
    (q : ℕ) [NeZero q] (d : ℕ) (hq : Squarefree q) (hd : 2 ∣ d)
    (A : Finset ℕ)
    (hA : ∀ n ∈ A, ∀ p ∈ q.primeFactors, ¬ p ∣ n*(n+d)) :
    (∏ p ∈ q.primeFactors,
      if p ∣ d then 1 / ((p : ℝ)-1) else 2 / ((p : ℝ)-2)) * (A.card : ℝ)^2 ≤
      ∑ u : (ZMod q)ˣ, ‖∑ n ∈ A, ZMod.stdAddChar (u.val*(n : ZMod q))‖^2 := by
  classical
  let χ (p : q.primeFactors) : AddChar (ZMod p.val) ℂ := by
    letI : NeZero p.val := ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩
    exact ZMod.stdAddChar
  have hχ (p : q.primeFactors) : Function.Injective (χ p) := by
    letI : NeZero p.val := ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩
    exact ZMod.injective_stdAddChar
  exact PrimitiveSieve.squarefree_pair_energy_generic q d hq hd A hA
    ZMod.stdAddChar ZMod.injective_stdAddChar χ hχ
