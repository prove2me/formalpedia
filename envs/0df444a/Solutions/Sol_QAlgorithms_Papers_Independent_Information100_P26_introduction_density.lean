-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P26.introduction_density
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T13:31:33.914359+00:00
-- url     : https://prove2.me/submissions/8a68b8aa-3600-417c-aa20-ea5b18c85f58

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26
import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_corollary_6_15

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

theorem x8_dep_apply {d : ℕ} (p q : Fin d × Fin d) :
    depolarizing d p q = if p.1 = p.2 ∧ q.1 = q.2 then (d : ℂ)⁻¹ else 0 := rfl

theorem x8_dep_sq {d : ℕ} (hd : 0 < d) : depolarizing d * depolarizing d = depolarizing d := by
  ext p q
  rw [Matrix.mul_apply]
  simp only [x8_dep_apply]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  by_cases hp : p.1 = p.2
  · by_cases hq : q.1 = q.2
    · simp only [hp, hq, true_and, and_true]
      rw [Fintype.sum_prod_type]
      simp only [ite_mul, zero_mul, mul_ite, mul_zero]
      rw [Finset.sum_congr rfl fun x _ => Finset.sum_ite_eq _ _ _]
      simp only [Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp
    · simp [hq]
  · simp [hp]

def x8mix (d : ℕ) (a : ℝ) : Map d := depolarizingMixture d a

theorem x8_mix_mul {d : ℕ} (hd : 0 < d) (a b : ℝ) :
    depolarizingMixture d a * depolarizingMixture d b = depolarizingMixture d (a * b) := by
  unfold depolarizingMixture
  have h := x8_dep_sq hd
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, h]

  module

theorem x8_mix_pow {d : ℕ} (hd : 0 < d) (a : ℝ) (n : ℕ) :
    depolarizingMixture d a ^ n = depolarizingMixture d (a ^ n) := by
  induction n with
  | zero => simp [depolarizingMixture]
  | succ n ih => rw [pow_succ, ih, x8_mix_mul hd, pow_succ]

theorem x8_applyMap {d : ℕ} (t : Map d) (X : Mat d) (i j : Fin d) :
    applyMap t X i j = ∑ p : Fin d × Fin d, t (i, j) p * X p.1 p.2 := by
  simp [applyMap, QAlgorithms.act, Matrix.mulVec, dotProduct]

theorem x8_mix_apply {d : ℕ} (a : ℝ) (X : Mat d) :
    applyMap (depolarizingMixture d a) X =
      (a : ℂ) • X + (((1 - a : ℝ) : ℂ) * (d : ℂ)⁻¹ * X.trace) • (1 : Mat d) := by
  ext i j
  rw [x8_applyMap]
  simp only [depolarizingMixture, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    x8_dep_apply, add_mul, Finset.sum_add_distrib, Matrix.trace, Matrix.diag]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Prod.mk.injEq, Complex.real_smul, ite_mul, one_mul, zero_mul, mul_ite, mul_zero,
    smul_eq_mul, ite_and]
  by_cases hij : i = j
  · subst hij
    simp [Finset.sum_ite_eq, Finset.mul_sum, mul_assoc]
  · simp [hij, Finset.sum_ite_eq]

def x8E {d : ℕ} (a : ℝ) : Fin (d * d + 1) → Mat d :=
  Fin.cons (((Real.sqrt a : ℝ) : ℂ) • (1 : Mat d))
    (fun k => ((Real.sqrt ((1 - a) / d) : ℝ) : ℂ) •
      Matrix.single (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 (1 : ℂ))

theorem x8_sum_E {d : ℕ} {M : Type*} [AddCommMonoid M] (a : ℝ) (f : Mat d → M) :
    ∑ k, f (x8E a k) = f (((Real.sqrt a : ℝ) : ℂ) • (1 : Mat d)) +
      ∑ p : Fin d × Fin d, f (((Real.sqrt ((1 - a) / d) : ℝ) : ℂ) • Matrix.single p.1 p.2 (1 : ℂ)) := by
  rw [Fin.sum_univ_succ]
  simp only [x8E, Fin.cons_zero, Fin.cons_succ]
  congr 1
  exact Equiv.sum_comp finProdFinEquiv.symm
    (fun p : Fin d × Fin d => f (((Real.sqrt ((1 - a) / d) : ℝ) : ℂ) • Matrix.single p.1 p.2 (1 : ℂ)))

theorem x8_sqrt_sq (x : ℝ) (hx : 0 ≤ x) :
    conj ((Real.sqrt x : ℝ) : ℂ) * ((Real.sqrt x : ℝ) : ℂ) = (x : ℂ) := by
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hx]

theorem x8_sq_lemmas (x : ℝ) (hx : 0 ≤ x) :
    star ((Real.sqrt x : ℝ) : ℂ) * ((Real.sqrt x : ℝ) : ℂ) = (x : ℂ) ∧
    ((Real.sqrt x : ℝ) : ℂ) * star ((Real.sqrt x : ℝ) : ℂ) = (x : ℂ) := by
  have h := x8_sqrt_sq x hx
  exact ⟨h, by rw [mul_comm]; exact h⟩

theorem x8_E_kraus {d : ℕ} (hd : 0 < d) (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    IsKrausFamily (x8E (d := d) a) := by
  unfold IsKrausFamily
  rw [x8_sum_E a (fun E => Eᴴ * E)]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hb : 0 ≤ (1 - a) / d := div_nonneg (by linarith) (Nat.cast_nonneg _)
  obtain ⟨ha1, ha2⟩ := x8_sq_lemmas a h0
  obtain ⟨hb1, hb2⟩ := x8_sq_lemmas _ hb
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.conjTranspose_one, Matrix.one_mul, ha1, ha2, hb1, hb2]
  ext i j
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.single_apply, Fintype.sum_prod_type, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq', ite_and]
    push_cast; field_simp; ring
  · simp [hij, ite_and]
    intro h; exact absurd h.symm hij

theorem x8_E_apply {d : ℕ} (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) (X : Mat d) :
    krausApply (x8E (d := d) a) X = applyMap (depolarizingMixture d a) X := by
  unfold krausApply
  rw [x8_sum_E a (fun E => E * X * Eᴴ), x8_mix_apply]
  have hb : 0 ≤ (1 - a) / d := div_nonneg (by linarith) (Nat.cast_nonneg _)
  obtain ⟨ha1, ha2⟩ := x8_sq_lemmas a h0
  obtain ⟨hb1, hb2⟩ := x8_sq_lemmas _ hb
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, ha1, ha2, hb1, hb2]
  ext i j
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.single_apply, Fintype.sum_prod_type, Matrix.one_apply,
    Matrix.trace, Matrix.diag]
  by_cases hij : i = j
  · subst hij
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mul_sum, ite_and]
    push_cast; ring_nf
  · simp [hij, ite_and]

theorem x8_mix_unital {d : ℕ} (hd : 0 < d) (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    UnitalChannel (depolarizingMixture d a) := by
  refine ⟨⟨d * d + 1, x8E a, x8_E_kraus hd a h0 h1, fun X => (x8_E_apply a h0 h1 X).symm⟩, ?_⟩
  rw [x8_mix_apply, Matrix.trace_one, Fintype.card_fin]
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [← add_smul]
  convert one_smul ℂ (1 : Mat d)
  push_cast; field_simp; ring

theorem x8_mulT {d : ℕ} (t : Map d) (p q : Fin d × Fin d) :
    (t * transposition d) p q = t p (q.2, q.1) := by
  rw [Matrix.mul_apply]
  simp [transposition]

theorem x8_amp_apply {d : ℕ} (a : ℝ) (Z : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ)
    (p q : Fin d × Fin 2) :
    amplify (depolarizingMixture d a * transposition d) 2 Z p q =
      (a : ℂ) * Z (q.1, p.2) (p.1, q.2) +
        (if p.1 = q.1 then ((1 - a : ℝ) : ℂ) * (d : ℂ)⁻¹ * ∑ u, Z (u, p.2) (u, q.2) else 0) := by
  simp only [amplify, x8_mulT, depolarizingMixture, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, x8_dep_apply, Prod.mk.injEq, Complex.real_smul, add_mul,
    Finset.sum_add_distrib, ite_and, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  congr 1
  · simp [Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]
  · by_cases h : p.1 = q.1
    · simp [h, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mul_sum, mul_assoc]
    · simp [h]

theorem x8_quad2 {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (p q : ι) :
    star (Pi.single p 1 - Pi.single q 1 : ι → ℂ) ⬝ᵥ (M *ᵥ (Pi.single p 1 - Pi.single q 1)) =
      M p p - M p q - M q p + M q q := by
  simp only [dotProduct, Matrix.mulVec, Pi.sub_apply, Pi.star_apply, star_sub, Pi.single_apply,
    mul_sub, sub_mul, Finset.sum_sub_distrib]
  simp [apply_ite (star : ℂ → ℂ)]
  ring

theorem x8_not_twoCop {d : ℕ} (hd : 2 ≤ d) (a : ℝ) (ha : 1 / ((d : ℝ) + 1) < a) :
    ¬ TwoCopositive (depolarizingMixture d a) := by
  intro h
  have hd0 : 0 < d := by omega
  let i0 : Fin d := ⟨0, hd0⟩
  let i1 : Fin d := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  let v : Fin d × Fin 2 → ℂ := fun p => if p = (i0, 0) then 1 else if p = (i1, 1) then 1 else 0
  have hZ := h (Matrix.vecMulVec v (star v)) (Matrix.posSemidef_vecMulVec_self_star v)
  have hq := hZ.dotProduct_mulVec_nonneg (Pi.single (i1, 0) 1 - Pi.single (i0, 1) 1)
  rw [x8_quad2] at hq
  simp only [x8_amp_apply, Matrix.vecMulVec_apply, Pi.star_apply, v] at hq
  have hs0 : ∀ u : Fin d, (if ((u, (0 : Fin 2)) : Fin d × Fin 2) = (i0, 0) then (1 : ℂ) else
      if ((u, (0 : Fin 2)) : Fin d × Fin 2) = (i1, 1) then 1 else 0) = if u = i0 then 1 else 0 := by
    intro u; simp [Prod.mk.injEq]
  have hs1 : ∀ u : Fin d, (if ((u, (1 : Fin 2)) : Fin d × Fin 2) = (i0, 0) then (1 : ℂ) else
      if ((u, (1 : Fin 2)) : Fin d × Fin 2) = (i1, 1) then 1 else 0) = if u = i1 then 1 else 0 := by
    intro u; simp [Prod.mk.injEq]
  simp only [hs0, hs1] at hq
  simp [h01, h01.symm, Finset.sum_ite_eq'] at hq
  have hd1 : (0 : ℝ) < d := by exact_mod_cast hd0
  have key : (1 - a) * (d : ℝ)⁻¹ < a := by
    rw [div_lt_iff₀ (by linarith)] at ha
    rw [← div_eq_mul_inv, div_lt_iff₀ hd1]; linarith
  have hre := (Complex.nonneg_iff.1 hq).1
  simp at hre
  push_cast at hre
  nlinarith [hre]

theorem x8_trace_real {I : Type*} [Fintype I] {M : Matrix I I ℂ} (hM : M.PosSemidef) :
    M.trace = ((M.trace.re : ℝ) : ℂ) := by
  have h := (Complex.nonneg_iff.1 hM.trace_nonneg).2
  apply Complex.ext <;> simp [← h]

theorem x8_normalize {I : Type*} [Fintype I] [Nonempty I] {M : Matrix I I ℂ} (hM : M.PosSemidef) :
    ∃ A : Matrix I I ℂ, IsDensityMatrix A ∧ M = ((M.trace.re : ℝ) : ℂ) • A := by
  classical
  by_cases h0 : M.trace = 0
  · refine ⟨Matrix.diagonal (Pi.single (Classical.arbitrary I) 1), ⟨?_, ?_⟩, ?_⟩
    · rw [Matrix.posSemidef_diagonal_iff]; intro i
      by_cases hi : i = Classical.arbitrary I
      · subst hi; simp
      · simp [Pi.single_apply, hi]
    · simp [Matrix.trace_diagonal]
    · rw [(hM.trace_eq_zero_iff).1 h0]; simp
  · set t := M.trace.re with ht
    have htr := x8_trace_real hM
    have htpos : t ≠ 0 := by intro h; apply h0; rw [htr, ← ht, h]; simp
    refine ⟨((t⁻¹ : ℝ) : ℂ) • M, ⟨hM.smul (Complex.zero_le_real.2 (inv_nonneg.2 ?_)), ?_⟩, ?_⟩
    · rw [ht]; exact (Complex.nonneg_iff.1 hM.trace_nonneg).1
    · rw [Matrix.trace_smul, htr, ← ht, smul_eq_mul, ← Complex.ofReal_mul, inv_mul_cancel₀ htpos]
      simp
    · rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ htpos]; simp

theorem x8_sep {I J ι : Type*} [Fintype I] [Fintype J] [Fintype ι] [Nonempty I] [Nonempty J]
    (M : ι → Matrix I I ℂ) (N : ι → Matrix J J ℂ)
    (hM : ∀ n, (M n).PosSemidef) (hN : ∀ n, (N n).PosSemidef) :
    QAlgorithms.Entanglement.IsSeparablePositive (∑ n, Matrix.kronecker (M n) (N n)) := by
  choose A hA hMA using fun n => x8_normalize (hM n)
  choose B hB hNB using fun n => x8_normalize (hN n)
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun n => (M (e.symm n)).trace.re * (N (e.symm n)).trace.re,
    fun n => A (e.symm n), fun n => B (e.symm n), fun n => mul_nonneg
    (Complex.nonneg_iff.1 (hM _).trace_nonneg).1 (Complex.nonneg_iff.1 (hN _).trace_nonneg).1,
    fun n => ⟨hA _, hB _⟩, ?_⟩
  rw [← e.symm.sum_comp]
  refine Finset.sum_congr rfl fun n _ => ?_
  conv_lhs => rw [hMA (e.symm n), hNB (e.symm n)]
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [Matrix.kronecker, Matrix.kroneckerMap_apply]; ring

theorem x8_conj (x : ZMod 3) :
    conj (ZMod.stdAddChar x : ℂ) = ZMod.stdAddChar (-x) := by
  rw [AddChar.map_neg_eq_inv, ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj, Circle.coe_inv]

theorem x8_char {d : ℕ} (i j k l : Fin d) :
    ∑ θ : Fin d → ZMod 3, (ZMod.stdAddChar (θ i - θ j - θ k + θ l) : ℂ) =
      if (i = j ∧ k = l) ∨ (i = k ∧ j = l) then (3 : ℂ) ^ d else 0 := by
  let L : (Fin d → ZMod 3) →+ ZMod 3 :=
    AddMonoidHom.mk' (fun θ => θ i - θ j - θ k + θ l) (by intros; simp; ring)
  have hL : ∀ θ, L θ = θ i - θ j - θ k + θ l := fun _ => rfl
  have e : ∑ θ : Fin d → ZMod 3, (ZMod.stdAddChar (θ i - θ j - θ k + θ l) : ℂ) =
      ∑ θ, (ZMod.stdAddChar (N := 3)).compAddMonoidHom L θ := by
    simp only [AddChar.compAddMonoidHom_apply, hL]
  have hone : ∀ x : ZMod 3, (ZMod.stdAddChar x : ℂ) = 1 ↔ x = 0 := by
    intro x
    rw [← (ZMod.stdAddChar (N := 3)).map_zero_eq_one, ZMod.injective_stdAddChar.eq_iff]
  rw [e, AddChar.sum_eq_ite]
  have hcard : ((Fintype.card (Fin d → ZMod 3) : ℕ) : ℂ) = (3 : ℂ) ^ d := by
    simp [Fintype.card_fun, ZMod.card]
  rw [hcard]
  by_cases hc : (i = j ∧ k = l) ∨ (i = k ∧ j = l)
  · rw [if_pos hc, if_pos]
    rw [AddChar.eq_zero_iff]
    intro θ
    rw [AddChar.compAddMonoidHom_apply, hone, hL]
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> ring
  · rw [if_neg hc, if_neg]
    rw [← ne_eq, AddChar.ne_zero_iff]
    simp only [AddChar.compAddMonoidHom_apply, ne_eq, hone, hL]
    push_neg at hc
    by_cases hij : i = j
    · subst hij
      have hkl : k ≠ l := fun h => (hc.1 rfl h)
      refine ⟨Pi.single k 1, ?_⟩
      simp [Pi.single_apply, Ne.symm hkl]
    · by_cases hik : i = k
      · subst hik
        have hjl : j ≠ l := fun h => (hc.2 rfl h)
        refine ⟨Pi.single l 1, ?_⟩
        simp [Pi.single_apply, hjl]
      · refine ⟨Pi.single i 1, ?_⟩
        simp only [Pi.single_apply, Ne.symm hij, Ne.symm hik, if_true, if_false]
        split_ifs <;> decide

theorem x8_choi_mix {d : ℕ} (b : ℝ) (i k j l : Fin d) :
    choi (depolarizingMixture d b) (i, k) (j, l) =
      (if i = k ∧ j = l then (b : ℂ) else 0) +
        (if i = j ∧ k = l then ((1 - b : ℝ) : ℂ) * (d : ℂ)⁻¹ else 0) := by
  simp only [choi, depolarizingMixture, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    x8_dep_apply, Prod.mk.injEq, Complex.real_smul]
  split_ifs <;> simp

theorem x8_arith {d : ℕ} (i j k l : Fin d) (b : ℝ) :
    ((if i = k ∧ j = l then (b : ℂ) else 0) + if i = j ∧ k = l then ((1 - b : ℝ) : ℂ) * (d : ℂ)⁻¹ else 0) =
    (if i = j ∧ k = l ∨ i = k ∧ j = l then (b : ℂ) else 0) +
      (((1 - b) / d - b + if i = k then b else 0 : ℝ) : ℂ) * (if j = i then 1 else 0) *
        (if l = k then 1 else 0) := by
  simp only [@eq_comm _ j i, @eq_comm _ l k]
  by_cases hij : i = j <;> by_cases hkl : k = l <;> by_cases hik : i = k <;> by_cases hjl : j = l <;>
    subst_vars <;> simp_all <;> push_cast <;> ring

def x8ψ {d : ℕ} (θ : Fin d → ZMod 3) : Fin d → ℂ := fun c => ZMod.stdAddChar (θ c)

def x8e {d : ℕ} (k : Fin d) : Fin d → ℂ := Pi.single k 1

theorem x8_mix_EB {d : ℕ} (hd : 0 < d) (b : ℝ) (h0 : 0 ≤ b) (h1 : b ≤ 1 / ((d : ℝ) + 1)) :
    EB (depolarizingMixture d b) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hd1 : (0 : ℝ) < d := by exact_mod_cast hd
  set c : ℝ := (1 - b) / d - b with hc
  have hc0 : 0 ≤ c := by
    rw [hc, sub_nonneg, le_div_iff₀ hd1]
    rw [le_div_iff₀ (by linarith)] at h1; linarith
  let ι := (Fin d → ZMod 3) ⊕ (Fin d × Fin d)
  let M : ι → Mat d := fun x => match x with
    | Sum.inl θ => ((b / 3 ^ d : ℝ) : ℂ) • Matrix.vecMulVec (x8ψ θ) (star (x8ψ θ))
    | Sum.inr kl => ((c + if kl.1 = kl.2 then b else 0 : ℝ) : ℂ) •
        Matrix.vecMulVec (x8e kl.1) (star (x8e kl.1))
  let N : ι → Mat d := fun x => match x with
    | Sum.inl θ => Matrix.vecMulVec (x8ψ (-θ)) (star (x8ψ (-θ)))
    | Sum.inr kl => Matrix.vecMulVec (x8e kl.2) (star (x8e kl.2))
  have hM : ∀ x, (M x).PosSemidef := by
    rintro (θ | kl)
    · exact (Matrix.posSemidef_vecMulVec_self_star _).smul
        (Complex.zero_le_real.2 (div_nonneg h0 (by positivity)))
    · refine (Matrix.posSemidef_vecMulVec_self_star _).smul (Complex.zero_le_real.2 ?_)
      split_ifs <;> linarith
  have hN : ∀ x, (N x).PosSemidef := by
    rintro (θ | kl) <;> exact Matrix.posSemidef_vecMulVec_self_star _
  have key : choi (depolarizingMixture d b) = ∑ x, Matrix.kronecker (M x) (N x) := by
    ext ⟨i, k⟩ ⟨j, l⟩
    rw [x8_choi_mix, Matrix.sum_apply, Fintype.sum_sum_type]
    have hθ : ∀ θ : Fin d → ZMod 3, Matrix.kronecker (M (Sum.inl θ)) (N (Sum.inl θ)) (i, k) (j, l) =
        ((b / 3 ^ d : ℝ) : ℂ) * (ZMod.stdAddChar (θ i - θ j - θ k + θ l) : ℂ) := by
      intro θ
      simp only [M, N, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.smul_apply,
        Matrix.vecMulVec_apply, Pi.star_apply, x8ψ, smul_eq_mul, RCLike.star_def, x8_conj,
        Pi.neg_apply, neg_neg]
      rw [mul_assoc, mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul,
        ← AddChar.map_add_eq_mul]
      congr 2; ring
    simp only [hθ, ← Finset.mul_sum, x8_char]
    simp only [M, N, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, x8e, Pi.single_apply, smul_eq_mul, RCLike.star_def,
      Fintype.sum_prod_type, map_one, map_zero, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul]
    simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have h3 : (3 : ℂ) ^ d ≠ 0 := pow_ne_zero _ (by norm_num)
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [show ((b / 3 ^ d : ℝ) : ℂ) * 3 ^ d = b by push_cast; field_simp]
    simp only [apply_ite (starRingEnd ℂ), map_one, map_zero, hc]
    exact x8_arith i j k l b
  unfold EB
  rw [key]
  exact x8_sep M N hM hN



theorem x8_deph_apply {d : ℕ} (p q : Fin d × Fin d) :
    dephasing d p q = if p.1 = p.2 ∧ p = q then 1 else 0 := rfl

theorem x8_deph_sq {d : ℕ} : dephasing d * dephasing d = dephasing d := by
  ext p q
  rw [Matrix.mul_apply]
  simp only [x8_deph_apply, ite_and, mul_ite, ite_mul, one_mul, mul_zero, zero_mul]
  by_cases hp : p.1 = p.2
  · rw [Finset.sum_eq_single p]
    · simp [hp]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · simp [hp]

theorem x8_idem_mul {d : ℕ} (P : Map d) (hP : P * P = P) (a b : ℝ) :
    (a • (1 : Map d) + (1 - a) • P) * (b • (1 : Map d) + (1 - b) • P) =
      (a * b) • (1 : Map d) + (1 - a * b) • P := by
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hP]
  module

theorem x8_dmix_pow {d : ℕ} (a : ℝ) (n : ℕ) :
    dephasingMixture d a ^ n = dephasingMixture d (a ^ n) := by
  induction n with
  | zero => simp [dephasingMixture]
  | succ n ih =>
    rw [pow_succ, ih]
    unfold dephasingMixture
    rw [x8_idem_mul _ x8_deph_sq, pow_succ]

theorem x8_dmix_entry {d : ℕ} (a : ℝ) (X : Mat d) (i j : Fin d) :
    applyMap (dephasingMixture d a) X i j =
      (a : ℂ) * X i j + if i = j then ((1 - a : ℝ) : ℂ) * X i i else 0 := by
  rw [x8_applyMap]
  simp only [dephasingMixture, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    x8_deph_apply, add_mul, Finset.sum_add_distrib, Complex.real_smul, mul_ite, mul_one,
    mul_zero, ite_mul, zero_mul]
  congr 1
  · rw [Finset.sum_ite_eq]; simp
  · by_cases hij : i = j
    · subst hij
      rw [Finset.sum_eq_single (i, i)]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    · simp [hij]

def x8F {d : ℕ} (a : ℝ) : Fin (d + 1) → Mat d :=
  Fin.cons (((Real.sqrt a : ℝ) : ℂ) • (1 : Mat d))
    (fun k => ((Real.sqrt (1 - a) : ℝ) : ℂ) • Matrix.single k k (1 : ℂ))

theorem x8_sum_F {d : ℕ} {M : Type*} [AddCommMonoid M] (a : ℝ) (f : Mat d → M) :
    ∑ k, f (x8F a k) = f (((Real.sqrt a : ℝ) : ℂ) • (1 : Mat d)) +
      ∑ k : Fin d, f (((Real.sqrt (1 - a) : ℝ) : ℂ) • Matrix.single k k (1 : ℂ)) := by
  rw [Fin.sum_univ_succ]
  simp only [x8F, Fin.cons_zero, Fin.cons_succ]

theorem x8_F_kraus {d : ℕ} (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    IsKrausFamily (x8F (d := d) a) := by
  unfold IsKrausFamily
  rw [x8_sum_F a (fun E => Eᴴ * E)]
  obtain ⟨ha1, ha2⟩ := x8_sq_lemmas a h0
  obtain ⟨hb1, hb2⟩ := x8_sq_lemmas (1 - a) (by linarith)
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.conjTranspose_one, Matrix.one_mul, ha1, ha2, hb1, hb2]
  ext i j
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.single_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq', ite_and]
  · simp [hij, ite_and]
    intro h; exact absurd h.symm hij

theorem x8_F_apply {d : ℕ} (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) (X : Mat d) :
    krausApply (x8F (d := d) a) X = applyMap (dephasingMixture d a) X := by
  unfold krausApply
  rw [x8_sum_F a (fun E => E * X * Eᴴ)]
  obtain ⟨ha1, ha2⟩ := x8_sq_lemmas a h0
  obtain ⟨hb1, hb2⟩ := x8_sq_lemmas (1 - a) (by linarith)
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, ha1, ha2, hb1, hb2]
  ext i j
  rw [x8_dmix_entry]
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.single_apply]
  by_cases hij : i = j
  · subst hij
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq', ite_and]
  · simp [hij, ite_and]

theorem x8_dmix_unital {d : ℕ} (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    UnitalChannel (dephasingMixture d a) := by
  refine ⟨⟨d + 1, x8F a, x8_F_kraus a h0 h1, fun X => (x8_F_apply a h0 h1 X).symm⟩, ?_⟩
  ext i j
  rw [x8_dmix_entry]
  by_cases hij : i = j
  · subst hij; simp <;> push_cast <;> ring
  · simp [hij]

theorem x8_damp_apply {d : ℕ} (a : ℝ) (Z : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ)
    (p q : Fin d × Fin 2) :
    amplify (dephasingMixture d a * transposition d) 2 Z p q =
      (a : ℂ) * Z (q.1, p.2) (p.1, q.2) +
        (if p.1 = q.1 then ((1 - a : ℝ) : ℂ) * Z (p.1, p.2) (p.1, q.2) else 0) := by
  simp only [amplify, x8_mulT, dephasingMixture, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, x8_deph_apply, Prod.mk.injEq, Complex.real_smul, add_mul,
    Finset.sum_add_distrib, ite_and, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  congr 1
  · simp [Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]
  · by_cases h : p.1 = q.1
    · simp only [h, if_true]
      simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
    · simp [h]

theorem x8_dmix_not_twoCop {d : ℕ} (hd : 2 ≤ d) (a : ℝ) (ha : 0 < a) :
    ¬ TwoCopositive (dephasingMixture d a) := by
  intro h
  have hd0 : 0 < d := by omega
  let i0 : Fin d := ⟨0, hd0⟩
  let i1 : Fin d := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  let v : Fin d × Fin 2 → ℂ := fun p => if p = (i0, 0) then 1 else if p = (i1, 1) then 1 else 0
  have hZ := h (Matrix.vecMulVec v (star v)) (Matrix.posSemidef_vecMulVec_self_star v)
  have hq := hZ.dotProduct_mulVec_nonneg (Pi.single (i1, 0) 1 - Pi.single (i0, 1) 1)
  rw [x8_quad2] at hq
  simp only [x8_damp_apply, Matrix.vecMulVec_apply, Pi.star_apply, v] at hq
  simp [h01, h01.symm, Prod.mk.injEq] at hq
  rw [Complex.le_def] at hq
  simp at hq
  linarith [hq]

theorem x8_EB_twoCop {d : ℕ} (t : Map d) (h : EB t) : TwoCopositive t := by
  obtain ⟨q, w, A, B, hw, hAB, hchoi⟩ := h
  have ht : ∀ x y u v, t (x, y) (u, v) = ∑ j, (w j : ℂ) * (A j x y * B j u v) := by
    intro x y u v
    have := congrFun (congrFun hchoi (x, u)) (y, v)
    simp only [choi, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.kronecker,
      Matrix.kroneckerMap_apply] at this
    exact this
  choose m φ hφ using fun j => Matrix.posSemidef_iff_eq_sum_vecMulVec.mp (hAB j).2.1.transpose
  intro Z hZ
  let V : (j : Fin q) → Fin (m j) → Matrix (Fin d × Fin 2) (Fin 2) ℂ :=
    fun j k => Matrix.of fun p s => if p.2 = s then conj (φ j k p.1) else 0
  let C : Fin q → Matrix (Fin 2) (Fin 2) ℂ := fun j => ∑ k, (V j k)ᴴ * Z * V j k
  have hB : ∀ j u v, B j v u = ∑ k, φ j k u * conj (φ j k v) := by
    intro j u v
    rw [← Matrix.transpose_apply (B j), hφ j]
    simp [Matrix.sum_apply, Matrix.vecMulVec_apply]
  have hC : ∀ j s s', C j s s' = ∑ u, ∑ v, B j v u * Z (u, s) (v, s') := by
    intro j s s'
    have e : ∀ k, ((V j k)ᴴ * Z * V j k) s s' =
        ∑ u, ∑ v, φ j k u * conj (φ j k v) * Z (u, s) (v, s') := by
      intro k
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, V, Matrix.of_apply, Fintype.sum_prod_type]
      simp only [apply_ite (star : ℂ → ℂ), star_zero, RCLike.star_def, Complex.conj_conj, ite_mul,
        zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true,
        Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
    simp only [C, Matrix.sum_apply, e, hB, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
  have hCpsd : ∀ j, (C j).PosSemidef := fun j =>
    Matrix.posSemidef_sum _ fun k _ => hZ.conjTranspose_mul_mul_same (V j k)
  have key : amplify (t * transposition d) 2 Z = ∑ j, (w j : ℂ) • Matrix.kronecker (A j) (C j) := by
    ext p p'
    simp only [amplify, x8_mulT, ht, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.kronecker, Matrix.kroneckerMap_apply, hC, Finset.mul_sum, Finset.sum_mul]
    conv_lhs => arg 2; ext v; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [key]
  exact Matrix.posSemidef_sum _ fun j _ =>
    ((hAB j).1.1.kronecker (hCpsd j)).smul (Complex.zero_le_real.2 (hw j))

theorem x8_dmix_offdiag {d : ℕ} (a : ℝ) (X : Mat d) (z : ℂ) (hz : ‖z‖ = 1) (ha1 : a < 1)
    (ha0 : 0 ≤ a) (hX : applyMap (dephasingMixture d a) X = z • X) (i j : Fin d) (hij : i ≠ j) :
    X i j = 0 := by
  have h := congrFun (congrFun hX i) j
  rw [x8_dmix_entry, if_neg hij, add_zero, Matrix.smul_apply, smul_eq_mul] at h
  by_contra hne
  have : (a : ℂ) = z := mul_right_cancel₀ hne h
  rw [← this] at hz
  simp [abs_of_nonneg ha0] at hz
  linarith

theorem x8_diag_mem {d : ℕ} (X : Mat d) (hX : ∀ i j, i ≠ j → X i j = 0) :
    X ∈ diagonalSpace d := by
  have : X = ∑ i, X i i • Matrix.single i i (1 : ℂ) := by
    ext k l
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    by_cases hkl : k = l
    · subst hkl; simp [Finset.sum_ite_eq']
    · rw [hX k l hkl]
      symm; apply Finset.sum_eq_zero; intro x _
      simp
      intro h1 h2; exact absurd (h1.symm.trans h2) hkl
  rw [this]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem x8_dmix_single {d : ℕ} (a : ℝ) (i : Fin d) :
    applyMap (dephasingMixture d a) (Matrix.single i i (1 : ℂ)) = Matrix.single i i (1 : ℂ) := by
  ext k l
  rw [x8_dmix_entry]
  by_cases hkl : k = l
  · subst hkl
    by_cases hki : k = i
    · subst hki; simp <;> push_cast <;> ring
    · simp [Matrix.single_apply, Ne.symm hki]
  · have : ¬ (i = k ∧ i = l) := fun h => hkl (h.1.symm.trans h.2)
    simp [Matrix.single_apply, this, hkl]

theorem x8_dmix_peripheral {d : ℕ} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    peripheral (dephasingMixture d a) = diagonalSpace d := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro X ⟨z, hz, hX⟩
    exact x8_diag_mem X fun i j hij => x8_dmix_offdiag a X z hz ha1 ha0 hX i j hij
  · apply Submodule.span_le.2
    rintro X ⟨i, rfl⟩
    exact Submodule.subset_span ⟨1, by simp, by rw [x8_dmix_single, one_smul]⟩

theorem x8_dmix_eig {d : ℕ} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (z : ℂ) (hz : ‖z‖ = 1)
    (X : Mat d) (hX0 : X ≠ 0) (hX : applyMap (dephasingMixture d a) X = z • X) : z = 1 := by
  have hoff := x8_dmix_offdiag a X z hz ha1 ha0 hX
  obtain ⟨k, l, hkl⟩ : ∃ k l, X k l ≠ 0 := by
    by_contra hc; push_neg at hc; exact hX0 (Matrix.ext hc)
  have hkl' : k = l := by by_contra hne; exact hkl (hoff k l hne)
  subst hkl'
  have h := congrFun (congrFun hX k) k
  rw [x8_dmix_entry, if_pos rfl, Matrix.smul_apply, smul_eq_mul] at h
  have : (1 : ℂ) * X k k = z * X k k := by rw [← h]; push_cast; ring
  exact (mul_right_cancel₀ hkl this).symm

theorem x8_ex65 {d : ℕ} (hd : 2 ≤ d) (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    let t := dephasingMixture d a
    UnitalChannel t ∧ peripheral t = diagonalSpace d ∧
    (∀ z : ℂ, ‖z‖ = 1 → (∃ X : Mat d, X ≠ 0 ∧ applyMap t X = z • X) → z = 1) ∧
    (∀ n : ℕ, 1 ≤ n → t^n = dephasingMixture d (a^n) ∧ ¬ TwoCopositive (t^n)) ∧
    ¬ Eventually TwoCopositive t ∧ ¬ Eventually EB t := by
  intro t
  have hpow : ∀ n : ℕ, ¬ TwoCopositive (t ^ n) := by
    intro n
    rw [x8_dmix_pow]
    exact x8_dmix_not_twoCop hd _ (pow_pos ha n)
  refine ⟨x8_dmix_unital a ha.le ha1.le, x8_dmix_peripheral a ha.le ha1,
    fun z hz ⟨X, hX0, hX⟩ => x8_dmix_eig a ha.le ha1 z hz X hX0 hX,
    fun n _ => ⟨x8_dmix_pow a n, hpow n⟩, ?_, ?_⟩
  · rintro ⟨n0, _, h⟩
    exact hpow n0 (h n0 le_rfl)
  · rintro ⟨n0, _, h⟩
    exact hpow n0 (x8_EB_twoCop _ (h n0 le_rfl))



theorem x8_beta_apply {d : ℕ} (U V : Unitary d) (p q : Fin d × Fin d) :
    beta U V p q = ∑ i, (U : Mat d) p.1 i * conj ((U : Mat d) p.2 i) *
      (conj ((V : Mat d) q.1 i) * (V : Mat d) q.2 i) := by
  simp only [beta, Matrix.mul_apply, ad, Matrix.conjTranspose_apply, x8_deph_apply,
    Complex.star_def, Complex.conj_conj]
  have inner : ∀ j : Fin d × Fin d, (∑ j1 : Fin d × Fin d, (U : Mat d) p.1 j1.1 *
      conj ((U : Mat d) p.2 j1.2) * (if j1.1 = j1.2 ∧ j1 = j then 1 else 0)) =
      if j.1 = j.2 then (U : Mat d) p.1 j.1 * conj ((U : Mat d) p.2 j.2) else 0 := by
    intro j
    rw [Finset.sum_eq_single j]
    · by_cases h : j.1 = j.2 <;> simp [h]
    · intro b _ hb; simp [hb]
    · simp
  simp only [inner, ite_mul, zero_mul]
  rw [Fintype.sum_prod_type]
  simp [Finset.sum_ite_eq]

theorem x8_MTD_EB {d : ℕ} (hd : 0 < d) {t : Map d} (h : MTD t) : EB t := by
  obtain ⟨n, p, U, V, hp, -, rfl⟩ := h
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let u : Fin n × Fin d → Fin d → ℂ := fun x a => (U x.1 : Mat d) a x.2
  let v : Fin n × Fin d → Fin d → ℂ := fun x b => conj ((V x.1 : Mat d) b x.2)
  have key : choi (∑ j, p j • beta (U j) (V j)) =
      ∑ x : Fin n × Fin d, Matrix.kronecker (((p x.1 : ℝ) : ℂ) • Matrix.vecMulVec (u x) (star (u x)))
        (Matrix.vecMulVec (v x) (star (v x))) := by
    ext a b
    simp only [choi, Matrix.sum_apply, Matrix.smul_apply, x8_beta_apply, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Matrix.vecMulVec_apply, Pi.star_apply, Complex.star_def,
      Complex.conj_conj, Complex.real_smul, smul_eq_mul, u, v, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  unfold EB
  rw [key]
  exact x8_sep _ _ (fun x => (Matrix.posSemidef_vecMulVec_self_star _).smul
    (Complex.zero_le_real.2 (hp x.1))) (fun x => Matrix.posSemidef_vecMulVec_self_star _)

end QAlgorithms.Papers.Independent.Information100.P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X8C6

variable {d : ℕ}

lemma dep_apply (p q : Fin d × Fin d) :
    depolarizing d p q = if p.1 = p.2 ∧ q.1 = q.2 then (d : ℂ)⁻¹ else 0 := rfl

lemma ad_apply (B : Mat d) (p q : Fin d × Fin d) : ad B p q = B p.1 q.1 * conj (B p.2 q.2) := rfl

lemma applyMap_apply (t : Map d) (X : Mat d) (i j : Fin d) :
    applyMap t X i j = ∑ q : Fin d × Fin d, t (i, j) q * X q.1 q.2 := by
  simp [applyMap, QAlgorithms.act, Matrix.mulVec, dotProduct]

lemma am_mul (s r : Map d) (X : Mat d) :
    applyMap (s * r) X = applyMap s (applyMap r X) := by
  ext i j
  simp only [applyMap_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
  ring

lemma am_ad (B : Mat d) (X : Mat d) : applyMap (ad B) X = B * X * Bᴴ := by
  ext i j
  rw [applyMap_apply]
  simp only [ad, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
    Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma am_sum {K : Type*} [Fintype K] (M : K → Map d) (X : Mat d) :
    applyMap (∑ k, M k) X = ∑ k, applyMap (M k) X := by
  ext i j
  simp only [applyMap_apply, Matrix.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma ent_single' {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (r s i j : n) :
    (A * Matrix.single r s (1 : ℂ) * Aᴴ) i j = A i r * conj (A j s) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single s]
  · rw [Matrix.conjTranspose_apply, Matrix.mul_apply, Finset.sum_eq_single r]
    · simp [Complex.star_def]
    · intro b _ hb; simp only [Matrix.single_apply]; rw [if_neg (fun h => hb h.1.symm)]; simp
    · simp
  · intro b _ hb
    rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro c _; simp [Matrix.single_apply, Ne.symm hb]
  · simp

lemma kraus_form {t : Map d} (ht : UnitalChannel t) :
    ∃ m : ℕ, ∃ E : Fin m → Mat d, (∑ j, (E j)ᴴ * E j = 1) ∧ t = ∑ j, ad (E j) := by
  obtain ⟨m, E, hK, hE⟩ := ht.1
  refine ⟨m, E, hK, ?_⟩
  ext p q
  have h := congrFun (congrFun (hE (Matrix.single q.1 q.2 1)) p.1) p.2
  rw [applyMap_apply, Finset.sum_eq_single q] at h
  · rw [Matrix.sum_apply]
    simp only [Matrix.single_apply, and_self, if_true, mul_one] at h
    rw [h]
    simp only [QAlgorithms.krausApply, Matrix.sum_apply, ent_single']
    rfl
  · intro b _ hb
    rw [Matrix.single_apply, if_neg (fun c => hb (Prod.ext c.1.symm c.2.symm)), mul_zero]
  · simp

lemma isChannel_of_kraus {K ι : Type*} [Fintype K] [Fintype ι] [DecidableEq ι]
    (E : K → Matrix ι ι ℂ) (hE : QAlgorithms.IsKrausFamily E) (Φ : QAlgorithms.Superop ι ι)
    (hΦ : ∀ ρ, Φ ρ = QAlgorithms.krausApply E ρ) : QAlgorithms.IsChannel Φ := by
  classical
  let e := Fintype.equivFin K
  refine ⟨Fintype.card K, fun j => E (e.symm j), ?_, ?_⟩
  · unfold QAlgorithms.IsKrausFamily at hE ⊢
    rw [← hE]
    exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  · intro ρ
    rw [hΦ]
    unfold QAlgorithms.krausApply
    exact (Fintype.sum_equiv e.symm _ _ (fun _ => rfl)).symm

lemma ad_mul (A B : Mat d) : ad A * ad B = ad (A * B) := by
  ext p q
  simp only [Matrix.mul_apply, ad_apply, Fintype.sum_prod_type, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma uc_mul {s r : Map d} (hs : UnitalChannel s) (hr : UnitalChannel r) :
    UnitalChannel (s * r) := by
  obtain ⟨m, E, hE, rfl⟩ := kraus_form hs
  obtain ⟨m', F, hF, rfl⟩ := kraus_form hr
  have hunit : applyMap ((∑ j, ad (E j)) * ∑ j, ad (F j)) 1 = 1 := by
    rw [am_mul, hr.2, hs.2]
  refine ⟨?_, hunit⟩
  let G : Fin m × Fin m' → Mat d := fun k => E k.1 * F k.2
  refine isChannel_of_kraus G ?_ _ ?_
  · unfold QAlgorithms.IsKrausFamily
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [G, Matrix.conjTranspose_mul]
    have : ∀ y : Fin m', ∑ x : Fin m, (F y)ᴴ * (E x)ᴴ * (E x * F y) = (F y)ᴴ * F y := by
      intro y
      calc ∑ x : Fin m, (F y)ᴴ * (E x)ᴴ * (E x * F y)
          = (F y)ᴴ * (∑ x, (E x)ᴴ * E x) * F y := by
            rw [Finset.mul_sum, Finset.sum_mul]
            exact Finset.sum_congr rfl fun x _ => by noncomm_ring
        _ = (F y)ᴴ * F y := by rw [hE, Matrix.mul_one]
    simp only [this]
    exact hF
  · intro ρ
    rw [am_mul, am_sum, am_sum]
    simp only [am_ad, QAlgorithms.krausApply, G, Fintype.sum_prod_type, Finset.mul_sum,
      Finset.sum_mul, Matrix.conjTranspose_mul]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    noncomm_ring

lemma uc_pow {t : Map d} (ht : UnitalChannel t) (n : ℕ) (hn : 1 ≤ n) :
    UnitalChannel (t ^ n) := by
  induction n, hn using Nat.le_induction with
  | base => rwa [pow_one]
  | succ n _ ih => rw [pow_succ]; exact uc_mul ih ht

lemma col_le {m : ℕ} (E : Fin m → Mat d) (hE : ∑ j, (E j)ᴴ * E j = 1) (a b : Fin d) :
    ∑ j, Complex.normSq (E j a b) ≤ 1 := by
  have h := congrFun (congrFun hE b) b
  rw [Matrix.sum_apply, Matrix.one_apply_eq] at h
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def] at h
  have h' : ∑ j, ∑ i, Complex.normSq (E j i b) = 1 := by
    have := congrArg Complex.re h
    simp only [Complex.re_sum, Complex.one_re] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    generalize E j i b = z
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]; ring
  rw [← h']
  refine Finset.sum_le_sum fun j _ => ?_
  exact Finset.single_le_sum (f := fun i => Complex.normSq (E j i b))
    (fun i _ => Complex.normSq_nonneg _) (Finset.mem_univ a)

lemma entry_le {t : Map d} (ht : UnitalChannel t) (p q : Fin d × Fin d) : ‖t p q‖ ≤ 1 := by
  obtain ⟨m, E, hE, rfl⟩ := kraus_form ht
  rw [Matrix.sum_apply]
  calc ‖∑ j, ad (E j) p q‖ ≤ ∑ j, ‖ad (E j) p q‖ := norm_sum_le _ _
    _ ≤ ∑ j, (Complex.normSq (E j p.1 q.1) + Complex.normSq (E j p.2 q.2)) / 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [ad_apply, norm_mul, Complex.norm_conj, Complex.normSq_eq_norm_sq,
          Complex.normSq_eq_norm_sq]
        nlinarith [sq_nonneg (‖E j p.1 q.1‖ - ‖E j p.2 q.2‖)]
    _ = (∑ j, Complex.normSq (E j p.1 q.1) + ∑ j, Complex.normSq (E j p.2 q.2)) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ 1 := by linarith [col_le E hE p.1 q.1, col_le E hE p.2 q.2]

end X8C6

end QAlgorithms.Papers.Independent.Information100.P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X8DN

open X8C6

variable {d : ℕ}

def Um (M : Map d) : Prop := ∀ p : Fin d × Fin d, ∑ i, M p (i,i) = if p.1 = p.2 then 1 else 0

lemma sum_diag (f : Fin d × Fin d → ℂ) :
    ∑ r : Fin d × Fin d, (if r.1 = r.2 then (1 : ℂ) else 0) * f r = ∑ j, f (j, j) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single x] <;> simp_all [eq_comm]

lemma sum_diag' (f : Fin d × Fin d → ℂ) :
    ∑ r : Fin d × Fin d, f r * (if r.1 = r.2 then (1 : ℂ) else 0) = ∑ j, f (j, j) := by
  rw [← sum_diag]; exact Finset.sum_congr rfl fun r _ => mul_comm _ _

lemma un_of {t : Map d} (ht : UnitalChannel t) : Um t := by
  intro p
  have h := congrFun (congrFun ht.2 p.1) p.2
  rw [applyMap_apply] at h
  rw [← sum_diag']
  rw [Matrix.one_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Matrix.one_apply]

lemma mul_dep {M : Map d} (hM : Um M) : M * depolarizing d = depolarizing d := by
  ext p q
  simp only [Matrix.mul_apply, dep_apply]
  rw [Fintype.sum_prod_type]
  by_cases hq : q.1 = q.2
  · simp only [hq, and_true, mul_ite, mul_zero]
    have : ∀ x : Fin d, (∑ y : Fin d, if x = y then M p (x, y) * (d : ℂ)⁻¹ else 0) =
        M p (x, x) * (d : ℂ)⁻¹ := fun x => by simp
    simp only [this, ← Finset.sum_mul, hM p]
    split_ifs <;> simp
  · simp [hq]


lemma am_smul (t : Map d) (c : ℂ) (X : Mat d) : applyMap t (c • X) = c • applyMap t X := by
  ext i j
  simp only [applyMap_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by ring

lemma am_sub (t : Map d) (X Y : Mat d) : applyMap t (X - Y) = applyMap t X - applyMap t Y := by
  ext i j
  simp only [applyMap_apply, Matrix.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun q _ => by ring

lemma tr_pres {t : Map d} (ht : UnitalChannel t) (X : Mat d) :
    (applyMap t X).trace = X.trace := by
  obtain ⟨⟨m, E, hE, hact⟩, -⟩ := ht
  rw [hact, QAlgorithms.krausApply, Matrix.trace_sum]
  simp only [Matrix.trace_mul_cycle (E _) X]
  rw [← Matrix.trace_sum, ← Finset.sum_mul]
  unfold QAlgorithms.IsKrausFamily at hE
  rw [hE, Matrix.one_mul]

lemma eig_le {t : Map d} (ht : UnitalChannel t) {Y : Mat d} {z : ℂ} (hY : Y ≠ 0)
    (hz : applyMap t Y = z • Y) : ‖z‖ ≤ 1 := by
  let v : Fin d × Fin d → ℂ := fun q => Y q.1 q.2
  have htv : t *ᵥ v = z • v := by
    funext q
    have := congrFun (congrFun hz q.1) q.2
    rw [applyMap_apply] at this
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, v]
    rw [this, Matrix.smul_apply]
  obtain ⟨p, hp⟩ : ∃ p, v p ≠ 0 := by
    by_contra h; push Not at h
    exact hY (funext fun i => funext fun j => h (i, j))
  by_contra h
  push Not at h
  set S := ∑ q, ‖v q‖
  have hvp : 0 < ‖v p‖ := norm_pos_iff.mpr hp
  have hT := tendsto_pow_atTop_atTop_of_one_lt h
  obtain ⟨n, hn, hn1⟩ := ((hT.eventually_gt_atTop (S / ‖v p‖)).and
    (eventually_ge_atTop 1)).exists
  have hpow : (t ^ n) *ᵥ v = z ^ n • v := by
    clear hn hn1
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, htv, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
        mul_comm]
  have hb : ‖z‖ ^ n * ‖v p‖ ≤ S := by
    have e := congrFun hpow p
    rw [Pi.smul_apply, smul_eq_mul] at e
    calc ‖z‖ ^ n * ‖v p‖ = ‖((t ^ n) *ᵥ v) p‖ := by rw [e, norm_mul, norm_pow]
      _ ≤ ∑ q, ‖(t ^ n) p q * v q‖ := norm_sum_le _ _
      _ ≤ ∑ q, ‖v q‖ := Finset.sum_le_sum fun q _ => by
          rw [norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (entry_le (uc_pow ht n hn1) p q)
  rw [div_lt_iff₀ hvp] at hn
  linarith

lemma hsNorm_eq' (M : Map d) : hsNorm M = ‖M‖ := by
  rw [Matrix.frobenius_norm_def, hsNorm, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [Complex.normSq_eq_norm_sq, Real.rpow_two]

lemma prim {ε : ℝ} {t : Map d} (ht : UnitalChannel t) (hs : UnitalChannel (t * depolarizingMixture d (1 - ε)))
    (hε0 : 0 < ε) (hε1 : ε < 1) : Primitive (t * depolarizingMixture d (1 - ε)) := by
  set s := t * depolarizingMixture d (1 - ε)
  unfold Primitive scalars
  apply le_antisymm
  · rw [peripheral, Submodule.span_le]
    rintro X ⟨a, ha, hX⟩
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    set c : ℂ := X.trace / d
    set Y := X - c • (1 : Mat d)
    have hsX : applyMap s X = applyMap t ((((1 - ε : ℝ)) : ℂ) • X +
        (((1 - (1 - ε) : ℝ) : ℂ) * (d : ℂ)⁻¹ * X.trace) • (1 : Mat d)) := by
      rw [am_mul, x8_mix_apply]
    have htrX : a * X.trace = X.trace := by
      rw [← smul_eq_mul, ← Matrix.trace_smul, ← hX, tr_pres hs]
    have hac : a * c = c := by
      simp only [c]; rw [← mul_div_assoc, htrX]
    have htrY : Y.trace = 0 := by
      simp only [Y, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, c,
        smul_eq_mul]
      by_cases hd : (d : ℂ) = 0
      · have : d = 0 := by exact_mod_cast hd
        subst this; simp [Matrix.trace]
      · field_simp; ring
    have hsY : applyMap s Y = a • Y := by
      simp only [Y]
      rw [am_sub, am_smul, hs.2, hX, smul_sub, smul_smul, hac]
    have hsY' : applyMap s Y = (((1 - ε : ℝ)) : ℂ) • applyMap t Y := by
      rw [am_mul, x8_mix_apply, htrY, mul_zero, zero_smul, add_zero, am_smul]
    have hne : (((1 - ε : ℝ)) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; linarith
    have htY : applyMap t Y = (a / (((1 - ε : ℝ)) : ℂ)) • Y := by
      rw [div_eq_inv_mul, mul_smul, ← hsY, hsY', smul_smul, inv_mul_cancel₀ hne, one_smul]
    have hY : Y = 0 := by
      by_contra hY0
      have h1 := eig_le ht hY0 htY
      rw [norm_div, ha, Complex.norm_real, Real.norm_of_nonneg (by linarith)] at h1
      rw [div_le_one (by linarith)] at h1
      linarith
    refine ⟨c, ?_⟩
    have : X - c • (1 : Mat d) = 0 := hY
    exact (sub_eq_zero.mp this).symm
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨1, by simp, by rw [hs.2, one_smul]⟩

theorem x8_dens {d : ℕ} (hd : 0 < d) (t : Map d) (ht : UnitalChannel t)
    (e : ℝ) (he : 0 < e) :
    ∃ s : Map d, UnitalChannel s ∧ Eventually EB s ∧ hsNorm (s - t) < e := by
  haveI : NeZero d := ⟨hd.ne'⟩
  set H := hsNorm (depolarizing d - t)
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  set ε := min (1 / 2) (e / (2 * (H + 1)))
  have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hs : UnitalChannel (t * depolarizingMixture d (1 - ε)) :=
    uc_mul ht (x8_mix_unital hd (1 - ε) (by linarith) (by linarith))
  refine ⟨t * depolarizingMixture d (1 - ε), hs, ?_, ?_⟩
  · obtain ⟨n0, hn0, h⟩ := corollary_6_15 hd _ hs (prim ht hs hε0 hε1)
    exact ⟨n0, hn0, fun n hn => x8_MTD_EB hd (h n hn)⟩
  · have e1 : t * depolarizingMixture d (1 - ε) - t = ε • (depolarizing d - t) := by
      unfold depolarizingMixture
      rw [mul_add, mul_smul_comm, mul_smul_comm, mul_one, mul_dep (un_of ht)]
      module
    rw [e1, hsNorm_eq', norm_smul, Real.norm_of_nonneg hε0.le, ← hsNorm_eq']
    have h2 : ε ≤ e / (2 * (H + 1)) := min_le_right _ _
    calc ε * H ≤ e / (2 * (H + 1)) * H := mul_le_mul_of_nonneg_right h2 hH
      _ < e := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith

end X8DN

end QAlgorithms.Papers.Independent.Information100.P26

open QAlgorithms.Papers.Independent.Information100.P26 in
theorem solution {d : ℕ} (hd : 0 < d) (t : Map d) (ht : UnitalChannel t)
    (e : ℝ) (he : 0 < e) :
    ∃ s : Map d, UnitalChannel s ∧ Eventually EB s ∧ hsNorm (s - t) < e :=
  QAlgorithms.Papers.Independent.Information100.P26.X8DN.x8_dens hd t ht e he
