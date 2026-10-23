-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P26.remark_6_10
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T22:52:18.468547+00:00
-- url     : https://prove2.me/submissions/948983ed-1a04-4bd1-851d-9610fba61435

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

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



theorem x8_am_mul {d : ℕ} (s r : Map d) (X : Mat d) :
    applyMap (s * r) X = applyMap s (applyMap r X) := by
  ext i j
  simp only [x8_applyMap, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
  ring

theorem x8_am_one {d : ℕ} (X : Mat d) : applyMap (1 : Map d) X = X := by
  ext i j
  rw [x8_applyMap]
  simp [Matrix.one_apply, Prod.ext_iff, ite_and, Finset.sum_ite_eq', Fintype.sum_prod_type]

theorem x8_am_ad {d : ℕ} (B : Mat d) (X : Mat d) : applyMap (ad B) X = B * X * Bᴴ := by
  ext i j
  rw [x8_applyMap]
  simp only [ad, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
    Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

def x8Good {d : ℕ} (s : Map d) : Prop :=
  (∀ X : Mat d, X.PosSemidef → (applyMap s X).PosSemidef) ∧
    (∀ X : Mat d, (applyMap s X).trace = X.trace) ∧ applyMap s 1 = 1

theorem x8_good_mul {d : ℕ} {s r : Map d} (hs : x8Good s) (hr : x8Good r) : x8Good (s * r) := by
  refine ⟨fun X hX => ?_, fun X => ?_, ?_⟩
  · rw [x8_am_mul]; exact hs.1 _ (hr.1 _ hX)
  · rw [x8_am_mul, hs.2.1, hr.2.1]
  · rw [x8_am_mul, hr.2.2, hs.2.2]

theorem x8_good_one {d : ℕ} : x8Good (1 : Map d) :=
  ⟨fun X hX => by rw [x8_am_one]; exact hX, fun X => by rw [x8_am_one], x8_am_one 1⟩

theorem x8_good_pow {d : ℕ} {s : Map d} (hs : x8Good s) (n : ℕ) : x8Good (s ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact x8_good_one
  | succ n ih => rw [pow_succ]; exact x8_good_mul ih hs

theorem x8_good_ad {d : ℕ} (W : Mat d) (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    x8Good (ad W) := by
  have h1 : W * Wᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hW
  have h2 : Wᴴ * W = 1 := Matrix.mem_unitaryGroup_iff'.1 hW
  refine ⟨fun X hX => ?_, fun X => ?_, ?_⟩
  · rw [x8_am_ad]; exact hX.mul_mul_conjTranspose_same W
  · rw [x8_am_ad, Matrix.trace_mul_cycle, h2, Matrix.one_mul]
  · rw [x8_am_ad, Matrix.mul_one, h1]

theorem x8_good_of_unital {d : ℕ} {t : Map d} (ht : UnitalChannel t) : x8Good t := by
  obtain ⟨⟨m, E, hE, hact⟩, hunit⟩ := ht
  refine ⟨fun X hX => ?_, fun X => ?_, hunit⟩
  · rw [hact, krausApply]
    exact Matrix.posSemidef_sum _ fun j _ => hX.mul_mul_conjTranspose_same (E j)
  · rw [hact, krausApply, Matrix.trace_sum]
    simp only [Matrix.trace_mul_cycle (E _) X]
    rw [← Matrix.trace_sum, ← Finset.sum_mul]
    unfold IsKrausFamily at hE
    rw [hE, Matrix.one_mul]

def x8Pc {d : ℕ} (σ : Equiv.Perm (Fin d)) : Mat d := fun a b => if σ a = b then 1 else 0

theorem x8_sandwich_entry {d : ℕ} (s : Map d) (p q : Fin d × Fin d) :
    (dephasing d * s * dephasing d) p q = if p.1 = p.2 ∧ q.1 = q.2 then s p q else 0 := by
  simp only [Matrix.mul_apply, x8_deph_apply, ite_mul, zero_mul, one_mul, mul_ite, mul_zero,
    mul_one]
  by_cases h : p.1 = p.2 ∧ q.1 = q.2
  · rw [if_pos h]
    rw [Finset.sum_eq_single q]
    · rw [if_pos ⟨h.2, rfl⟩, Finset.sum_eq_single p]
      · simp [h.1]
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    · intro b _ hb; simp [hb]
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero; intro r _
    split_ifs with h1
    · apply Finset.sum_eq_zero; intro r' _
      split_ifs with h2
      · exfalso; apply h; rcases h1 with ⟨h1a, rfl⟩; exact ⟨h2.1, h1a⟩
      · rfl
    · rfl

theorem x8_adP_entry {d : ℕ} (σ : Equiv.Perm (Fin d)) (p q : Fin d × Fin d) :
    (ad (x8Pc σ) * dephasing d) p q = if p.1 = p.2 ∧ q.1 = q.2 ∧ σ p.1 = q.1 then 1 else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single q]
  · simp only [ad, x8Pc, x8_deph_apply]
    by_cases hq : q.1 = q.2
    · by_cases h1 : σ p.1 = q.1
      · by_cases h2 : p.1 = p.2
        · simp [hq, h1, h2]
        · have : σ p.2 ≠ q.2 := fun h => h2 (σ.injective (h1.trans (hq.trans h.symm)))
          simp [hq, h1, h2, this]
      · simp [h1]
    · simp [hq]
  · intro b _ hb; simp only [x8_deph_apply]; rw [if_neg]; · simp
    rintro ⟨-, h⟩; exact hb h
  · simp

theorem x8_single_psd {d : ℕ} (j : Fin d) : (Matrix.single j j (1 : ℂ)).PosSemidef := by
  have : Matrix.single j j (1 : ℂ) = Matrix.vecMulVec (Pi.single j 1) (star (Pi.single j 1)) := by
    ext a b
    by_cases ha : a = j <;> by_cases hb : b = j <;>
      simp [Matrix.single_apply, Matrix.vecMulVec_apply, Pi.single_apply, ha, hb, eq_comm] <;>
      intros <;> simp_all [eq_comm]
  rw [this]; exact Matrix.posSemidef_vecMulVec_self_star _

theorem x8_s_diag {d : ℕ} (s : Map d) (i j : Fin d) :
    s (i, i) (j, j) = applyMap s (Matrix.single j j 1) i i := by
  rw [x8_applyMap, Finset.sum_eq_single (j, j)]
  · simp
  · intro b _ hb; rw [Matrix.single_apply, if_neg, mul_zero]
    rintro ⟨h1, h2⟩; exact hb (Prod.ext h1.symm h2.symm)
  · simp

theorem x8_sandwich {d : ℕ} {s : Map d} (hs : x8Good s) :
    ∃ w : Equiv.Perm (Fin d) → ℝ, (∀ σ, 0 ≤ w σ) ∧ ∑ σ, w σ = 1 ∧
      dephasing d * s * dephasing d = ∑ σ, w σ • (ad (x8Pc σ) * dephasing d) := by
  let P : Matrix (Fin d) (Fin d) ℝ := fun i j => (s (i, i) (j, j)).re
  have hreal : ∀ i j, s (i, i) (j, j) = ((P i j : ℝ) : ℂ) ∧ 0 ≤ P i j := by
    intro i j
    have h0 : 0 ≤ s (i, i) (j, j) := by
      have := (hs.1 _ (x8_single_psd j)).diag_nonneg (i := i)
      rwa [← x8_s_diag] at this
    obtain ⟨hre, him⟩ := Complex.nonneg_iff.1 h0
    exact ⟨Complex.ext rfl (by simp [← him]), hre⟩
  have hrow : ∀ i, ∑ j, s (i, i) (j, j) = 1 := by
    intro i
    have := congrFun (congrFun hs.2.2 i) i
    rw [x8_applyMap, Matrix.one_apply_eq] at this
    rw [← this, Fintype.sum_prod_type]
    simp [Matrix.one_apply, Finset.sum_ite_eq']
  have hcol : ∀ j, ∑ i, s (i, i) (j, j) = 1 := by
    intro j
    have := hs.2.1 (Matrix.single j j 1)
    simp only [x8_s_diag]
    rw [Matrix.trace] at this
    simp only [Matrix.diag] at this
    rw [this]; simp [Matrix.trace, Matrix.single_apply]
  have hP : P ∈ doublyStochastic ℝ (Fin d) := by
    refine ⟨fun i j => (hreal i j).2, ?_, ?_⟩
    · ext i
      simp only [Matrix.mulVec, dotProduct, Pi.one_apply, mul_one]
      apply Complex.ofReal_injective
      push_cast
      rw [← hrow i]
      exact Finset.sum_congr rfl fun j _ => (hreal i j).1.symm
    · ext j
      simp only [Matrix.vecMul, dotProduct, Pi.one_apply, one_mul]
      apply Complex.ofReal_injective
      push_cast
      rw [← hcol j]
      exact Finset.sum_congr rfl fun i _ => (hreal i j).1.symm
  obtain ⟨w, hw0, hw1, hw⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hP
  refine ⟨w, hw0, hw1, ?_⟩
  ext p q
  rw [x8_sandwich_entry, Matrix.sum_apply]
  simp only [Matrix.smul_apply, x8_adP_entry, Complex.real_smul, mul_ite, mul_one, mul_zero]
  by_cases h : p.1 = p.2 ∧ q.1 = q.2
  · obtain ⟨p1, p2⟩ := p
    obtain ⟨q1, q2⟩ := q
    simp only at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [true_and, if_true]
    rw [(hreal p1 q1).1]
    have := congrFun (congrFun hw p1) q1
    rw [← this, Matrix.sum_apply]
    push_cast
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    split_ifs <;> simp
  · rw [if_neg h]
    symm; apply Finset.sum_eq_zero; intro σ _
    rw [if_neg]; rintro ⟨h1, h2, -⟩; exact h ⟨h1, h2⟩

theorem x8_MTD_of {d : ℕ} {ι : Type*} [Fintype ι] (p : ι → ℝ) (U V : ι → Unitary d)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) : MTD (∑ i, p i • beta (U i) (V i)) := by
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun n => p (e.symm n), fun n => U (e.symm n), fun n => V (e.symm n),
    fun n => hp _, ?_, ?_⟩
  · rw [← hs]; exact e.symm.sum_comp p
  · exact (e.symm.sum_comp (fun i => p i • beta (U i) (V i))).symm

theorem x8_ad_mul {d : ℕ} (A B : Mat d) : ad A * ad B = ad (A * B) := by
  ext p q
  simp only [ad, Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem x8_Pc_unitary {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    x8Pc σ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a b
  simp only [Matrix.mul_apply, Matrix.star_apply, x8Pc, Matrix.one_apply]
  by_cases h : a = b
  · subst h; simp [Finset.sum_ite_eq]
  · have : σ a ≠ σ b := fun h' => h (σ.injective h')
    simp [h, apply_ite (star : ℂ → ℂ)]

theorem x8_beta_s_beta {d : ℕ} {s : Map d} (U V U' V' : Unitary d) (w : Equiv.Perm (Fin d) → ℝ)
    (hw : dephasing d * (ad (V : Mat d)ᴴ * s * ad (U' : Mat d)) * dephasing d =
      ∑ σ, w σ • (ad (x8Pc σ) * dephasing d)) :
    beta U V * s * beta U' V' =
      ∑ σ, w σ • beta (⟨(U : Mat d) * x8Pc σ, Submonoid.mul_mem _ U.2 (x8_Pc_unitary σ)⟩ : Unitary d) V' := by
  have : beta U V * s * beta U' V' =
      ad (U : Mat d) * (dephasing d * (ad (V : Mat d)ᴴ * s * ad (U' : Mat d)) * dephasing d) *
        ad (V' : Mat d)ᴴ := by
    simp only [beta, mul_assoc]
  rw [this, hw, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  simp only [beta, ← mul_assoc, x8_ad_mul]

theorem x8_MTD_comp {d : ℕ} {m s m' : Map d} (hm : MTD m) (hs : x8Good s) (hm' : MTD m') :
    MTD (m * s * m') := by
  obtain ⟨n, p, U, V, hp, hp1, rfl⟩ := hm
  obtain ⟨n', q, U', V', hq, hq1, rfl⟩ := hm'
  have hgood : ∀ x : Fin n × Fin n', x8Good (ad ((V x.1 : Mat d))ᴴ * s * ad (U' x.2 : Mat d)) :=
    fun x => x8_good_mul (x8_good_mul (x8_good_ad _ (Unitary.star_mem (V x.1).2)) hs)
      (x8_good_ad _ (U' x.2).2)
  choose w hw0 hw1 hweq using fun x => x8_sandwich (hgood x)
  have key : (∑ j, p j • beta (U j) (V j)) * s * (∑ l, q l • beta (U' l) (V' l)) =
      ∑ x : Fin n × Fin n' × Equiv.Perm (Fin d), (p x.1 * q x.2.1 * w (x.1, x.2.1) x.2.2) •
        beta (⟨(U x.1 : Mat d) * x8Pc x.2.2, Submonoid.mul_mem _ (U x.1).2 (x8_Pc_unitary _)⟩ :
          Unitary d) (V' x.2.1) := by
    rw [Finset.sum_mul, Finset.sum_mul, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, x8_beta_s_beta _ _ _ _ _ (hweq (j, l)),
      Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_smul, smul_smul]
  rw [key]
  refine x8_MTD_of _ _ _ (fun x => mul_nonneg (mul_nonneg (hp _) (hq _)) (hw0 _ _)) ?_
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, ← Finset.mul_sum, hw1, mul_one]
  rw [hq1]; simp [hp1]

theorem x8_rem610 {d : ℕ} (t : Map d) (ht : UnitalChannel t) :
    Eventually MTD t ↔ ∃ n0 : ℕ, 1 ≤ n0 ∧ MTD (t ^ n0) := by
  constructor
  · rintro ⟨n0, h1, h⟩; exact ⟨n0, h1, h n0 le_rfl⟩
  · rintro ⟨n0, h1, hm⟩
    refine ⟨2 * n0, by omega, fun n hn => ?_⟩
    have : t ^ n = t ^ n0 * t ^ (n - 2 * n0) * t ^ n0 := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [this]
    exact x8_MTD_comp hm (x8_good_pow (x8_good_of_unital ht) _) hm

end QAlgorithms.Papers.Independent.Information100.P26

open QAlgorithms.Papers.Independent.Information100.P26 in
theorem solution {d : ℕ} (hd : 0 < d) (t : Map d) (ht : UnitalChannel t) :
    Eventually MTD t ↔ ∃ n0 : ℕ, 1 ≤ n0 ∧ MTD (t^n0) :=
  x8_rem610 t ht
