-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P26.remark_3_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T22:44:42.525416+00:00
-- url     : https://prove2.me/submissions/138953ce-972d-423e-b9db-ead32be46d00

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



theorem x8_choi_ad_vmv {d : ℕ} (u v : Fin d → ℂ) :
    choi (ad (Matrix.vecMulVec u v)) =
      Matrix.kronecker (Matrix.vecMulVec u (star u)) (Matrix.vecMulVec v (star v)) := by
  ext p q
  simp [choi, ad, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.vecMulVec_apply]
  ring

theorem x8_choi_sum {d : ℕ} {ι : Type*} [Fintype ι] (f : ι → Map d) :
    choi (∑ i, f i) = ∑ i, choi (f i) := by
  ext p q; simp [choi, Matrix.sum_apply]

theorem x8_EB_of {d : ℕ} (hd : 0 < d) {ι : Type*} [Fintype ι] (u v : ι → Fin d → ℂ) :
    EB (∑ i, ad (Matrix.vecMulVec (u i) (v i))) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  unfold EB
  rw [x8_choi_sum]
  simp only [x8_choi_ad_vmv]
  exact x8_sep _ _ (fun i => Matrix.posSemidef_vecMulVec_self_star _)
    (fun i => Matrix.posSemidef_vecMulVec_self_star _)

theorem x8_of_EB {d : ℕ} {f : Map d} (h : EB f) :
    ∃ (ι : Type) (_ : Fintype ι) (u v : ι → Fin d → ℂ),
      f = ∑ i, ad (Matrix.vecMulVec (u i) (v i)) := by
  obtain ⟨q, w, A, B, hw, hAB, hchoi⟩ := h
  choose mA a ha using fun j => Matrix.posSemidef_iff_eq_sum_vecMulVec.1 (hAB j).1.1
  choose mB b hb using fun j => Matrix.posSemidef_iff_eq_sum_vecMulVec.1 (hAB j).2.1
  refine ⟨(j : Fin q) × Fin (mA j) × Fin (mB j), inferInstance,
    fun x => (((Real.sqrt (w x.1) : ℝ) : ℂ)) • a x.1 x.2.1, fun x => b x.1 x.2.2, ?_⟩
  have : choi f = choi (∑ x : (j : Fin q) × Fin (mA j) × Fin (mB j),
      ad (Matrix.vecMulVec ((((Real.sqrt (w x.1) : ℝ) : ℂ)) • a x.1 x.2.1) (b x.1 x.2.2))) := by
    rw [hchoi, x8_choi_sum]
    simp only [x8_choi_ad_vmv]
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ha j, hb j, Fintype.sum_prod_type]
    ext p r
    simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      Finset.sum_mul, star_mul', Complex.star_def, Complex.conj_ofReal]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    have hw' : ((Real.sqrt (w j) : ℝ) : ℂ) * ((Real.sqrt (w j) : ℝ) : ℂ) = (w j : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hw j)]
    linear_combination (a j k p.1 * conj (a j k r.1) * (b j l p.2 * conj (b j l r.2))) * hw'.symm
  exact congrArg choi this

theorem x8_rank_one_fac {d : ℕ} (B : Mat d) (h : B.rank = 1) :
    ∃ u v : Fin d → ℂ, B = Matrix.vecMulVec u v := by
  rw [Matrix.rank_eq_finrank_span_cols] at h
  obtain ⟨w, -, hw⟩ := finrank_eq_one_iff'.1 h
  choose c hc using fun j : Fin d => hw ⟨Bᵀ j, Submodule.subset_span ⟨j, rfl⟩⟩
  refine ⟨(w : Fin d → ℂ), c, ?_⟩
  ext i j
  have := congrArg (fun x : Submodule.span ℂ (Set.range Bᵀ) => (x : Fin d → ℂ) i) (hc j)
  simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, Matrix.transpose_apply] at this
  rw [Matrix.vecMulVec_apply, ← this, mul_comm]

theorem x8_rank_vmv {d : ℕ} (u v : Fin d → ℂ) (h : Matrix.vecMulVec u v ≠ 0) :
    (Matrix.vecMulVec u v).rank = 1 := by
  refine le_antisymm (Matrix.rank_vecMulVec_le u v) ?_
  by_contra hlt
  push Not at hlt
  have h0 : (Matrix.vecMulVec u v).rank = 0 := by omega
  rw [Matrix.rank_eq_finrank_span_cols, Submodule.finrank_eq_zero] at h0
  apply h
  ext i j
  have : (Matrix.vecMulVec u v)ᵀ j ∈ (⊥ : Submodule ℂ (Fin d → ℂ)) := by
    rw [← h0]; exact Submodule.subset_span ⟨j, rfl⟩
  rw [Submodule.mem_bot] at this
  have := congrFun this i
  simpa using this

theorem x8_ad_zero {d : ℕ} : ad (0 : Mat d) = 0 := by ext p q; simp [ad]

theorem x8_ad_smul {d : ℕ} (c : ℝ) (u v : Fin d → ℂ) :
    ad (Matrix.vecMulVec ((c : ℂ) • u) v) = (c ^ 2) • ad (Matrix.vecMulVec u v) := by
  ext p q
  simp [ad, Matrix.vecMulVec_apply, Complex.real_smul]
  ring

theorem x8_rem32 {d : ℕ} (hd : 0 < d) (t : Map d) :
    faceSpan t = Submodule.span ℝ {s : Map d | EB s ∧ ∃ a : ℝ, 0 < a ∧ EB (a • t - s)} := by
  apply le_antisymm
  · unfold faceSpan
    apply Submodule.span_le.2
    rintro s ⟨B, hB, rfl, hEB⟩
    apply Submodule.subset_span
    refine ⟨?_, 1, one_pos, by rw [one_smul]; exact hEB⟩
    obtain ⟨u, v, rfl⟩ := x8_rank_one_fac B hB
    simpa using x8_EB_of hd (fun _ : Unit => u) (fun _ => v)
  · apply Submodule.span_le.2
    rintro s ⟨hs, a, ha, hts⟩
    obtain ⟨ι, _, u, v, rfl⟩ := x8_of_EB hs
    obtain ⟨κ, _, u', v', hC⟩ := x8_of_EB hts
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases h0 : Matrix.vecMulVec (u i) (v i) = 0
    · rw [h0, x8_ad_zero]; exact Submodule.zero_mem _
    set c : ℝ := (Real.sqrt a)⁻¹ with hc
    have hc2 : c ^ 2 = a⁻¹ := by rw [hc, inv_pow, Real.sq_sqrt ha.le]
    have hB'0 : Matrix.vecMulVec ((c : ℂ) • u i) (v i) ≠ 0 := by
      intro h; apply h0
      have hcne : (c : ℂ) ≠ 0 := by
        rw [hc]; exact_mod_cast inv_ne_zero (Real.sqrt_pos.2 ha).ne'
      ext p q
      have := congrFun (congrFun h p) q
      simp [Matrix.vecMulVec_apply, hcne] at this
      simp [Matrix.vecMulVec_apply, this]
    have hEB' : EB (t - ad (Matrix.vecMulVec ((c : ℂ) • u i) (v i))) := by
      have key : t - ad (Matrix.vecMulVec ((c : ℂ) • u i) (v i)) =
          ∑ x : κ ⊕ ι, ad (Matrix.vecMulVec
            (Sum.elim (fun k => (c : ℂ) • u' k) (fun i' => if i' = i then 0 else (c : ℂ) • u i') x)
            (Sum.elim v' v x)) := by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, x8_ad_smul, hc2]
        have hif : ∀ i', ad (Matrix.vecMulVec (if i' = i then 0 else (c : ℂ) • u i') (v i')) =
            a⁻¹ • ad (Matrix.vecMulVec (u i') (v i')) -
              if i' = i then a⁻¹ • ad (Matrix.vecMulVec (u i) (v i)) else 0 := by
          intro i'
          split_ifs with h
          · subst h; rw [Matrix.zero_vecMulVec, x8_ad_zero, sub_self]
          · rw [x8_ad_smul, hc2, sub_zero]
        simp only [hif, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        rw [← Finset.smul_sum, ← Finset.smul_sum, ← hC, smul_sub, smul_smul, inv_mul_cancel₀ ha.ne',
          one_smul]
        abel
      rw [key]
      exact x8_EB_of hd _ _
    have hgen : ad (Matrix.vecMulVec ((c : ℂ) • u i) (v i)) ∈ faceGenerators t :=
      ⟨_, x8_rank_vmv _ _ hB'0, rfl, hEB'⟩
    have : ad (Matrix.vecMulVec (u i) (v i)) = a • ad (Matrix.vecMulVec ((c : ℂ) • u i) (v i)) := by
      rw [x8_ad_smul, hc2, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hgen)

end QAlgorithms.Papers.Independent.Information100.P26

open QAlgorithms.Papers.Independent.Information100.P26 in
theorem solution {d : ℕ} (hd : 0 < d) (t : Map d) (ht : t ∈ UEBTP d) :
    faceSpan t = Submodule.span ℝ
      {s : Map d | EB s ∧ ∃ a : ℝ, 0 < a ∧ EB (a • t - s)} :=
  x8_rem32 hd t
