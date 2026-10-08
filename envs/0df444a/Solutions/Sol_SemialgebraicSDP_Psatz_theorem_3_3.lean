-- Prove2me | solution 1 for SemialgebraicSDP.Psatz.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:27:55.460221+00:00
-- url     : https://prove2.me/submissions/068be97c-3a9c-41c9-825e-eb70935bd72a

import Mathlib
import Definitions.Def_SemialgebraicSDP_Psatz_Gram

open SemialgebraicSDP.Psatz MvPolynomial

private def slackEquiv (n d : ℕ) :
    Mon n d ≃ {a : Option (Fin n) → ℕ // ∑ i, a i = d} where
  toFun a := ⟨fun i => match i with
    | none => d - ∑ j, (a.1 j : ℕ)
    | some j => (a.1 j : ℕ), by
      simp only [Fintype.sum_option]
      exact Nat.sub_add_cancel a.2⟩
  invFun a := ⟨fun j => ⟨a.1 (some j), by
    have he := a.2
    rw [Fintype.sum_option] at he
    have hb := Finset.single_le_sum (fun k _ => Nat.zero_le (a.1 (some k)))
      (Finset.mem_univ j)
    omega⟩, by
      have he := a.2
      rw [Fintype.sum_option] at he
      dsimp
      omega⟩
  left_inv a := by
    apply Subtype.ext
    funext j
    rfl
  right_inv a := by
    apply Subtype.ext
    funext i
    cases i with
    | none =>
      have he := a.2
      rw [Fintype.sum_option] at he
      dsimp
      omega
    | some j => rfl

theorem SemialgebraicSDP.Psatz.monomial_vector_card (n d : ℕ) :
    Fintype.card (Mon n d) = (n + d).choose d := by
  classical
  let e := (slackEquiv n d).trans (Sym.equivNatSumOfFintype (Option (Fin n)) d).symm
  rw [Fintype.card_congr e, Sym.card_sym_eq_choose]
  simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

open SemialgebraicSDP.Psatz MvPolynomial
open scoped MatrixOrder
set_option maxHeartbeats 2000000

theorem SemialgebraicSDP.Psatz.gram_psd_isSumSq {n d : ℕ}
    (Q : Matrix (Mon n d) (Mon n d) ℝ) (hQ : Q.PosSemidef) :
    IsSumSq (gramPoly Q) := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hQ.nonneg
  have he : gramPoly Q =
      ∑ k, (∑ a, C (B k a) * monVec n d a) ^ 2 := by
    rw [hB]
    simp only [gramPoly, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, star_trivial, map_sum, map_mul, pow_two,
      Finset.mul_sum, Finset.sum_mul]
    conv_lhs =>
      arg 2
      ext a
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    congr 1
    funext k
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [he]
  exact IsSumSq.sum_sq _ _

open SemialgebraicSDP.Psatz MvPolynomial
open scoped MonomialOrder

private theorem add_positive_leading {n : ℕ} (m : MonomialOrder (Fin n))
    (a b : MvPolynomial (Fin n) ℝ)
    (ha : 0 ≤ m.leadingCoeff a) (hb : 0 ≤ m.leadingCoeff b) :
    0 ≤ m.leadingCoeff (a + b) ∧
      m.degree a ≼[m] m.degree (a + b) ∧ m.degree b ≼[m] m.degree (a + b) := by
  classical
  by_cases ha0 : a = 0
  · simp [ha0, hb]
  by_cases hb0 : b = 0
  · simp [hb0, ha]
  rcases lt_trichotomy (m.toSyn (m.degree a)) (m.toSyn (m.degree b)) with hlt | heq | hgt
  · rw [m.degree_add_eq_right_of_lt hlt]
    refine ⟨?_, le_of_lt hlt, le_rfl⟩
    rw [add_comm, m.leadingCoeff_add_of_lt hlt]
    exact hb
  · have he : m.degree a = m.degree b := m.toSyn.injective heq
    have hpos : 0 < m.leadingCoeff a :=
      lt_of_le_of_ne ha (Ne.symm ((m.leadingCoeff_ne_zero_iff).mpr ha0))
    have hec : coeff (m.degree a) b = m.leadingCoeff b :=
      congrArg (fun e => coeff e b) he
    have hc : coeff (m.degree a) (a + b) ≠ 0 := by
      rw [coeff_add, hec]
      change m.leadingCoeff a + m.leadingCoeff b ≠ 0
      linarith
    have hd : m.degree (a + b) = m.degree a := by
      apply m.toSyn.injective
      apply le_antisymm
      · simpa [he] using (m.degree_add_le (f := a) (g := b))
      · exact m.le_degree (mem_support_iff.mpr hc)
    rw [hd]
    refine ⟨?_, le_rfl, by rw [← he]⟩
    change 0 ≤ coeff (m.degree (a + b)) (a + b)
    rw [hd, coeff_add, hec]
    exact add_nonneg ha hb
  · rw [m.degree_add_of_lt hgt]
    refine ⟨?_, le_rfl, le_of_lt hgt⟩
    rw [m.leadingCoeff_add_of_lt hgt]
    exact ha

private theorem sos_leading_nonneg {n : ℕ} (m : MonomialOrder (Fin n))
    {a : MvPolynomial (Fin n) ℝ} (ha : IsSumSq a) : 0 ≤ m.leadingCoeff a := by
  induction ha with
  | zero => simp
  | sq_add a hs ih =>
    exact (add_positive_leading m (a * a) _ (by
      rw [m.leadingCoeff_mul]
      exact mul_self_nonneg _) ih).1

private theorem sos_add_degree_bounds {n : ℕ} (a b : MvPolynomial (Fin n) ℝ)
    (hb : IsSumSq b) :
    2 * a.totalDegree ≤ (a * a + b).totalDegree ∧
      b.totalDegree ≤ (a * a + b).totalDegree := by
  classical
  let m : MonomialOrder (Fin n) := MonomialOrder.degLex
  have h := add_positive_leading m (a * a) b
    (by rw [m.leadingCoeff_mul]; exact mul_self_nonneg _) (sos_leading_nonneg m hb)
  have ha := MvPolynomial.degLex_totalDegree_monotone h.2.1
  have hb' := MvPolynomial.degLex_totalDegree_monotone h.2.2
  refine ⟨?_, hb'⟩
  by_cases ha0 : a = 0
  · simp [ha0]
  · have he : (a * a).totalDegree = 2 * a.totalDegree := by
      rw [← degree_degLexDegree, m.degree_mul ha0 ha0]
      rw [map_add]
      change (MonomialOrder.degLex.degree a).degree +
        (MonomialOrder.degLex.degree a).degree = 2 * a.totalDegree
      rw [degree_degLexDegree]
      omega
    simpa [he] using ha

private def monOfFinsupp {n d : ℕ} (a : Fin n →₀ ℕ)
    (ha : a.sum (fun _ k => k) ≤ d) : Mon n d :=
  ⟨fun i => ⟨a i, by
    have h := Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
    rw [Finsupp.sum_fintype _ _ (by intro; rfl)] at ha
    omega⟩, by simpa [Finsupp.sum_fintype] using ha⟩

private theorem toFinsupp_monOfFinsupp {n d : ℕ} (a : Fin n →₀ ℕ)
    (ha : a.sum (fun _ k => k) ≤ d) : (monOfFinsupp a ha).toFinsupp = a := by
  ext i
  simp [Mon.toFinsupp, monOfFinsupp]

private theorem toFinsupp_injective {n d : ℕ} :
    Function.Injective (@Mon.toFinsupp n d) := by
  intro a b h
  apply Subtype.ext
  funext i
  apply Fin.ext
  have he := congrArg (fun t : Fin n →₀ ℕ => t i) h
  simpa [Mon.toFinsupp] using he

private theorem monomial_expansion {n d : ℕ} (a : MvPolynomial (Fin n) ℝ)
    (ha : a.totalDegree ≤ d) :
    a = ∑ α : Mon n d, C (coeff α.toFinsupp a) * monVec n d α := by
  classical
  ext μ
  by_cases hμ : μ.sum (fun _ k => k) ≤ d
  · let α := monOfFinsupp μ hμ
    have he : α.toFinsupp = μ := toFinsupp_monOfFinsupp μ hμ
    rw [coeff_sum]
    rw [Finset.sum_eq_single α]
    · simp [monVec, C_mul_monomial, he]
    · intro β _ hβ
      have hn : β.toFinsupp ≠ μ := by
        intro hh
        exact hβ (toFinsupp_injective (hh.trans he.symm))
      simp [monVec, C_mul_monomial, coeff_monomial, hn]
    · simp
  · have hc : coeff μ a = 0 := by
      apply coeff_eq_zero_of_totalDegree_lt
      change a.totalDegree < μ.sum (fun _ k => k)
      omega
    rw [hc, coeff_sum]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro α _
    have hn : α.toFinsupp ≠ μ := by
      intro he
      have hb : α.toFinsupp.sum (fun _ k => k) ≤ d := by
        simpa [Mon.toFinsupp, Finsupp.sum_fintype] using α.2
      exact hμ (he ▸ hb)
    simp [monVec, C_mul_monomial, coeff_monomial, hn]

private theorem square_gram {n d : ℕ} (a : MvPolynomial (Fin n) ℝ)
    (ha : a.totalDegree ≤ d) :
    ∃ Q : Matrix (Mon n d) (Mon n d) ℝ, Q.PosSemidef ∧ a * a = gramPoly Q := by
  classical
  let v : Mon n d → ℝ := fun α => coeff α.toFinsupp a
  refine ⟨Matrix.vecMulVec v v, ?_, ?_⟩
  · simpa using Matrix.posSemidef_vecMulVec_self_star v
  · have he := monomial_expansion a ha
    calc
      a * a = (∑ α, C (v α) * monVec n d α) * (∑ α, C (v α) * monVec n d α) :=
        congrArg₂ (· * ·) he he
      _ = gramPoly (Matrix.vecMulVec v v) := by
        simp only [gramPoly, Matrix.vecMulVec_apply, map_mul, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro α _
        apply Finset.sum_congr rfl
        intro β _
        ring

theorem SemialgebraicSDP.Psatz.isSumSq_exists_gram {n d : ℕ}
    (F : MvPolynomial (Fin n) ℝ) (hF : IsSumSq F) (hdeg : F.totalDegree ≤ 2 * d) :
    ∃ Q : Matrix (Mon n d) (Mon n d) ℝ, Q.PosSemidef ∧ F = gramPoly Q := by
  classical
  induction hF with
  | zero =>
    exact ⟨0, Matrix.PosSemidef.zero, by simp [gramPoly]⟩
  | @sq_add a b hb ih =>
    have hbounds := sos_add_degree_bounds a b hb
    have ha : a.totalDegree ≤ d := by omega
    obtain ⟨A, hA, heA⟩ := square_gram a ha
    obtain ⟨B, hB, heB⟩ := ih (hbounds.2.trans hdeg)
    refine ⟨A + B, hA.add hB, ?_⟩
    rw [heA, heB]
    simp [gramPoly, map_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem SemialgebraicSDP.Psatz.theorem_3_3 {n d : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (hdeg : F.totalDegree ≤ 2 * d) :
    (IsSumSq F ↔ ∃ Q : Matrix (Mon n d) (Mon n d) ℝ, Q.PosSemidef ∧ F = gramPoly Q) ∧
      Fintype.card (Mon n d) = (n + d).choose d := by
  refine ⟨⟨fun hF => SemialgebraicSDP.Psatz.isSumSq_exists_gram F hF hdeg, ?_⟩,
    SemialgebraicSDP.Psatz.monomial_vector_card n d⟩
  rintro ⟨Q, hQ, rfl⟩
  exact SemialgebraicSDP.Psatz.gram_psd_isSumSq Q hQ

theorem solution {n d : ℕ} (F : MvPolynomial (Fin n) ℝ)
    (hdeg : F.totalDegree ≤ 2 * d) :
    (IsSumSq F ↔ ∃ Q : Matrix (Mon n d) (Mon n d) ℝ, Q.PosSemidef ∧ F = gramPoly Q) ∧
      Fintype.card (Mon n d) = (n + d).choose d :=
  SemialgebraicSDP.Psatz.theorem_3_3 F hdeg

#print axioms solution
