-- Prove2me | solution 1 for QSVT19.Main.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T21:14:18.483598+00:00
-- url     : https://prove2.me/submissions/c09a0503-7b08-41ca-8dc5-ddf3ecbfe35b

import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ComputeDegree
import Definitions.Def_QSVT19_Main_Setting
import Theorems.Thm_QSVT19_Main_lemma_6
import Mathlib.Data.Complex.BigOperators

noncomputable section
open Polynomial QAlgorithms
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QSVTCert
lemma parity_add {P Q : ℂ[X]} {k : ℕ}
    (hP : HasParity P k) (hQ : HasParity Q k) : HasParity (P+Q) k := by
  simpa only [HasParity,add_comp,smul_add] using congrArg₂ (·+·) hP hQ
lemma parity_neg {P : ℂ[X]} {k : ℕ} (h : HasParity P k) : HasParity (-P) k := by
  simpa only [HasParity,neg_comp,smul_neg] using congrArg Neg.neg h
lemma parity_sub {P Q : ℂ[X]} {k : ℕ}
    (hP : HasParity P k) (hQ : HasParity Q k) : HasParity (P-Q) k := by
  simpa only [sub_eq_add_neg] using parity_add hP (parity_neg hQ)
lemma parity_mul {P Q : ℂ[X]} {k l : ℕ}
    (hP : HasParity P k) (hQ : HasParity Q l) : HasParity (P*Q) (k+l) := by
  dsimp [HasParity] at *
  rw [mul_comp,hP,hQ,pow_add,mul_smul_mul_comm]
lemma parity_shift (P : ℂ[X]) (k : ℕ) : HasParity P (k+2) ↔ HasParity P k := by
  simp [HasParity,pow_add]
lemma parity_X : HasParity (X : ℂ[X]) 1 := by simp [HasParity]
lemma parity_gap : HasParity (1-X^2 : ℂ[X]) 0 := by simp [HasParity]
lemma degree_mul_lt_right {P Q : ℝ[X]} {k l : ℕ}
    (hP : P.degree ≤ k) (hQ : Q.degree < l) : (P*Q).degree < (↑(k+l) : WithBot ℕ) := by
  by_cases hp : P = 0
  · simp [hp]
  by_cases hq : Q = 0
  · simp [hq]
  rw [degree_eq_natDegree hp] at hP
  rw [degree_eq_natDegree hq] at hQ
  rw [degree_mul,degree_eq_natDegree hp,degree_eq_natDegree hq]
  exact_mod_cast Nat.add_lt_add_of_le_of_lt (by exact_mod_cast hP) (by exact_mod_cast hQ)
lemma degree_gap_mul {P Q : ℝ[X]} {k l : ℕ}
    (hP : P.degree < k) (hQ : Q.degree < l) :
    ((1-X^2)*P*Q).degree ≤ (↑(k+l) : WithBot ℕ) := by
  by_cases hp : P = 0
  · simp [hp]
  by_cases hq : Q = 0
  · simp [hq]
  have hg : (1-X^2 : ℝ[X]) ≠ 0 := by intro h;have := congrArg (fun p : ℝ[X] => p.coeff 2) h;norm_num [coeff_one] at this
  have hd : (1-X^2 : ℝ[X]).degree = 2 := by compute_degree!
  rw [degree_eq_natDegree hp] at hP
  rw [degree_eq_natDegree hq] at hQ
  rw [degree_mul,degree_mul,hd,degree_eq_natDegree hp,degree_eq_natDegree hq]
  have hk : P.natDegree < k := by exact_mod_cast hP
  have hl : Q.natDegree < l := by exact_mod_cast hQ
  have h : 2 + P.natDegree + Q.natDegree ≤ k+l := by omega
  exact_mod_cast h
lemma certificate_mul (k l : ℕ) (A B C D E F : ℝ[X])
    (hA : A = B^2 + (1-X^2)*C^2) (hD : D = E^2 + (1-X^2)*F^2)
    (hB : B.degree ≤ k) (hC : C.degree < k)
    (hE : E.degree ≤ l) (hF : F.degree < l)
    (hpB : HasParity (B.map Complex.ofRealHom) k)
    (hpC : HasParity (C.map Complex.ofRealHom) (k+1))
    (hpE : HasParity (E.map Complex.ofRealHom) l)
    (hpF : HasParity (F.map Complex.ofRealHom) (l+1)) :
    A*D = (B*E-(1-X^2)*C*F)^2 + (1-X^2)*(B*F+C*E)^2 ∧
      (B*E-(1-X^2)*C*F).degree ≤ (↑(k+l) : WithBot ℕ) ∧ (B*F+C*E).degree < (↑(k+l) : WithBot ℕ) ∧
      HasParity ((B*E-(1-X^2)*C*F).map Complex.ofRealHom) (k+l) ∧
      HasParity ((B*F+C*E).map Complex.ofRealHom) (k+l+1) := by
  refine ⟨by rw [hA,hD];ring,?_,?_,?_,?_⟩
  · apply (degree_sub_le _ _).trans
    apply max_le
    · simpa using degree_mul_le_of_le hB hE
    · exact degree_gap_mul hC hF
  · apply (degree_add_le _ _).trans_lt
    apply max_lt
    · exact degree_mul_lt_right hB hF
    · rw [mul_comm C E,Nat.add_comm k l]
      exact degree_mul_lt_right hE hC
  · simp only [Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_one,Polynomial.map_pow,Polynomial.map_X]
    apply parity_sub (parity_mul hpB hpE)
    have h := parity_mul (parity_mul parity_gap hpC) hpF
    have he : 0+(k+1)+(l+1) = k+l+2 := by omega
    rw [he] at h
    exact (parity_shift _ _).mp h
  · simp only [Polynomial.map_add,Polynomial.map_mul]
    apply parity_add
    · simpa only [show k+(l+1)=k+l+1 by omega] using parity_mul hpB hpF
    · simpa only [show (k+1)+l=k+l+1 by omega] using parity_mul hpC hpE
end QSVTCert

noncomputable section
open Polynomial QAlgorithms
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QSVTReal
lemma neg_coeff (P : ℂ[X]) (i : ℕ) :
    (P.comp (-X)).coeff i = (-1:ℂ)^i * P.coeff i := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq => simp [add_comp, hp, hq, mul_add]
  | monomial n a =>
    simp only [monomial_comp, show (-X : ℂ[X]) = (-1:ℂ) • X by simp,
      _root_.smul_pow, coeff_C_mul, coeff_smul, smul_eq_mul, coeff_X_pow, coeff_monomial]
    by_cases e : n=i
    · subst i; simp [mul_comm]
    · simp only [if_neg e, if_neg (Ne.symm e), mul_zero]

lemma parity_coeff {P : ℂ[X]} {k i : ℕ} (h : HasParity P k)
    (hi : i%2 ≠ k%2) : P.coeff i = 0 := by
  have e := congrArg (fun p : ℂ[X] => p.coeff i) h
  simp only [neg_coeff, coeff_smul, smul_eq_mul] at e
  rw [neg_one_pow_eq_pow_mod_two i, neg_one_pow_eq_pow_mod_two k] at e
  rcases Nat.mod_two_eq_zero_or_one i with hmi|hmi <;>
    rcases Nat.mod_two_eq_zero_or_one k with hmk|hmk
  all_goals simp only [hmi,hmk,pow_zero,pow_one,one_mul,neg_one_mul] at e hi
  all_goals first | contradiction | linear_combination e/2 | linear_combination -e/2


open QSVT19.Main
lemma real_degree {P : ℂ[X]} {PR : ℝ[X]} (h : RePartEq P PR) : PR.degree ≤ P.degree := by
  apply (degree_le_iff_coeff_zero _ _).mpr
  intro n hn
  rw [← h n,coeff_eq_zero_of_degree_lt hn]
  rfl
lemma real_eval {P : ℂ[X]} {PR : ℝ[X]} (h : RePartEq P PR) (x : ℝ) :
    (P.eval (x:ℂ)).re = PR.eval x := by
  let n := max P.natDegree PR.natDegree + 1
  rw [eval_eq_sum_range' (n := n) (by dsimp [n];omega),
    eval_eq_sum_range' (n := n) (by dsimp [n];omega),Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Complex.ofReal_pow]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,h i]
lemma real_parity {P : ℂ[X]} {PR : ℝ[X]} {k : ℕ} (h : RePartEq P PR)
    (hp : HasParity P k) : HasParity (PR.map Complex.ofRealHom) k := by
  unfold HasParity
  ext n
  rw [neg_coeff,coeff_smul,coeff_map]
  by_cases hn : n%2 = k%2
  · rw [neg_one_pow_eq_pow_mod_two n,neg_one_pow_eq_pow_mod_two k,hn]
    rfl
  · have hz : PR.coeff n = 0 := by rw [← h n,parity_coeff hp hn];rfl
    simp [hz]
lemma eval_real (p : ℝ[X]) (x : ℝ) :
    (p.map Complex.ofRealHom).eval (x:ℂ) = ((p.eval x : ℝ) : ℂ) := by
  rw [eval_map]
  exact Polynomial.eval₂_at_apply (p := p) Complex.ofRealHom x
lemma square_even {p : ℝ[X]} {k : ℕ} (hp : HasParity (p.map Complex.ofRealHom) k) :
    (p^2).comp (-X) = p^2 := by
  have he := QSVTCert.parity_mul hp hp
  have hs : (-1 : ℂ)^(k+k) = 1 := by rw [← two_mul,pow_mul];simp
  change ((p.map Complex.ofRealHom)*(p.map Complex.ofRealHom)).comp (-X) =
    (-1:ℂ)^(k+k) • ((p.map Complex.ofRealHom)*(p.map Complex.ofRealHom)) at he
  rw [hs,one_smul] at he
  apply Polynomial.map_injective Complex.ofRealHom Complex.ofReal_injective
  simpa only [Polynomial.map_comp,Polynomial.map_neg,Polynomial.map_X,
    Polynomial.map_pow,pow_two,Polynomial.map_mul] using he
end QSVTReal

noncomputable section
open Polynomial QAlgorithms QSVT19.Main QSVTReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
lemma theorem5_checked (k : ℕ) (Pt Qt : ℝ[X]) :
    (∃ P Q : ℂ[X], IsQSPPair k P Q ∧ RePartEq P Pt ∧ RePartEq Q Qt) ↔
      ((Pt.degree ≤ k ∧ Qt.degree < k) ∧
       (HasParity (Pt.map Complex.ofRealHom) k ∧ HasParity (Qt.map Complex.ofRealHom) (k+1)) ∧
       ∀ x ∈ Set.Icc (-1:ℝ) 1, Pt.eval x^2+(1-x^2)*Qt.eval x^2 ≤ 1) := by
  constructor
  · rintro ⟨P,Q,⟨⟨hdP,hdQ⟩,⟨hpP,hpQ⟩,hid⟩,hPr,hQr⟩
    refine ⟨⟨(real_degree hPr).trans hdP,(real_degree hQr).trans_lt hdQ⟩,
      ⟨real_parity hPr hpP,real_parity hQr hpQ⟩,?_⟩
    intro x hx
    have hw : 0 ≤ 1-x^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (show 0 ≤ 1+x by linarith [hx.1])]
    have hnP : ‖P.eval (x:ℂ)‖^2 = Pt.eval x^2+(P.eval (x:ℂ)).im^2 := by
      rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,real_eval hPr]
      ring
    have hnQ : ‖Q.eval (x:ℂ)‖^2 = Qt.eval x^2+(Q.eval (x:ℂ)).im^2 := by
      rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,real_eval hQr]
      ring
    have h := hid x hx
    rw [hnP,hnQ] at h
    nlinarith [sq_nonneg (P.eval (x:ℂ)).im,mul_nonneg hw (sq_nonneg (Q.eval (x:ℂ)).im)]
  · rintro ⟨⟨hdPt,hdQt⟩,⟨hpPt,hpQt⟩,hbd⟩
    let A : ℝ[X] := 1-Pt^2-(1-X^2)*Qt^2
    have he : A.comp (-X) = A := by
      dsimp [A]
      rw [sub_comp,sub_comp,one_comp,square_even hpPt,mul_comp,square_even hpQt]
      simp
    have hd : A.degree ≤ (2*k : ℕ) := by
      apply (degree_sub_le _ _).trans
      apply max_le
      · apply (degree_sub_le _ _).trans
        apply max_le
        · simpa using (show (0 : WithBot ℕ) ≤ (2*k : ℕ) from by exact_mod_cast Nat.zero_le (2*k))
        · simpa [pow_two,two_mul] using degree_mul_le_of_le hdPt hdPt
      · simpa only [pow_two,two_mul,mul_assoc] using QSVTCert.degree_gap_mul hdQt hdQt
    have ha : ∀ x ∈ Set.Icc (-1:ℝ) 1, 0 ≤ A.eval x := by
      intro x hx
      simp only [A,eval_sub,eval_one,eval_pow,eval_mul,eval_X]
      linarith [hbd x hx]
    obtain ⟨B,C,hA,hdB,hdC,hpB,hpC⟩ := QSVT19.Main.lemma_6 k A he hd ha
    let P : ℂ[X] := Pt.map Complex.ofRealHom+Polynomial.C Complex.I * B.map Complex.ofRealHom
    let Q : ℂ[X] := Qt.map Complex.ofRealHom+Polynomial.C Complex.I * C.map Complex.ofRealHom
    have hIB : (Polynomial.C Complex.I*B.map Complex.ofRealHom).degree ≤ k := by
      rw [degree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr Complex.I_ne_zero)]
      exact degree_map_le.trans hdB
    have hIC : (Polynomial.C Complex.I*C.map Complex.ofRealHom).degree < k := by
      rw [degree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr Complex.I_ne_zero)]
      exact degree_map_le.trans_lt hdC
    have hparB : HasParity (Polynomial.C Complex.I*B.map Complex.ofRealHom) k := by
      simpa using QSVTCert.parity_mul (show HasParity (Polynomial.C Complex.I) 0 by simp [HasParity]) hpB
    have hparC : HasParity (Polynomial.C Complex.I*C.map Complex.ofRealHom) (k+1) := by
      simpa using QSVTCert.parity_mul (show HasParity (Polynomial.C Complex.I) 0 by simp [HasParity]) hpC
    refine ⟨P,Q,⟨⟨(degree_add_le _ _).trans (max_le (degree_map_le.trans hdPt) hIB),
      (degree_add_le _ _).trans_lt (max_lt (degree_map_le.trans_lt hdQt) hIC)⟩,
      ⟨QSVTCert.parity_add hpPt hparB,QSVTCert.parity_add hpQt hparC⟩,?_⟩,?_,?_⟩
    · intro x hx
      have hnP : ‖P.eval (x:ℂ)‖^2 = Pt.eval x^2+B.eval x^2 := by
        simp only [P,eval_add,eval_mul,eval_C,eval_real]
        rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
        simp [pow_two]
      have hnQ : ‖Q.eval (x:ℂ)‖^2 = Qt.eval x^2+C.eval x^2 := by
        simp only [Q,eval_add,eval_mul,eval_C,eval_real]
        rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
        simp [pow_two]
      have hh := congrArg (Polynomial.eval x) hA
      simp only [A,eval_sub,eval_one,eval_pow,eval_mul,eval_X,eval_add] at hh
      rw [hnP,hnQ]
      linarith
    · intro j
      simp [P,coeff_add,coeff_C_mul,coeff_map]
    · intro j
      simp [Q,coeff_add,coeff_C_mul,coeff_map]

set_option autoImplicit false
open QSVT19.Main


/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Theorem 5, p. 11: "Let k ∈ N be fixed. Let P̃, Q̃ ∈ R[x], there exists some
P, Q ∈ C[x] satisfying properties (i)-(iii) of Theorem 3 such that P̃ = ℜ[P], Q̃ = ℜ[Q], if and
only if P̃, Q̃ satisfy properties (i)-(ii) of Theorem 3 and
(vi) ∀x ∈ [−1, 1]: P̃(x)^2 + (1 − x^2)Q̃^2 ≤ 1."

**Formalization Note.** Properties (i)–(iii) of Theorem 3 (p. 8) are `IsQSPPair k P Q`;
`ℜ[P] = P̃` is `RePartEq P Pt` (real parts of the coefficients, §2). Properties (i)–(ii) for the
real pair are written out: `deg P̃ ≤ k`, `deg Q̃ ≤ k − 1` (as `Q̃.degree < k`), `P̃` of parity
`k mod 2`, `Q̃` of parity `k − 1 mod 2` (as `HasParity _ (k + 1)` of the complexification). The
printed "`Q̃^2`" in (vi) is `Q̃(x)^2`. The parenthetical remark after the theorem (ℑ variants,
`Q̃ ≡ 0`) is not part of this statement. -/
theorem solution (k : ℕ) (Pt Qt : ℝ[X]) :
    (∃ P Q : ℂ[X], IsQSPPair k P Q ∧ RePartEq P Pt ∧ RePartEq Q Qt) ↔ ((Pt.degree ≤ k ∧ Qt.degree < k) ∧ (QAlgorithms.HasParity (Pt.map Complex.ofRealHom) k ∧ QAlgorithms.HasParity (Qt.map Complex.ofRealHom) (k + 1)) ∧ ∀ x ∈ Set.Icc (-1 : ℝ) 1, Pt.eval x ^ 2 + (1 - x ^ 2) * Qt.eval x ^ 2 ≤ 1) := by
  exact theorem5_checked k Pt Qt