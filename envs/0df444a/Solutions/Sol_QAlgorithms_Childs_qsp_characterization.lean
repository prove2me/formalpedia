-- Prove2me | solution 1 for QAlgorithms.Childs.qsp_characterization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T21:09:15.462952+00:00
-- url     : https://prove2.me/submissions/1bf9e707-90ca-41fc-9591-a395f710a08c

import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

open Polynomial QAlgorithms
open scoped ComplexConjugate

set_option maxRecDepth 2048
noncomputable section
namespace QSPProof

private abbrev cj (P : ℂ[X]) : ℂ[X] := P.map (starRingEnd ℂ)
private def normal (P Q : ℂ[X]) : Prop :=
  P * cj P + (1 - X ^ 2) * (Q * cj Q) = 1
private def valid (k : ℕ) (P Q : ℂ[X]) : Prop :=
  (P.degree ≤ k ∧ Q.degree < k) ∧
  (HasParity P k ∧ HasParity Q (k+1)) ∧ normal P Q
private noncomputable def mat (P Q : ℂ[X]) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![P.eval (x : ℂ), Complex.I * Q.eval (x : ℂ) * (Real.sqrt (1-x^2) : ℂ);
    Complex.I * (cj Q).eval (x : ℂ) * (Real.sqrt (1-x^2) : ℂ), (cj P).eval (x : ℂ)]

private lemma real_ext {P Q : ℂ[X]} (h : ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
    P.eval (x : ℂ) = Q.eval (x : ℂ)) : P = Q := by
  apply eq_of_infinite_eval_eq
  exact ((Set.Ioo_infinite (by norm_num : (-1:ℝ)<1)).image
    Complex.ofReal_injective.injOn).mono (by
      rintro _ ⟨x,hx,rfl⟩; exact h x hx)

private lemma cj_eval (P : ℂ[X]) (x : ℝ) : (cj P).eval (x : ℂ) = conj (P.eval (x : ℂ)) := by
  simpa only [cj, Polynomial.eval_map, Complex.conj_ofReal] using (Polynomial.eval₂_at_apply (p := P) (starRingEnd ℂ) (x : ℂ))

private lemma norm_eval (P : ℂ[X]) (x : ℝ) :
    (P * cj P).eval (x : ℂ) = (‖P.eval (x : ℂ)‖ ^ 2 : ℝ) := by
  simp only [eval_mul, cj_eval, Complex.mul_conj, Complex.normSq_eq_norm_sq]

private lemma normal_iff (P Q : ℂ[X]) : normal P Q ↔
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ‖P.eval (x : ℂ)‖ ^ 2 + (1-x^2)*‖Q.eval (x : ℂ)‖ ^ 2 = 1 := by
  constructor
  · intro h x _
    have e := congrArg (Polynomial.eval (x:ℂ)) h
    simp only [eval_one] at e
    simp only [eval_add, eval_mul, eval_sub, eval_one, eval_pow, eval_X, cj_eval,
      Complex.mul_conj, Complex.normSq_eq_norm_sq] at e
    exact_mod_cast e
  · intro h
    apply real_ext
    intro x hx
    simp only [eval_one]
    have e : ((‖P.eval (x:ℂ)‖^2 + (1-x^2)*‖Q.eval (x:ℂ)‖^2 : ℝ):ℂ)=1 :=
      by exact_mod_cast h x ⟨hx.1.le,hx.2.le⟩
    simpa only [eval_add, eval_mul, eval_sub, eval_one, eval_pow, eval_X, cj_eval,
      mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow] using e

private lemma neg_coeff (P : ℂ[X]) (i : ℕ) :
    (P.comp (-X)).coeff i = (-1:ℂ)^i * P.coeff i := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq => simp [add_comp, hp, hq, mul_add]
  | monomial n a =>
    simp only [monomial_comp, show (-X : ℂ[X]) = (-1:ℂ) • X by simp,
      _root_.smul_pow, coeff_C_mul, coeff_smul, smul_eq_mul, coeff_X_pow, coeff_monomial]
    by_cases e : n=i
    · subst i; simp [mul_comm]
    · simp only [if_neg e, if_neg (Ne.symm e), mul_zero]

private lemma parity_coeff {P : ℂ[X]} {k i : ℕ} (h : HasParity P k)
    (hi : i%2 ≠ k%2) : P.coeff i = 0 := by
  have e := congrArg (fun p : ℂ[X] => p.coeff i) h
  simp only [neg_coeff, coeff_smul, smul_eq_mul] at e
  rw [neg_one_pow_eq_pow_mod_two i, neg_one_pow_eq_pow_mod_two k] at e
  rcases Nat.mod_two_eq_zero_or_one i with hmi|hmi <;>
    rcases Nat.mod_two_eq_zero_or_one k with hmk|hmk
  all_goals simp only [hmi,hmk,pow_zero,pow_one,one_mul,neg_one_mul] at e hi
  all_goals first | contradiction | linear_combination e/2 | linear_combination -e/2

private lemma phase {p q : ℂ} (h : ‖p‖ = ‖q‖) :
    ∃ φ : ℝ, Complex.exp (-(φ:ℂ)*Complex.I)*p = Complex.exp ((φ:ℂ)*Complex.I)*q := by
  by_cases hq : q=0
  · have hp : p=0 := norm_eq_zero.mp (by simpa [hq] using h)
    exact ⟨0, by simp [hp,hq]⟩
  obtain ⟨θ,hθ⟩ := (Complex.norm_eq_one_iff (p/q)).mp (by rw [norm_div,h,div_self (norm_ne_zero_iff.mpr hq)])
  refine ⟨θ/2, ?_⟩
  have e : Complex.exp ((θ:ℂ)*Complex.I)*q=p := by rw [hθ,div_mul_cancel₀ _ hq]
  rw [← e, ← mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  push_cast
  ring

private lemma parity_smul {P : ℂ[X]} {k : ℕ} (h : HasParity P k) (a : ℂ) :
    HasParity (C a * P) k := by
  dsimp [HasParity] at *
  simp only [mul_comp, C_comp, h, mul_smul_comm]

private lemma parity_sum {P Q : ℂ[X]} {k : ℕ}
    (hP : HasParity P k) (hQ : HasParity Q k) : HasParity (P+Q) k := by
  simpa only [HasParity, add_comp, smul_add] using congrArg₂ (·+·) hP hQ

private lemma parity_prod {P Q : ℂ[X]} {k l : ℕ}
    (hP : HasParity P k) (hQ : HasParity Q l) : HasParity (P*Q) (k+l) := by
  dsimp [HasParity] at *
  rw [mul_comp,hP,hQ,pow_add,mul_smul_mul_comm]

private lemma parity_shift (P : ℂ[X]) (k : ℕ) : HasParity P (k+2) ↔ HasParity P k := by
  simp [HasParity,pow_add]

private lemma parity_X : HasParity (X : ℂ[X]) 1 := by simp [HasParity]
private lemma parity_gap : HasParity (1-X^2 : ℂ[X]) 0 := by simp [HasParity]

private lemma parity_step {P Q : ℂ[X]} {k : ℕ}
    (hP : HasParity P k) (hQ : HasParity Q (k+1)) (a b : ℂ) :
    HasParity (C a * (X*P) + C b * ((1-X^2)*Q)) (k+1) ∧
    HasParity (C a * P + C b * (X*Q)) (k+2) := by
  constructor
  · apply parity_sum
    · simpa [Nat.add_comm] using parity_smul (parity_prod parity_X hP) a
    · simpa using parity_smul (parity_prod parity_gap hQ) b
  · apply parity_sum
    · exact (parity_shift _ _).mpr (parity_smul hP a)
    · simpa only [show 1+(k+1)=k+2 by omega] using parity_smul (parity_prod parity_X hQ) b

private lemma parity_back {P Q : ℂ[X]} {k : ℕ}
    (hP : HasParity P (k+1)) (hQ : HasParity Q (k+2)) (a b : ℂ) :
    HasParity (C a * (X*P) + C b * ((1-X^2)*Q)) k ∧
    HasParity (C (-a) * P + C b * (X*Q)) (k+1) := by
  have e := parity_step hP hQ a b
  have e' := parity_step hP hQ (-a) b
  exact ⟨(parity_shift _ _).mp e.1, (parity_shift _ _).mp e'.2⟩

private lemma top_norm {P Q : ℂ[X]} {k : ℕ}
    (hd : P.degree ≤ k+1 ∧ Q.degree < k+1) (hn : normal P Q) :
    ‖P.coeff (k+1)‖ = ‖Q.coeff k‖ := by
  have hp : P.natDegree ≤ k+1 := natDegree_le_of_degree_le hd.1
  have hq : Q.natDegree ≤ k := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    exact (degree_lt_iff_coeff_zero Q (k+1)).mp hd.2 i (by omega)
  have hqq : (Q*cj Q).natDegree ≤ 2*k := by
    apply (natDegree_mul_le).trans
    simp only [natDegree_map_eq_of_injective (starRingEnd ℂ).injective]
    omega
  have hpp := coeff_mul_add_eq_of_natDegree_le hp
    (show (cj P).natDegree ≤ k+1 by simpa using hp)
  have hqtop := coeff_mul_add_eq_of_natDegree_le hq
    (show (cj Q).natDegree ≤ k by simpa using hq)
  have e := congrArg (fun p : ℂ[X] => p.coeff (2*(k+1))) hn
  have e₀ : (Q*cj Q).coeff (2*(k+1)) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have e₁ : (X^2*(Q*cj Q)).coeff (2*(k+1)) = (Q*cj Q).coeff (2*k) := by
    convert coeff_X_pow_mul (Q*cj Q) 2 (2*k) using 1; congr 1
  have en : (P.coeff (k+1) * conj (P.coeff (k+1))) =
      Q.coeff k * conj (Q.coeff k) := by
    simp only [sub_mul, one_mul, coeff_add, coeff_sub, e₀, e₁] at e
    rw [show 2*(k+1)=(k+1)+(k+1) by omega, hpp] at e
    rw [show 2*k=k+k by omega, hqtop] at e
    simp only [cj, coeff_map, coeff_one, show (k+1+(k+1) ≠ 0) by omega, if_false] at e
    linear_combination e
  have en' := congrArg Complex.re en
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.ofReal_re] at en'
  nlinarith [norm_nonneg (P.coeff (k+1)),norm_nonneg (Q.coeff k)]

private abbrev ep (φ : ℝ) : ℂ := Complex.exp ((φ:ℂ)*Complex.I)
private abbrev em (φ : ℝ) : ℂ := Complex.exp (-((φ:ℂ)*Complex.I))
private lemma epem (φ : ℝ) : ep φ * em φ = 1 := by simp [ep,em, ← Complex.exp_add]
private lemma cep (φ : ℝ) : conj (ep φ) = em φ := by simp [ep,em, ← Complex.exp_conj]
private lemma cem (φ : ℝ) : conj (em φ) = ep φ := by simp [ep,em, ← Complex.exp_conj]
private noncomputable def fp (φ : ℝ) (P Q : ℂ[X]) := C (ep φ)*(X*P-(1-X^2)*Q)
private noncomputable def fq (φ : ℝ) (P Q : ℂ[X]) := C (em φ)*(P+X*Q)
private noncomputable def bp (φ : ℝ) (P Q : ℂ[X]) := C (em φ)*(X*P)+C (ep φ)*((1-X^2)*Q)
private noncomputable def bq (φ : ℝ) (P Q : ℂ[X]) := C (-(em φ))*P+C (ep φ)*(X*Q)

private lemma normal_forward {P Q : ℂ[X]} (hn : normal P Q) (φ : ℝ) :
    normal (fp φ P Q) (fq φ P Q) := by
  have hab : C (ep φ)*C (em φ)=(1:ℂ[X]) := by rw [← C_mul,epem,map_one]
  unfold normal fp fq cj
  simp only [Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_add,Polynomial.map_C,
    Polynomial.map_X,Polynomial.map_one,Polynomial.map_pow,cep,cem]
  calc
    _ = (C (ep φ)*C (em φ))*(P*cj P+(1-X^2)*(Q*cj Q)) := by ring
    _ = 1 := by rw [hab,hn,one_mul]

private lemma normal_backward {P Q : ℂ[X]} (hn : normal P Q) (φ : ℝ) :
    normal (bp φ P Q) (bq φ P Q) := by
  have hab : C (ep φ)*C (em φ)=(1:ℂ[X]) := by rw [← C_mul,epem,map_one]
  unfold normal bp bq cj
  simp only [Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_add,Polynomial.map_C,
    Polynomial.map_X,Polynomial.map_one,Polynomial.map_pow,Polynomial.map_neg,map_neg,cep,cem]
  calc
    _ = (C (ep φ)*C (em φ))*(P*cj P+(1-X^2)*(Q*cj Q)) := by ring
    _ = 1 := by rw [hab,hn,one_mul]

private lemma inverse_poly (φ : ℝ) (P Q : ℂ[X]) :
    fp φ (bp φ P Q) (bq φ P Q)=P ∧ fq φ (bp φ P Q) (bq φ P Q)=Q := by
  have hab : C (ep φ)*C (em φ)=(1:ℂ[X]) := by rw [← C_mul,epem,map_one]
  constructor
  · unfold fp bp bq
    calc
      _ = (C (ep φ)*C (em φ))*P := by simp only [C_neg];ring
      _ = P := by rw [hab,one_mul]
  · unfold fq bp bq
    calc
      _ = (C (ep φ)*C (em φ))*Q := by simp only [C_neg];ring
      _ = Q := by rw [hab,one_mul]

private lemma forward_matrix (φ : ℝ) (P Q : ℂ[X]) (x : ℝ) (hx : x ∈ Set.Icc (-1:ℝ) 1) :
    mat (fp φ P Q) (fq φ P Q) x = mat P Q x * (qspW x * qspZ φ) := by
  have hs : (Real.sqrt (1-x^2) : ℂ)^2 = 1-(x:ℂ)^2 := by
    norm_cast
    exact Real.sq_sqrt (by nlinarith [hx.1,hx.2])
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mat,fp,fq,ep,em,qspW,qspZ,Matrix.mul_apply,Fin.sum_univ_two,
      cj_eval, ← Complex.exp_conj] <;>
    ring_nf <;> (try simp only [Complex.I_sq,hs]) <;> ring

private lemma xp_coeff (P : ℂ[X]) (i : ℕ) :
    (X*P).coeff i = if i=0 then 0 else P.coeff (i-1) := by
  cases i <;> simp

private lemma forward_valid {k : ℕ} {P Q : ℂ[X]} (h : valid k P Q) (φ : ℝ) :
    valid (k+1) (fp φ P Q) (fq φ P Q) := by
  rcases h with ⟨⟨hp,hq⟩,⟨hpa,hqa⟩,hn⟩
  have zp (i : ℕ) (hi : k < i) : P.coeff i=0 :=
    coeff_eq_zero_of_degree_lt (hp.trans_lt (by exact_mod_cast hi))
  have zq (i : ℕ) (hi : k≤ i) : Q.coeff i=0 :=
    (degree_lt_iff_coeff_zero Q k).mp hq i hi
  refine ⟨⟨?_,?_⟩,?_,normal_forward hn φ⟩
  · apply (degree_le_iff_coeff_zero _ _).mpr
    intro i hi
    have hi' : k+1 < i := by exact_mod_cast hi
    simp only [fp,mul_sub,sub_mul,one_mul,coeff_C_mul,coeff_sub,xp_coeff,
      coeff_X_pow_mul']
    simp [show i≠0 by omega,show 2≤ i by omega,zp (i-1) (by omega),
      zq i (by omega),zq (i-2) (by omega)]
  · apply (degree_lt_iff_coeff_zero _ _).mpr
    intro i hi
    simp only [fq,coeff_C_mul,coeff_add,xp_coeff]
    simp [show i≠0 by omega,zp i (by omega),zq (i-1) (by omega)]
  · have e := parity_step hpa hqa (ep φ) (-(ep φ))
    refine ⟨?_,?_⟩
    · simpa only [fp,C_neg,neg_mul,sub_eq_add_neg,mul_add,mul_neg] using e.1
    · have e' := parity_step hpa hqa (em φ) (em φ)
      simpa only [fq,mul_add, Nat.add_assoc] using e'.2

private lemma peel {k : ℕ} {P Q : ℂ[X]} (h : valid (k+1) P Q) :
    ∃ φ : ℝ, valid k (bp φ P Q) (bq φ P Q) := by
  obtain ⟨φ,hφ⟩ := phase (top_norm h.1 h.2.2)
  have hphase : em φ * P.coeff (k+1)=ep φ * Q.coeff k := by
    simpa only [neg_mul] using hφ
  have zp (i : ℕ) (hi : k+1 < i) : P.coeff i=0 :=
    coeff_eq_zero_of_degree_lt (h.1.1.trans_lt (by exact_mod_cast hi))
  have zq (i : ℕ) (hi : k+1 ≤ i) : Q.coeff i=0 :=
    (degree_lt_iff_coeff_zero Q (k+1)).mp h.1.2 i hi
  have par := parity_back h.2.1.1 h.2.1.2 (em φ) (ep φ)
  refine ⟨φ,⟨⟨?_,?_⟩,par,normal_backward h.2.2 φ⟩⟩
  · apply (degree_le_iff_coeff_zero _ _).mpr
    intro i hi
    have hi' : k < i := by exact_mod_cast hi
    by_cases e : i=k+1
    · subst i
      exact parity_coeff par.1 (by omega)
    · have hi2 : k+2≤ i := by omega
      simp only [bp,coeff_add,coeff_C_mul,mul_sub,sub_mul,one_mul,coeff_sub,
        xp_coeff,coeff_X_pow_mul']
      simp only [show i≠0 by omega,if_false,show 2≤ i by omega,if_pos,zq i (by omega)]
      by_cases ei : i=k+2
      · subst i
        simp only [show k+2-1=k+1 by omega,show k+2-2=k by omega,mul_zero,
          zero_sub, ← sub_eq_add_neg]
        exact sub_eq_zero.mpr hphase
      · simp [zp (i-1) (by omega),zq (i-2) (by omega)]
  · apply (degree_lt_iff_coeff_zero _ _).mpr
    intro i hi
    by_cases e : i=k
    · subst i;exact parity_coeff par.2 (by omega)
    · have hi1 : k+1 ≤ i := by omega
      simp only [bq,coeff_add,coeff_C_mul,xp_coeff,show i≠0 by omega,if_false]
      by_cases ei : i=k+1
      · subst i
        simp only [Nat.add_sub_cancel_right,neg_mul]
        linear_combination -hphase
      · simp [zp i (by omega),zq (i-1) (by omega)]

private lemma const_valid (φ : ℝ) : valid 0 (C (ep φ)) 0 := by
  refine ⟨⟨degree_C_le,by simp⟩,⟨by simp [HasParity],by simp [HasParity]⟩,?_⟩
  simp [normal,cj,cep, ← C_mul,epem]

private lemma const_matrix (φ : ℝ) (x : ℝ) : mat (C (ep φ)) 0 x = qspZ φ := by
  ext i j;fin_cases i <;> fin_cases j <;> simp [mat,qspZ,cj,cep]

private lemma sequence_last {k : ℕ} (Φ : Fin (k+2) → ℝ) (x : ℝ) :
    qspSequence Φ x = qspSequence (fun i : Fin (k+1) => Φ i.castSucc) x *
      (qspW x * qspZ (Φ (Fin.last (k+1)))) := by
  unfold qspSequence
  rw [List.ofFn_succ',List.prod_concat]
  simp only [show (Fin.last (k+1) : Fin (k+2)) ≠ 0 by
    intro h;have := congrArg Fin.val h;simp at this,if_false]
  congr 1
  congr 1
  congr 1
  funext i
  simp only [Fin.ext_iff,Fin.val_castSucc,Fin.val_zero]

private lemma sequence_polys : ∀ k : ℕ, ∀ Φ : Fin (k+1) → ℝ,
    ∃ P Q : ℂ[X], valid k P Q ∧ ∀ x ∈ Set.Icc (-1:ℝ) 1,
      qspSequence Φ x = mat P Q x := by
  intro k
  induction k with
  | zero =>
    intro Φ
    refine ⟨C (ep (Φ 0)),0,const_valid (Φ 0),?_⟩
    intro x _
    rw [const_matrix]
    simp [qspSequence]
  | succ k ih =>
    intro Φ
    obtain ⟨P,Q,hv,hm⟩ := ih (fun i => Φ i.castSucc)
    refine ⟨fp (Φ (Fin.last (k+1))) P Q,fq (Φ (Fin.last (k+1))) P Q,
      forward_valid hv _,?_⟩
    intro x hx
    rw [sequence_last,hm x hx,forward_matrix _ _ _ x hx]

private lemma synthesize : ∀ k : ℕ, ∀ P Q : ℂ[X], valid k P Q →
    ∃ Φ : Fin (k+1) → ℝ, ∀ x ∈ Set.Icc (-1:ℝ) 1,
      qspSequence Φ x = mat P Q x := by
  intro k
  induction k with
  | zero =>
    intro P Q h
    have hp : P=C (P.coeff 0) := eq_C_of_degree_le_zero h.1.1
    have hq : Q=0 := degree_eq_bot.mp (by simpa using h.1.2)
    have hn := (normal_iff P Q).mp h.2.2 0 (by norm_num)
    rw [hp,hq] at hn
    simp only [eval_C,eval_zero,norm_zero,zero_pow (by omega : 2≠0),
      mul_zero,add_zero] at hn
    have hn' : ‖P.coeff 0‖=1 := by nlinarith [norm_nonneg (P.coeff 0)]
    obtain ⟨φ,hφ⟩ := (Complex.norm_eq_one_iff _).mp hn'
    refine ⟨fun _ => φ,?_⟩
    intro x _
    rw [hp,hq, ← hφ,const_matrix]
    simp [qspSequence]
  | succ k ih =>
    intro P Q h
    obtain ⟨φ,hφ⟩ := peel h
    obtain ⟨Φ,hΦ⟩ := ih (bp φ P Q) (bq φ P Q) hφ
    refine ⟨Fin.lastCases φ Φ,?_⟩
    intro x hx
    rw [sequence_last]
    simp only [Fin.lastCases_castSucc,Fin.lastCases_last]
    rw [hΦ x hx, ← forward_matrix φ _ _ x hx,
      (inverse_poly φ P Q).1,(inverse_poly φ P Q).2]

private lemma mat_inj {P Q R S : ℂ[X]}
    (h : ∀ x ∈ Set.Icc (-1:ℝ) 1, mat P Q x = mat R S x) : P=R ∧ Q=S := by
  constructor
  · apply real_ext
    intro x hx
    have e := congrArg (fun a : Matrix (Fin 2) (Fin 2) ℂ => a 0 0)
      (h x ⟨hx.1.le,hx.2.le⟩)
    simpa [mat] using e
  · apply real_ext
    intro x hx
    have e := congrArg (fun a : Matrix (Fin 2) (Fin 2) ℂ => a 0 1)
      (h x ⟨hx.1.le,hx.2.le⟩)
    simp only [mat] at e
    have hs : (Real.sqrt (1-x^2) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by nlinarith [hx.1,hx.2])))
    exact mul_left_cancel₀ Complex.I_ne_zero (mul_right_cancel₀ hs e)

end QSPProof

theorem solution (k : ℕ) (P Q : ℂ[X]) :
    (∃ Φ : Fin (k + 1) → ℝ, ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      qspSequence Φ x =
        !![P.eval (x : ℂ), Complex.I * Q.eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ);
          Complex.I * (Q.map (starRingEnd ℂ)).eval (x : ℂ) * (Real.sqrt (1 - x ^ 2) : ℂ),
          (P.map (starRingEnd ℂ)).eval (x : ℂ)]) ↔
    ((P.degree ≤ k ∧ Q.degree < k) ∧
      (HasParity P k ∧ HasParity Q (k + 1)) ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        ‖P.eval (x : ℂ)‖ ^ 2 + (1 - x ^ 2) * ‖Q.eval (x : ℂ)‖ ^ 2 = 1) := by
  constructor
  · rintro ⟨Φ,hΦ⟩
    obtain ⟨R,S,hv,hm⟩ := QSPProof.sequence_polys k Φ
    have he : P=R ∧ Q=S := QSPProof.mat_inj (by
      intro x hx
      exact (hΦ x hx).symm.trans (hm x hx))
    rcases he with ⟨heP,heQ⟩
    subst R;subst S
    exact ⟨hv.1,hv.2.1,(QSPProof.normal_iff P Q).mp hv.2.2⟩
  · intro h
    exact QSPProof.synthesize k P Q ⟨h.1,h.2.1,(QSPProof.normal_iff P Q).mpr h.2.2⟩
