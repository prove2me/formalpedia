-- Prove2me | solution 1 for QSVT19.Main.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T21:02:54.8662+00:00
-- url     : https://prove2.me/submissions/74d1376e-3a11-4cbb-b31b-19a9380b9e82

import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ComputeDegree
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.DenselyOrdered

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
open Polynomial
set_option autoImplicit false
namespace QSVTEven
lemma neg_coeff (P : ℝ[X]) (i : ℕ) :
    (P.comp (-X)).coeff i = (-1:ℝ)^i * P.coeff i := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq => simp [add_comp, hp, hq, mul_add]
  | monomial n a =>
    simp only [monomial_comp, show (-X : ℝ[X]) = (-1:ℝ) • X by simp,
      _root_.smul_pow, coeff_C_mul, coeff_smul, smul_eq_mul, coeff_X_pow, coeff_monomial]
    by_cases e : n=i
    · subst i; simp [mul_comm]
    · simp only [if_neg e, if_neg (Ne.symm e), mul_zero]

lemma even_contract (A : ℝ[X]) (he : A.comp (-X) = A) :
    (contract 2 A).comp (X^2) = A := by
  have hodd (n : ℕ) (hn : ¬ 2 ∣ n) : A.coeff n = 0 := by
    have h := congrArg (fun p : ℝ[X] => p.coeff n) he
    simp only [neg_coeff] at h
    have hmod : n % 2 = 1 := by omega
    rw [neg_one_pow_eq_pow_mod_two,hmod] at h
    norm_num at h
    linarith
  rw [← expand_eq_comp_X_pow]
  ext n
  rw [coeff_expand (by decide : 0 < 2)]
  split_ifs with hn
  · rw [coeff_contract (by decide : (2:ℕ) ≠ 0)]
    congr 1
    exact Nat.div_mul_cancel hn
  · exact (hodd n hn).symm
lemma contract_degree (A : ℝ[X]) (k : ℕ) (he : A.comp (-X) = A)
    (hd : A.degree ≤ (2*k : ℕ)) : (contract 2 A).natDegree ≤ k := by
  have h := congrArg Polynomial.natDegree (even_contract A he)
  rw [← expand_eq_comp_X_pow,natDegree_expand] at h
  have hA : A.natDegree ≤ 2*k := natDegree_le_iff_degree_le.mpr hd
  omega
lemma contract_nonneg (A : ℝ[X]) (he : A.comp (-X) = A)
    (hp : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ A.eval x) :
    ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ (contract 2 A).eval y := by
  intro y hy
  have hs : Real.sqrt y ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨(by linarith [Real.sqrt_nonneg y]),(Real.sqrt_le_one).mpr hy.2⟩
  have h := hp (Real.sqrt y) hs
  rw [← even_contract A he,eval_comp,eval_pow,eval_X,Real.sq_sqrt hy.1] at h
  exact h
end QSVTEven

noncomputable section
open Polynomial QAlgorithms
set_option autoImplicit false
namespace QSVTCert
 def Cert (k : ℕ) (A : ℝ[X]) : Prop := ∃ B C : ℝ[X],
  A = B^2 + (1-X^2)*C^2 ∧ B.degree ≤ k ∧ C.degree < k ∧
  HasParity (B.map Complex.ofRealHom) k ∧ HasParity (C.map Complex.ofRealHom) (k+1)
lemma cert_mul {k l : ℕ} {A D : ℝ[X]} (hA : Cert k A) (hD : Cert l D) : Cert (k+l) (A*D) := by
  obtain ⟨B,C,ha,hb,hc,hpb,hpc⟩ := hA
  obtain ⟨E,F,hd,he,hf,hpe,hpf⟩ := hD
  exact ⟨B*E-(1-X^2)*C*F,B*F+C*E,certificate_mul k l A B C D E F ha hd hb hc he hf hpb hpc hpe hpf⟩
lemma cert_const (a : ℝ) (ha : 0 ≤ a) : Cert 0 (C a) := by
  refine ⟨C (Real.sqrt a),0,?_,degree_C_le,by simp,?_,by simp [HasParity]⟩
  · simp only [zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero,add_zero,← C_pow,Real.sq_sqrt ha]
  · simp [HasParity]
lemma cert_one_grade_one : Cert 1 (1 : ℝ[X]) := by
  refine ⟨X,1,by ring,by simp,by norm_num,?_,?_⟩ <;> simp [HasParity]
lemma cert_succ {k : ℕ} {A : ℝ[X]} (h : Cert k A) : Cert (k+1) A := by
  simpa only [mul_one] using cert_mul h cert_one_grade_one
lemma cert_mono {k l : ℕ} {A : ℝ[X]} (h : Cert k A) (hk : k ≤ l) : Cert l A := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hk
  induction n with
  | zero => simpa using h
  | succ n ih => exact cert_succ (ih (Nat.le_add_right k n))
lemma cert_linear_low (r : ℝ) (hr : r ≤ 0) : Cert 1 (X^2-C r) := by
  let b := Real.sqrt (1-r)
  let c := Real.sqrt (-r)
  have hb : b^2 = 1-r := Real.sq_sqrt (by linarith)
  have hc : c^2 = -r := Real.sq_sqrt (by linarith)
  refine ⟨C b * X,C c,?_,?_,?_,?_,?_⟩
  · apply Polynomial.funext
    intro x
    simp only [eval_sub,eval_pow,eval_X,eval_C,eval_add,eval_mul,eval_one]
    linear_combination -x^2 * hb - (1-x^2) * hc
  · compute_degree!
  · exact lt_of_le_of_lt degree_C_le (by norm_num)
  · simp [HasParity,Polynomial.map_mul]
  · simp [HasParity]
lemma cert_linear_high (r : ℝ) (hr : 1 ≤ r) : Cert 1 (C r-X^2) := by
  let b := Real.sqrt (r-1)
  let c := Real.sqrt r
  have hb : b^2 = r-1 := Real.sq_sqrt (by linarith)
  have hc : c^2 = r := Real.sq_sqrt (by linarith)
  refine ⟨C b * X,C c,?_,?_,?_,?_,?_⟩
  · apply Polynomial.funext
    intro x
    simp only [eval_sub,eval_pow,eval_X,eval_C,eval_add,eval_mul,eval_one]
    linear_combination -x^2 * hb - (1-x^2) * hc
  · compute_degree!
  · exact lt_of_le_of_lt degree_C_le (by norm_num)
  · simp [HasParity,Polynomial.map_mul]
  · simp [HasParity]
lemma cert_real_square (r : ℝ) : Cert 2 ((X^2-C r)^2) := by
  refine ⟨X^2-C r,0,by simp,?_,WithBot.bot_lt_coe 2,?_,by simp [HasParity]⟩
  · compute_degree!
  · simp [HasParity]
lemma cert_complex_pair (a b : ℝ) : Cert 2 ((X^2-C a)^2+(C b)^2) := by
  let r := Real.sqrt (a^2+b^2)
  let s := Real.sqrt ((a-1)^2+b^2)
  let c := r+s
  let d := Real.sqrt (c^2-1)
  have hr : r^2 = a^2+b^2 := Real.sq_sqrt (by positivity)
  have hs : s^2 = (a-1)^2+b^2 := Real.sq_sqrt (by positivity)
  have hra : a ≤ r := by have := Real.sqrt_nonneg (a^2+b^2);change 0 ≤ r at this;nlinarith [sq_nonneg b]
  have hsa : 1-a ≤ s := by have := Real.sqrt_nonneg ((a-1)^2+b^2);change 0 ≤ s at this;nlinarith [sq_nonneg b]
  have hc : 1 ≤ c := by dsimp [c];linarith
  have hd : d^2 = c^2-1 := Real.sq_sqrt (by nlinarith)
  have he : c^2-2*r*c = 1-2*a := by dsimp [c];nlinarith [hr,hs]
  refine ⟨C c*X^2-C r,C d*X,?_,?_,?_,?_,?_⟩
  · apply Polynomial.funext
    intro x
    simp only [eval_sub,eval_pow,eval_X,eval_C,eval_add,eval_mul,eval_one]
    linear_combination -(x^2-x^4)*hd - x^2*he - hr
  · compute_degree!
  · have : (C d * X : ℝ[X]).degree ≤ 1 := by compute_degree!
    exact lt_of_le_of_lt this (by norm_num)
  · simp [HasParity,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_pow]
  · norm_num [HasParity,Polynomial.map_mul]
end QSVTCert

noncomputable section
open Polynomial
set_option autoImplicit false
set_option maxRecDepth 2048
namespace QSVTFactor
open QSVTCert
lemma extend_nonneg (q : ℝ[X]) (h : ∀ x ∈ Set.Ioo (0:ℝ) 1, 0 ≤ q.eval x) :
    ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ q.eval x := by
  have hc : closure (Set.Ioo (0:ℝ) 1) ⊆ {x | 0 ≤ q.eval x} :=
    closure_minimal h (isClosed_le continuous_const q.continuous)
  rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)] at hc
  exact hc
lemma quotient_nonneg (p g q : ℝ[X])
    (hp : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ p.eval x)
    (hpg : p = g*q) (hg : ∀ x ∈ Set.Ioo (0:ℝ) 1, 0 < g.eval x) :
    ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ q.eval x := by
  apply extend_nonneg
  intro x hx
  have h := hp x ⟨hx.1.le,hx.2.le⟩
  rw [hpg,eval_mul] at h
  exact nonneg_of_mul_nonneg_right h (hg x hx)
lemma square_factor (p : ℝ[X]) (a : ℝ) (ha : a ∈ Set.Ioo (0:ℝ) 1)
    (hp : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ p.eval x) (hpa : p.eval a = 0) :
    ∃ q : ℝ[X], p = (X-C a)^2*q ∧ ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ q.eval x := by
  have hmin : IsLocalMin (fun x : ℝ => p.eval x) a := by
    apply IsMinOn.isLocalMin (s := Set.Ioo (0:ℝ) 1)
    · intro x hx;change p.eval a ≤ p.eval x;rw [hpa];exact hp x ⟨hx.1.le,hx.2.le⟩
    · exact isOpen_Ioo.mem_nhds ha
  have hd : p.derivative.eval a = 0 := hmin.hasDerivAt_eq_zero (p.hasDerivAt a)
  obtain ⟨q,hq⟩ := (dvd_iff_isRoot.mpr hpa : X-C a ∣ p)
  have hqa : q.eval a = 0 := by
    rw [hq,derivative_mul] at hd
    simpa using hd
  obtain ⟨r,hr⟩ := (dvd_iff_isRoot.mpr hqa : X-C a ∣ q)
  have hpr : p = (X-C a)^2*r := by rw [hq,hr];ring
  refine ⟨r,hpr,?_⟩
  apply extend_nonneg
  have hclosed : IsClosed {x : ℝ | 0 ≤ r.eval x} := isClosed_le continuous_const r.continuous
  have hset : (Set.Ioo (0:ℝ) 1 ∩ {a}ᶜ) ⊆ {x : ℝ | 0 ≤ r.eval x} := by
    rintro x ⟨hx,hxa⟩
    have hxne : x-a ≠ 0 := sub_ne_zero.mpr (by simpa using hxa)
    have h := hp x ⟨hx.1.le,hx.2.le⟩
    rw [hpr,eval_mul,eval_pow,eval_sub,eval_X,eval_C] at h
    exact nonneg_of_mul_nonneg_right h (sq_pos_of_ne_zero hxne)
  exact ((dense_compl_singleton a).open_subset_closure_inter isOpen_Ioo).trans
    (closure_minimal hset hclosed)
lemma bounded_certificate (p : ℝ[X])
    (hp : ∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ p.eval x) :
    Cert p.natDegree (p.comp (X^2)) := by
  classical
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases hz : p = 0
    · subst p
      refine ⟨0,0,by simp,by simp,WithBot.bot_lt_coe n,?_,?_⟩ <;> simp [QAlgorithms.HasParity]
    by_cases hc : p.natDegree = 0
    · have he : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hc
      have h0 : 0 ≤ p.coeff 0 := by
        have h := hp 0 (by norm_num)
        rw [he,eval_C] at h
        exact h
      rw [he,C_comp]
      exact cert_mono (cert_const _ h0) (Nat.zero_le n)
    by_cases hr : ∃ a ∈ Set.Ioo (0:ℝ) 1, p.eval a = 0
    · obtain ⟨a,ha,hpa⟩ := hr
      obtain ⟨q,hq,hqp⟩ := square_factor p a ha hp hpa
      have hq0 : q ≠ 0 := by intro h;rw [h,mul_zero] at hq;exact hz hq
      have hd : n = 2+q.natDegree := by
        have h := congrArg Polynomial.natDegree hq
        rw [natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero a)) hq0,natDegree_pow,natDegree_X_sub_C] at h
        omega
      have hi := ih q.natDegree (by omega) q hqp rfl
      rw [hq,mul_comp,pow_comp,sub_comp,X_comp,C_comp,hd]
      exact cert_mul (cert_real_square a) hi
    · obtain ⟨z,hzroot⟩ : ∃ z : ℂ, aeval z p = 0 :=
        IsAlgClosed.exists_aeval_eq_zero ℂ p (by
          rw [degree_eq_natDegree hz];exact_mod_cast (Nat.pos_of_ne_zero hc).ne')
      by_cases him : z.im = 0
      · let a := z.re
        have hza : z = (a : ℂ) := by apply Complex.ext <;> simp [a,him]
        have hpa : p.eval a = 0 := by
          have h := hzroot
          rw [hza] at h
          change aeval (algebraMap ℝ ℂ a) p = 0 at h
          rw [aeval_algebraMap_apply_eq_algebraMap_eval] at h
          exact Complex.ofReal_injective h
        have hout : a ≤ 0 ∨ 1 ≤ a := by
          by_cases h : a ≤ 0
          · exact Or.inl h
          · right;by_contra h';exact hr ⟨a,⟨by linarith,by linarith⟩,hpa⟩
        obtain ⟨q,hq⟩ := (dvd_iff_isRoot.mpr hpa : X-C a ∣ p)
        obtain ⟨g,r,hpr,hgdeg,hgpos,hgcert⟩ :
            ∃ g r : ℝ[X], p = g*r ∧ g.natDegree = 1 ∧
              (∀ x ∈ Set.Ioo (0:ℝ) 1, 0 < g.eval x) ∧ Cert 1 (g.comp (X^2)) := by
          rcases hout with hlow | hhigh
          · refine ⟨X-C a,q,hq,natDegree_X_sub_C a,?_,?_⟩
            · intro x hx;simp only [eval_sub,eval_X,eval_C];linarith [hx.1,hx.2]
            · simpa only [sub_comp,X_comp,C_comp] using cert_linear_low a hlow
          · refine ⟨C a-X,-q,?_,?_,?_,?_⟩
            · rw [hq];ring
            · have he : C a-X = -(X-C a) := by ring
              rw [he,natDegree_neg,natDegree_X_sub_C]
            · intro x hx;simp only [eval_sub,eval_X,eval_C];linarith [hx.1,hx.2]
            · simpa only [sub_comp,X_comp,C_comp] using cert_linear_high a hhigh
        have hg0 : g ≠ 0 := by intro h;simp [h] at hgdeg
        have hr0 : r ≠ 0 := by intro h;rw [h,mul_zero] at hpr;exact hz hpr
        have hd : n = 1+r.natDegree := by
          have h := congrArg Polynomial.natDegree hpr
          rw [natDegree_mul hg0 hr0,hgdeg] at h
          omega
        have hi := ih r.natDegree (by omega) r (quotient_nonneg p g r hp hpr hgpos) rfl
        rw [hpr,mul_comp,hd]
        exact cert_mul hgcert hi
      · let g : ℝ[X] := (X-C z.re)^2+(C z.im)^2
        have hgp (x : ℝ) : 0 < g.eval x := by
          simp only [g,eval_add,eval_pow,eval_sub,eval_X,eval_C]
          nlinarith [sq_nonneg (x-z.re),sq_pos_of_ne_zero him]
        have hg0 : g ≠ 0 := by intro h;have := hgp 0;simp [h] at this
        have hgdeg : g.natDegree = 2 := by dsimp [g];compute_degree!
        obtain ⟨q,hq⟩ := p.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hzroot him
        have he : X^2-C (2*z.re)*X+C (‖z‖^2) = g := by
          dsimp [g]
          rw [Complex.sq_norm,Complex.normSq_apply]
          simp only [map_add,map_mul,map_pow,map_ofNat]
          ring
        rw [he] at hq
        have hq0 : q ≠ 0 := by intro h;rw [h,mul_zero] at hq;exact hz hq
        have hd : n = 2+q.natDegree := by
          have h := congrArg Polynomial.natDegree hq
          rw [natDegree_mul hg0 hq0,hgdeg] at h
          omega
        have hi := ih q.natDegree (by omega) q (quotient_nonneg p g q hp hq (fun x _ => hgp x)) rfl
        have hgcert : Cert 2 (g.comp (X^2)) := by
          simpa only [g,add_comp,pow_comp,sub_comp,X_comp,C_comp] using cert_complex_pair z.re z.im
        rw [hq,mul_comp,hd]
        exact cert_mul hgcert hi
end QSVTFactor

noncomputable section
open Polynomial
set_option autoImplicit false
namespace QSVT19.Main
lemma lemma6_checked (k : ℕ) (A : ℝ[X]) (he : A.comp (-X) = A)
    (hd : A.degree ≤ (2*k : ℕ))
    (hp : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ A.eval x) :
    ∃ B C : ℝ[X], A = B^2+(1-X^2)*C^2 ∧ B.degree ≤ k ∧ C.degree < k ∧
      QAlgorithms.HasParity (B.map Complex.ofRealHom) k ∧
      QAlgorithms.HasParity (C.map Complex.ofRealHom) (k+1) := by
  have h := QSVTFactor.bounded_certificate (contract 2 A) (QSVTEven.contract_nonneg A he hp)
  have hbound := QSVTEven.contract_degree A k he hd
  have h' := QSVTCert.cert_mono h hbound
  rw [QSVTEven.even_contract A he] at h'
  exact h'
end QSVT19.Main

set_option autoImplicit false



/-- Gilyén, Su, Low, Wiebe, arXiv:1806.01838v1, Lemma 6, p. 11: "Suppose that A ∈ R[x] is an even polynomial such that deg(A) ≤ 2k and
for all x ∈ [−1, 1] we have A(x) ≥ 0. Then there exist polynomials B, C ∈ R[x] such that
A(x) = B^2(x) + (1 − x^2)C^2(x), moreover deg(B) ≤ k, deg(C) ≤ k − 1, B has parity-(k mod 2) and
C has parity-(k − 1 mod 2)."

**Formalization Note.** "A is even" is `A.comp (−X) = A`. The identity `A = B² + (1 − X²)C²` is
an identity of polynomials (equivalently, for all real `x`). "deg(C) ≤ k − 1" is `C.degree < k`
(so `k = 0` forces `C = 0`), and "parity-(k − 1 mod 2)" is `HasParity _ (k + 1)`; parities of
real polynomials are stated for their images in `ℂ[X]`. -/
theorem solution (k : ℕ) (A : ℝ[X]) (hA_even : A.comp (-X) = A) (hA_deg : A.degree ≤ (2 * k : ℕ))
    (hA_nonneg : ∀ x ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ A.eval x) :
    ∃ B C : ℝ[X], A = B ^ 2 + (1 - X ^ 2) * C ^ 2 ∧ B.degree ≤ k ∧ C.degree < k ∧ QAlgorithms.HasParity (B.map Complex.ofRealHom) k ∧ QAlgorithms.HasParity (C.map Complex.ofRealHom) (k + 1) := by
  exact QSVT19.Main.lemma6_checked k A hA_even hA_deg hA_nonneg