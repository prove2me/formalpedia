-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P56.tensor_fourier_formula
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T06:06:07.434683+00:00
-- url     : https://prove2.me/submissions/77f0b9b8-7e94-4d6c-8f6c-7e63547605ba

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

open Polynomial
lemma h54b_cfc_diag {X : Type*} [Fintype X] [DecidableEq X] (d : X → ℝ) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal (fun i => (d i : ℂ))) = Matrix.diagonal (fun i => (f (d i) : ℂ)) := by
  set A := Matrix.diagonal (fun i => (d i : ℂ)) with hA
  have hsa : IsSelfAdjoint A := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, hA, Matrix.diagonal_conjTranspose]
    congr 1; funext i; simp
  set S : Finset ℝ := Finset.univ.image d
  let p : ℝ[X] := Lagrange.interpolate S id f
  have hp : ∀ i, p.eval (d i) = f (d i) := by
    intro i
    have := Lagrange.eval_interpolate_at_node (s := S) (v := id) (r := f) (i := d i)
      (Set.injOn_id _) (Finset.mem_image_of_mem d (Finset.mem_univ i))
    exact this
  have hspec : ∀ x ∈ spectrum ℝ A, ∃ i, d i = x := by
    intro x hx
    rw [← spectrum.preimage_algebraMap ℂ, Set.mem_preimage, hA, spectrum_diagonal,
      Set.mem_range] at hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, by rw [Complex.coe_algebraMap] at hi; exact_mod_cast hi⟩
  have h1 : cfc f A = cfc p.eval A := by
    apply cfc_congr
    intro x hx
    obtain ⟨i, rfl⟩ := hspec x hx
    exact (hp i).symm
  rw [h1, cfc_polynomial p A]
  rw [hA, show Matrix.diagonal (fun i => (d i : ℂ)) =
    Matrix.diagonalAlgHom ℝ (fun i => (d i : ℂ)) from rfl, Polynomial.aeval_algHom_apply]
  rw [show Matrix.diagonal (fun i => (f (d i) : ℂ)) =
    Matrix.diagonalAlgHom ℝ (fun i => (f (d i) : ℂ)) from rfl]
  congr 1
  funext i
  rw [Polynomial.aeval_pi_apply₂]
  rw [show ((d i : ℝ) : ℂ) = algebraMap ℝ ℂ (d i) from rfl, Polynomial.aeval_algebraMap_apply,
    Polynomial.aeval_def, Algebra.algebraMap_self, ← Polynomial.eval, hp]
  rfl
lemma h54b_sign_sum {ι : Type*} (s : Finset ι) (b : ι → Bool) :
    (if (∑ i ∈ s, b i) = true then (-1 : ℝ) else 1) = ∏ i ∈ s, (if b i = true then (-1 : ℝ) else 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, ← ih]
    generalize (∑ i ∈ s, b i) = S
    have e1 : (true + true : Bool) = false := rfl
    have e2 : (true + false : Bool) = true := rfl
    have e3 : (false + true : Bool) = true := rfl
    have e4 : (false + false : Bool) = false := rfl
    cases b a <;> cases S <;> simp [e1, e2, e3, e4]

lemma h54b_prod_ite {n : ℕ} (c : Fin n → Bool) (u v : ℝ) :
    ∏ i, (if c i = true then u else v) = u ^ hammingWeight c * v ^ (n - hammingWeight c) := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  unfold hammingWeight
  congr 2
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i => c i = true)
  rw [Finset.card_univ, Fintype.card_fin] at this
  omega

lemma h54b_sqrt_pow (x : ℝ) (hx : 0 ≤ x) (m : ℕ) : Real.sqrt (x ^ m) = Real.sqrt x ^ m := by
  rw [← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg x) m), ← pow_mul, mul_comm, pow_mul,
    Real.sq_sqrt hx]

def h54b_r (qp : ℝ) (a : Bool) : ℝ := if a = true then Real.sqrt (1 - qp) else Real.sqrt qp

lemma h54b_eve_coord (qp : ℝ) (x a b : Bool) :
    hybridEve qp x a b = ((h54b_r qp a * h54b_r qp b *
      (if (x && Bool.xor a b) = true then (-1 : ℝ) else 1) : ℝ) : ℂ) := by
  cases x <;> cases a <;> cases b <;> simp [hybridEve, h54b_r, Complex.conj_ofReal]

lemma h54b_prod_r {n : ℕ} (qp : ℝ) (h0 : 0 ≤ qp) (h1 : qp ≤ 1) (j : Qubits n) :
    ∏ i, h54b_r qp (j i) = Real.sqrt (eveWeight n qp j) := by
  unfold h54b_r eveWeight
  rw [h54b_prod_ite j, Real.sqrt_mul (pow_nonneg h0 _), h54b_sqrt_pow _ h0,
    h54b_sqrt_pow _ (by linarith)]
  ring

theorem solution (n : ℕ) (hn : 1 ≤ n) (q qprime : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hqp : qprime ∈ Set.Icc (0 : ℝ) 1)
    (P : QAlgorithms.Qubits n → ℝ) (hP : IsLaw P) :
    (∀ y z, average (productOutput n (hybridBob q)) P y z =
      if y = z then ((∑ g, P g *
        q ^ QAlgorithms.hammingWeight (fun i => Bool.xor (y i) (g i)) *
        (1 - q) ^ (n - QAlgorithms.hammingWeight (fun i => Bool.xor (y i) (g i))) : ℝ) : ℂ)
      else 0) ∧
    (∀ j k, average (productOutput n (hybridEve qprime)) P j k =
      ((Real.sqrt (eveWeight n qprime j) * walsh P (fun i => Bool.xor (j i) (k i)) *
        Real.sqrt (eveWeight n qprime k) : ℝ) : ℂ)) ∧
    walsh P (fun _ => false) = 1 ∧
    (entropy (average (productOutput n (hybridBob q)) P) =
      - ∑ y : QAlgorithms.Qubits n, let py := ∑ g, P g *
          q ^ QAlgorithms.hammingWeight (fun i => Bool.xor (y i) (g i)) *
          (1 - q) ^ (n - QAlgorithms.hammingWeight (fun i => Bool.xor (y i) (g i)))
        py * Real.log py) ∧
    (∀ (Q : QAlgorithms.Qubits 2 → ℝ) (t1 t2 t3 : ℝ),
      IsLaw Q →
      (∀ z, Q z = (![t1, (1 - t1 - t2 + t3) / 2,
        (1 - t1 - t2 - t3) / 2, t2] (QAlgorithms.bitsEquivFin 2 z))) →
      walsh Q ![true, false] = t1 - t2 + t3 ∧
      walsh Q ![false, true] = t1 - t2 - t3 ∧
      walsh Q ![true, true] = 2 * t1 + 2 * t2 - 1) := by
  have hbob : ∀ y z, average (productOutput n (hybridBob q)) P y z =
      if y = z then ((∑ g, P g *
        q ^ QAlgorithms.hammingWeight (fun i => Bool.xor (y i) (g i)) *
        (1 - q) ^ (n - QAlgorithms.hammingWeight (fun i => Bool.xor (y i) (g i))) : ℝ) : ℂ)
      else 0 := by
    intro y z
    unfold average
    rw [Matrix.sum_apply]
    simp only [Matrix.smul_apply, productOutput, hybridBob, Matrix.diagonal_apply, smul_eq_mul]
    split_ifs with h
    · subst h
      push_cast
      refine Finset.sum_congr rfl (fun g _ => ?_)
      simp only [if_true]
      have key : ∏ x, (if y x = g x then 1 - q else q) =
          q ^ QAlgorithms.hammingWeight (fun i => Bool.xor (y i) (g i)) *
          (1 - q) ^ (n - QAlgorithms.hammingWeight (fun i => Bool.xor (y i) (g i))) := by
        rw [← h54b_prod_ite (fun i => Bool.xor (y i) (g i)) q (1 - q)]
        refine Finset.prod_congr rfl (fun i _ => ?_)
        cases y i <;> cases g i <;> simp
      rw [← Complex.ofReal_prod, key]
      push_cast
      ring
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      refine Finset.sum_eq_zero (fun g _ => ?_)
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), mul_zero]
  refine ⟨hbob, ?_, ?_, ?_, ?_⟩
  · intro j k
    unfold average walsh
    rw [Matrix.sum_apply]
    simp only [Matrix.smul_apply, productOutput, h54b_eve_coord, smul_eq_mul]
    simp only [← Complex.ofReal_prod]
    simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum]
    congr 1
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, h54b_prod_r _ hqp.1 hqp.2,
      h54b_prod_r _ hqp.1 hqp.2]
    unfold dotBits
    rw [h54b_sign_sum]
    ring
  · have h0 : ∀ g : QAlgorithms.Qubits n, QAlgorithms.dotBits g (fun _ => false) = false := by
      intro g; unfold QAlgorithms.dotBits; simp only [Bool.and_false]
      exact Finset.sum_eq_zero (fun _ _ => rfl)
    unfold walsh
    simp [h0, hP.2]
  · have hdiag : average (productOutput n (hybridBob q)) P = Matrix.diagonal (fun y =>
        ((∑ g, P g * q ^ QAlgorithms.hammingWeight (fun i => Bool.xor (y i) (g i)) *
        (1 - q) ^ (n - QAlgorithms.hammingWeight (fun i => Bool.xor (y i) (g i))) : ℝ) : ℂ)) := by
      ext y z
      rw [hbob, Matrix.diagonal_apply]
    unfold entropy
    rw [hdiag, h54b_cfc_diag, Matrix.trace_diagonal, Complex.re_sum]
    simp only [Complex.ofReal_re]
  · intro Q t1 t2 t3 _ hQ
    have hsum : ∀ F : QAlgorithms.Qubits 2 → ℝ, ∑ z, F z =
        F ![false,false] + F ![false,true] + F ![true,false] + F ![true,true] := by
      intro F
      rw [← (QAlgorithms.bitsEquivFin 2).symm.sum_comp]
      show ∑ k : Fin 4, _ = _
      rw [Fin.sum_univ_four]
      have h0 : (QAlgorithms.bitsEquivFin 2).symm 0 = ![false, false] := by decide
      have h1 : (QAlgorithms.bitsEquivFin 2).symm 1 = ![false, true] := by decide
      have h2 : (QAlgorithms.bitsEquivFin 2).symm 2 = ![true, false] := by decide
      have h3 : (QAlgorithms.bitsEquivFin 2).symm 3 = ![true, true] := by decide
      rw [h0, h1, h2, h3]
    have q0 : Q ![false, false] = t1 := by
      rw [hQ]; rw [show QAlgorithms.bitsEquivFin 2 ![false, false] = 0 by decide]; rfl
    have q1 : Q ![false, true] = (1 - t1 - t2 + t3) / 2 := by
      rw [hQ]; rw [show QAlgorithms.bitsEquivFin 2 ![false, true] = 1 by decide]; rfl
    have q2 : Q ![true, false] = (1 - t1 - t2 - t3) / 2 := by
      rw [hQ]; rw [show QAlgorithms.bitsEquivFin 2 ![true, false] = 2 by decide]; rfl
    have q3 : Q ![true, true] = t2 := by
      rw [hQ]; rw [show QAlgorithms.bitsEquivFin 2 ![true, true] = 3 by decide]; rfl
    unfold walsh
    rw [hsum, hsum, hsum, q0, q1, q2, q3]
    have d1 : QAlgorithms.dotBits ![false, false] ![true, false] = false := by decide
    have d2 : QAlgorithms.dotBits ![false, true] ![true, false] = false := by decide
    have d3 : QAlgorithms.dotBits ![true, false] ![true, false] = true := by decide
    have d4 : QAlgorithms.dotBits ![true, true] ![true, false] = true := by decide
    have e1 : QAlgorithms.dotBits ![false, false] ![false, true] = false := by decide
    have e2 : QAlgorithms.dotBits ![false, true] ![false, true] = true := by decide
    have e3 : QAlgorithms.dotBits ![true, false] ![false, true] = false := by decide
    have e4 : QAlgorithms.dotBits ![true, true] ![false, true] = true := by decide
    have f1 : QAlgorithms.dotBits ![false, false] ![true, true] = false := by decide
    have f2 : QAlgorithms.dotBits ![false, true] ![true, true] = true := by decide
    have f3 : QAlgorithms.dotBits ![true, false] ![true, true] = true := by decide
    have f4 : QAlgorithms.dotBits ![true, true] ![true, true] = false := by decide
    simp only [d1, d2, d3, d4, e1, e2, e3, e4, f1, f2, f3, f4]
    refine ⟨by norm_num; ring, by norm_num; ring, by norm_num; ring⟩

end
