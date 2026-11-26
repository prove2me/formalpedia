-- Prove2me | solution 1 for QNoiseStab.corollary_2_9
-- status  : ACCEPTED   (prove)
-- author  : @blake-holman
-- created : 2026-11-26T04:04:12.835699+00:00
-- url     : https://prove2.me/submissions/c3a1c302-1ab0-43b8-9e1d-b30217d64439

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QNoiseStab_phaseQuery
import Definitions.Def_QNoiseStab_fourierWeight
import Definitions.Def_QNoiseStab_fourierVec

-- Solutions.Corollary29
section
namespace QNoiseStab

section

variable {n d : ℕ}

/-- Finite sums of functions that each depend on at most `t` coordinates. -/
inductive JuntaSum (t : ℕ) : ((Fin n → ZMod d) → ℂ) → Prop where
  | junta (s : Finset (Fin n)) (hs : s.card ≤ t) (f : (Fin n → ZMod d) → ℂ)
      (hf : ∀ x y, (∀ i ∈ s, x i = y i) → f x = f y) : JuntaSum t f
  | sum {ι : Type} [Fintype ι] (f : ι → (Fin n → ZMod d) → ℂ)
      (hf : ∀ j, JuntaSum t (f j)) : JuntaSum t (fun x => ∑ j, f j x)

theorem JuntaSum.mul_unary {t : ℕ} {f : (Fin n → ZMod d) → ℂ} (hf : JuntaSum t f)
    (i : Fin n) (g : ZMod d → ℂ) : JuntaSum (t + 1) (fun x => g (x i) * f x) := by
  induction hf with
  | junta s hs f hf =>
    apply JuntaSum.junta (insert i s) ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ hs))
    intro x y h
    rw [h i (Finset.mem_insert_self ..), hf x y (fun j hj => h j (Finset.mem_insert_of_mem hj))]
  | sum f hf ih =>
    simp only [Finset.mul_sum]
    exact JuntaSum.sum _ ih

theorem JuntaSum.const (t : ℕ) (c : ℂ) :
    JuntaSum (n := n) (d := d) t (fun _ => c) :=
  .junta ∅ (by simp) _ (fun _ _ _ => rfl)

theorem JuntaSum.const_mul {t : ℕ} {f : (Fin n → ZMod d) → ℂ} (hf : JuntaSum t f) (c : ℂ) :
    JuntaSum t (fun x => c * f x) := by
  induction hf with
  | junta s hs f hf => exact .junta s hs _ (fun x y h => congrArg (c * ·) (hf x y h))
  | sum f hf ih =>
    simp only [Finset.mul_sum]
    exact .sum _ ih

theorem JuntaSum.matrix_mulVec {I J : Type} [Fintype J] {t : ℕ} (M : Matrix I J ℂ)
    (v : (Fin n → ZMod d) → J → ℂ) (h : ∀ j, JuntaSum t (fun x => v x j)) (i : I) :
    JuntaSum t (fun x => M.mulVec (v x) i) :=
  .sum _ (fun j => (h j).const_mul (M i j))

variable [NeZero d]

private lemma phase_act {W : Type} [Fintype W] [DecidableEq W] (ω : ℂ)
    (x : Fin n → ZMod d) (ψ : EuclideanSpace ℂ ((Fin n × ZMod d) × W))
    (p : (Fin n × ZMod d) × W) :
    QAlgorithms.act (Matrix.kronecker (phaseQuery ω x) (1 : Matrix W W ℂ)) ψ p =
      ω ^ (p.1.2 * x p.1.1).val * ψ p := by
  unfold phaseQuery Matrix.kronecker
  rw [← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal]
  exact (Matrix.mulVec_diagonal _ _ _).trans (by simp)

private lemma state_juntaSum {W : Type} [Fintype W] [DecidableEq W] {T : ℕ}
    (ω : ℂ) (alg : QAlgorithms.QueryAlg (Fin n) (ZMod d) W T) (t : Fin (T + 1)) :
    ∀ q, JuntaSum t.val (fun x => alg.stateAt (phaseQuery ω x) t q) := by
  induction t using Fin.induction with
  | zero =>
    intro q
    exact JuntaSum.junta ∅ (by simp) _ (fun _ _ _ => rfl)
  | succ i ih =>
    intro q
    simp only [QAlgorithms.QueryAlg.stateAt, Fin.induction_succ]
    change JuntaSum (i.val + 1) (fun x => ∑ p, (alg.U i.succ : Matrix _ _ ℂ) q p *
      QAlgorithms.act (Matrix.kronecker (phaseQuery ω x) (1 : Matrix W W ℂ))
        (alg.stateAt (phaseQuery ω x) i.castSucc) p)
    simp only [phase_act, ← mul_assoc]
    exact JuntaSum.sum _ (fun p => JuntaSum.mul_unary (ih p) p.1.1
      (fun a => (alg.U i.succ : Matrix _ _ ℂ) q p * ω ^ (p.1.2 * a).val))

private lemma sum_star_ket {w : ZMod d} (hw : w ≠ 0) :
    ∑ a : ZMod d, star (fourierKet w a) = 0 := by
  have hchar (a : ZMod d) :
      Complex.exp (2 * Real.pi * Complex.I * (a.val : ℂ) / (d : ℂ)) = ZMod.stdAddChar a := by
    simpa using (ZMod.stdAddChar_coe (N := d) (a.val : ℤ)).symm
  have hzero : ∑ a : ZMod d, ZMod.stdAddChar (w * a) = 0 :=
    AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar d hw)
  rw [← star_sum]
  change star (∑ a : ZMod d, ((Real.sqrt d)⁻¹ : ℂ) * _) = 0
  simp only [hchar, ← Finset.mul_sum, hzero, mul_zero, star_zero]

private lemma junta_fourier_zero (s : Finset (Fin n)) (f : (Fin n → ZMod d) → ℂ)
    (hf : ∀ x y, (∀ j ∈ s, x j = y j) → f x = f y)
    (z : Fin n → ZMod d) (hz : s.card < fourierWeight z) :
    ∑ x, star (fourierVec z x) * f x = 0 := by
  classical
  obtain ⟨i, hzi, his⟩ := Finset.exists_mem_notMem_of_card_lt_card hz
  have hne : z i ≠ 0 := (Finset.mem_filter.mp hzi).2
  let e := Equiv.funSplitAt i (ZMod d)
  rw [← e.symm.sum_comp (fun x => star (fourierVec z x) * f x), Fintype.sum_prod_type_right]
  apply Finset.sum_eq_zero
  intro y _
  let x (a : ZMod d) := e.symm (a, y)
  have hxi (a) : x a i = a := by simp [x, e, Equiv.funSplitAt_symm_apply]
  have hoff (a) (j : Fin n) (hj : j ≠ i) : x a j = x 0 j := by
    simp [x, e, Equiv.funSplitAt_symm_apply, hj]
  have hproduct (a) : fourierVec z (x a) =
      fourierKet (z i) a * ∏ j ∈ Finset.univ.erase i, fourierKet (z j) (x 0 j) := by
    change ∏ j, fourierKet (z j) (x a j) = _
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), hxi]
    congr 1
    exact Finset.prod_congr rfl (fun j hj => by rw [hoff a j (Finset.ne_of_mem_erase hj)])
  have hf' (a) : f (x a) = f (x 0) := hf _ _ (fun j hj => hoff a j (fun h => his (h ▸ hj)))
  change ∑ a, star (fourierVec z (x a)) * f (x a) = 0
  simp only [hproduct, star_mul', hf', mul_assoc, ← Finset.sum_mul, sum_star_ket hne, zero_mul]

theorem JuntaSum.fourier_zero {t : ℕ} {f : (Fin n → ZMod d) → ℂ} (hf : JuntaSum t f)
    (z : Fin n → ZMod d) (hz : t < fourierWeight z) :
    ∑ x, star (fourierVec z x) * f x = 0 := by
  induction hf with
  | junta s hs f hf => exact junta_fourier_zero s f hf z (lt_of_le_of_lt hs hz)
  | sum f hf ih =>
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero (fun j _ => ih j)

end

-- The published statement assumes a root of unity. The degree bound uses only locality.
set_option linter.unusedVariables false in
/-- **Corollary 2.9** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query
Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256
814fe20e…), p.10, in the setting of p.9: "We focus on the domain X = Zm and the input
distribution being the uniform distribution on Xn"). The state of any quantum query algorithm
that makes at most `t` queries to its input is a linear combination of states whose input register
in the Fourier basis `|ẑ⟩` has the property that `z` contains at most `t` non-0 entries.

Stated for every `T`-query algorithm `alg` with phase queries `phaseQuery ω x` (`ω ^ d = 1`) on
inputs `x ∈ Z_dⁿ`, every number of queries `t ≤ T` (the intermediate state `alg.stateAt _ t`),
every computational basis state `q` of the algorithm registers `QPW`, and every frequency `z` with
more than `t` nonzero entries: `Σ_x conj(⟨x|ẑ⟩) · ⟨q|ψ_t^x⟩ = 0`.

**Formalization Note** For the uniform input the joint state after `t` queries is
`Σ_x d^{-n/2} |ψ_t^x⟩|x⟩`; its input-register component at the basis state `q` is
`φ_q = Σ_x d^{-n/2} ψ_t^x(q) |x⟩`, and `⟨ẑ|φ_q⟩` is `d^{-n/2}` times the displayed sum. "A linear
combination of `|q⟩ ⊗ |ẑ⟩` with at most `t` nonzero `z_i`" is exactly the vanishing of this sum for
every `q` and every `z` of weight `> t`. The Fourier basis uses the primitive root `exp(2πi/d)`;
the oracle root `ω` is any `d`-th root of unity. -/
private theorem submission_proof {W : Type} [Fintype W] [DecidableEq W] {n d T : ℕ} [NeZero d] (ω : ℂ)
    (hω : ω ^ d = 1) (alg : QAlgorithms.QueryAlg (Fin n) (ZMod d) W T) (t : Fin (T + 1))
    (q : (Fin n × ZMod d) × W) (z : Fin n → ZMod d) (hz : t.val < fourierWeight z) :
    ∑ x : Fin n → ZMod d, star (fourierVec z x) * alg.stateAt (phaseQuery ω x) t q = 0 := by
  exact JuntaSum.fourier_zero (state_juntaSum ω alg t q) z hz

end QNoiseStab
end

section
open QNoiseStab

set_option linter.unusedVariables false in
theorem solution :
    ∀ {W : Type} [Fintype W] [DecidableEq W] {n d T : ℕ} [NeZero d] (ω : ℂ)
        (hω : ω ^ d = 1) (alg : QAlgorithms.QueryAlg (Fin n) (ZMod d) W T) (t : Fin (T + 1))
        (q : (Fin n × ZMod d) × W) (z : Fin n → ZMod d) (hz : t.val < fourierWeight z),
      ∑ x : Fin n → ZMod d, star (fourierVec z x) * alg.stateAt (phaseQuery ω x) t q = 0 :=
  @QNoiseStab.submission_proof

end
