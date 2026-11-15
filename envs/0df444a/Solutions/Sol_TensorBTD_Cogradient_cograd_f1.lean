-- Prove2me | solution 1 for TensorBTD.Cogradient.cograd_f1
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-14T13:58:12.817892+00:00
-- url     : https://prove2.me/submissions/c1031d0d-b832-468f-839e-f4a1a311c1b7

import Definitions.Def_TensorBTD_Cogradient_Setting
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open TensorBTD.Gramian (GIdx Col Tensor cpdFactor)
open TensorBTD.Cogradient Matrix

private lemma V_shift {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (x : GIdx I L → ℂ) (n : Fin P ⊕ Fin Q) (r : Col L) (i : Fin (I n))
    (t : ℂ) : V {n} (cpdFactor (x + t • Pi.single (⟨n,(r,i)⟩ : GIdx I L) 1)) = V {n} (cpdFactor x) := by
  classical
  ext ρ c
  apply Finset.prod_congr rfl
  intro m hm
  have hmn : m.1 ≠ n := by simpa using m.2
  have hidx : (⟨m.1,(c,ρ m)⟩ : GIdx I L) ≠ ⟨n,(r,i)⟩ := by
    intro h
    exact hmn (congrArg Sigma.fst h)
  simp [cpdFactor, Pi.single_eq_of_ne hidx]

private lemma model_shift {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (x : GIdx I L → ℂ) (n : Fin P ⊕ Fin Q) (r : Col L) (i j : Fin (I n))
    (ρ : KRIdx I {n}) (t : ℂ) :
    (cpdFactor (x + t • Pi.single (⟨n,(r,i)⟩ : GIdx I L) 1) n *
      (V {n} (cpdFactor (x + t • Pi.single (⟨n,(r,i)⟩ : GIdx I L) 1)))ᵀ : Matrix (Fin (I n)) (KRIdx I {n}) ℂ) j ρ =
    (cpdFactor x n * (V {n} (cpdFactor x))ᵀ : Matrix (Fin (I n)) (KRIdx I {n}) ℂ) j ρ +
      t * (if j = i then V {n} (cpdFactor x) ρ r else 0) := by
  classical
  rw [V_shift]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, cpdFactor, Matrix.of_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, mul_assoc]
  congr 1
  rw [← Finset.mul_sum]
  congr 1
  by_cases hji : j = i
  · subst j
    simp [Pi.single_apply, ite_and, eq_comm, ite_mul]
  · have hij : i ≠ j := Ne.symm hji
    simp [Pi.single_apply, hji, hij]

set_option maxRecDepth 4096 in
private lemma wirtinger_sum_norm {X S : Type*} [DecidableEq X] [Fintype S]
    (f : (X → ℂ) → ℂ) (x : X → ℂ) (β : X) (a b : S → ℂ)
    (h : ∀ t : ℂ, f (x + t • Pi.single β 1) =
      ∑ s, starRingEnd ℂ (a s + t * b s) * (a s + t * b s)) :
    cograd f x β = ∑ s, starRingEnd ℂ (a s) * b s := by
  have hd (a b : ℂ) : HasDerivAt (fun t : ℝ => a + (t : ℂ) * b) b 0 := by
    simpa using (((hasDerivAt_id (0 : ℂ)).mul_const b).const_add a).comp_ofReal
  have hdterm (c : ℂ) (s : S) : HasDerivAt (fun t : ℝ =>
      starRingEnd ℂ (a s + (t : ℂ) * (c * b s)) * (a s + (t : ℂ) * (c * b s)))
      (starRingEnd ℂ (c * b s) * a s + starRingEnd ℂ (a s) * (c * b s)) 0 := by
    have h₁ := (((hasDerivAt_id (0 : ℂ)).mul_const (starRingEnd ℂ (c * b s))).const_add
      (starRingEnd ℂ (a s)))
    have h₂ := (((hasDerivAt_id (0 : ℂ)).mul_const (c * b s)).const_add (a s))
    have hp := (h₁.fun_mul h₂).comp_ofReal
    convert hp using 1
    · funext t
      rw [map_add (starRingEnd ℂ), map_mul (starRingEnd ℂ)]
      have hreal : starRingEnd ℂ (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
      rw [hreal]
      simp only [id_eq]
    · simp only [id_eq, zero_mul, add_zero, one_mul]
  have hh (c : ℂ) : HasDerivAt (fun t : ℝ => ∑ s,
      starRingEnd ℂ (a s + (t : ℂ) * (c * b s)) * (a s + (t : ℂ) * (c * b s)))
      (∑ s : S, (starRingEnd ℂ (c * b s) * a s + starRingEnd ℂ (a s) * (c * b s))) 0 := by
    exact HasDerivAt.fun_sum (u := Finset.univ) (fun s _ => hdterm c s)
  have hr := hh 1
  have hi := hh Complex.I
  unfold cograd
  simp_rw [h]
  simp only [one_mul] at hr
  simp only [mul_assoc]
  rw [hr.deriv, hi.deriv]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  simp [map_mul, mul_assoc] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

private lemma v_gram {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (x : GIdx I L → ℂ) (n : Fin P ⊕ Fin Q) :
    (V {n} (cpdFactor x))ᴴ * V {n} (cpdFactor x) = W {n} (cpdFactor x) := by
  classical
  ext c c'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, V, W]
  simp_rw [star_prod, ← Finset.prod_mul_distrib]
  rw [Finset.prod_subtype (p := fun m : Fin P ⊕ Fin Q => m ∉ ({n} : Finset _)) (Finset.univ.filter (· ∉ ({n} : Finset _))) (by simp)]
  exact (Fintype.prod_sum (fun (m : {m : Fin P ⊕ Fin Q // m ∉ ({n} : Finset _)})
    (i : Fin (I m.1)) => starRingEnd ℂ (cpdFactor x m.1 i c) * cpdFactor x m.1 i c')).symm

theorem solution {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ} (x : TensorBTD.Gramian.GIdx I L → ℂ)
    (n : Fin P ⊕ Fin Q) :
    cogradMatG (fOne n) x n = (TensorBTD.Gramian.cpdFactor x n).map (starRingEnd ℂ) * W {n} (TensorBTD.Gramian.cpdFactor x) := by
  classical
  ext i r
  change cograd (fOne n) x ⟨n,(r,i)⟩ = _
  have he (t : ℂ) : fOne n (x + t • Pi.single (⟨n,(r,i)⟩ : GIdx I L) 1) =
      ∑ s : Fin (I n) × KRIdx I {n},
        starRingEnd ℂ ((cpdFactor x n * (V {n} (cpdFactor x))ᵀ) s.1 s.2 +
          t * (if s.1 = i then V {n} (cpdFactor x) s.2 r else 0)) *
        ((cpdFactor x n * (V {n} (cpdFactor x))ᵀ) s.1 s.2 +
          t * (if s.1 = i then V {n} (cpdFactor x) s.2 r else 0)) := by
    simp only [fOne, frobNormSq, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self,
      model_shift, Fintype.sum_prod_type]
  rw [wirtinger_sum_norm (fOne n) x ⟨n,(r,i)⟩ _ _ he]
  rw [Fintype.sum_prod_type]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← v_gram x n]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
    map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro ρ hρ
  simp only [starRingEnd_apply]
  ring

#print axioms solution














