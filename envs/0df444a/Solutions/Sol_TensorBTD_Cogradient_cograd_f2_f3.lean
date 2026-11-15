-- Prove2me | solution 1 for TensorBTD.Cogradient.cograd_f2_f3
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-14T13:33:43.158798+00:00
-- url     : https://prove2.me/submissions/4e6351c8-1054-4caf-9510-fd78f850b897

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

private lemma two_shift {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (T : Tensor I) (x : GIdx I L → ℂ) (n : Fin P ⊕ Fin Q) (r : Col L) (i : Fin (I n))
    (t : ℂ) : fTwo T n (x + t • Pi.single (⟨n,(r,i)⟩ : GIdx I L) 1) = fTwo T n x +
      t * (((unfolding T n).map (starRingEnd ℂ) * V {n} (cpdFactor x)) i r) := by
  classical
  simp only [fTwo, frobInner, model_shift, mul_add, Finset.sum_add_distrib]
  congr 1
  simp only [Matrix.mul_apply, Matrix.map_apply]
  rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ρ hρ
  simp [mul_ite, ite_mul, mul_assoc, mul_left_comm, mul_comm]

private lemma wirtinger_affine {X : Type*} [DecidableEq X]
    (f : (X → ℂ) → ℂ) (x : X → ℂ) (β : X) (a b : ℂ)
    (h : ∀ t : ℂ, f (x + t • Pi.single β 1) = a + t * b) :
    cograd f x β = b ∧ cograd (fun y => starRingEnd ℂ (f y)) x β = 0 := by
  have hd (c : ℂ) : HasDerivAt (fun t : ℝ => a + (t : ℂ) * c) c 0 := by
    simpa using (((hasDerivAt_id (0 : ℂ)).mul_const c).const_add a).comp_ofReal
  have hi : HasDerivAt (fun t : ℝ => a + ((t : ℂ) * Complex.I) * b) (Complex.I * b) 0 := by
    simpa only [mul_assoc] using hd (Complex.I * b)
  have hr := hd b
  constructor
  · unfold cograd
    simp_rw [h]
    rw [hr.deriv, hi.deriv]
    simp [mul_assoc] <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  · unfold cograd
    simp_rw [h]
    have hr' := hr.star
    have hi' := hi.star
    simp only [starRingEnd_apply]
    rw [hr'.deriv, hi'.deriv]
    simp [map_mul, mul_assoc] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem solution {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ} (T : TensorBTD.Gramian.Tensor I)
    (x : TensorBTD.Gramian.GIdx I L → ℂ) (n : Fin P ⊕ Fin Q) :
    cogradMatG (fTwo T n) x n = (unfolding T n).map (starRingEnd ℂ) * V {n} (TensorBTD.Gramian.cpdFactor x) ∧
    cogradMatG (fun y => starRingEnd ℂ (fTwo T n y)) x n = 0 ∧
    cogradMatG (fun _ : TensorBTD.Gramian.GIdx I L → ℂ => fThree T n) x n = 0 := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · ext i r
    exact (wirtinger_affine (fTwo T n) x ⟨n,(r,i)⟩ (fTwo T n x) _ (two_shift T x n r i)).1
  · ext i r
    exact (wirtinger_affine (fTwo T n) x ⟨n,(r,i)⟩ (fTwo T n x) _ (two_shift T x n r i)).2
  · ext i r
    simp [cogradMatG, cograd]

#print axioms solution






