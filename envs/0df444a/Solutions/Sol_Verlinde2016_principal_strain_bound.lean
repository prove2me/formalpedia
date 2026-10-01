-- Prove2me | solution 1 for Verlinde2016.principal_strain_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:17:38.173509+00:00
-- url     : https://prove2.me/submissions/9a38aa37-dd07-4f54-81b9-39be02a8e72d

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

private theorem traceless_eigenvalue {n : ℕ} (hn : 0 < n)
    (E : Matrix (Fin n) (Fin n) ℝ) (htr : E.trace=0)
    (ε : ℝ) (v : Fin n → ℝ) (hv : v ≠ 0) (hev : E.mulVec v=ε • v) :
    ε^2 ≤ ((n : ℝ)-1)/(n : ℝ)*(∑ i,∑ j,E i j^2) := by
  classical
  let S := ∑ i,(v i)^2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hS : 0 < S := by
    have hh : 0 ≤ S := Finset.sum_nonneg (fun i hi => sq_nonneg _)
    by_contra he
    have hzero : S=0 := by linarith
    apply hv
    funext i
    have hi : (v i)^2 ≤ S := Finset.single_le_sum (fun j hj => sq_nonneg _) (Finset.mem_univ i)
    have hvi : v i=0 := by nlinarith [sq_nonneg (v i)]
    exact hvi
  let a := S/(n : ℝ)
  let B := fun i j => v i*v j-(if i=j then a else 0)
  have hev' (i) : (∑ j,E i j*v j)=ε*v i := by
    have hh := congrFun hev i
    simpa only [Matrix.mulVec, dotProduct,Pi.smul_apply,smul_eq_mul] using hh
  have hrow (i) : (∑ j,E i j*B i j)=ε*(v i)^2-E i i*a := by
    calc
      _ = ∑ j,(v i*(E i j*v j)-(if i=j then E i i*a else 0)) := by
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [B]
        split_ifs with hij
        · subst j;ring
        · ring
      _ = ε*(v i)^2-E i i*a := by
        rw [Finset.sum_sub_distrib,← Finset.mul_sum,hev']
        simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
        ring
  have hcross : (∑ i,∑ j,E i j*B i j)=ε*S := by
    simp only [hrow,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul]
    change ε*S-(∑ i,E i i)*a=_
    change (∑ i,E i i)=0 at htr
    rw [htr]
    ring
  have hbrow (i) : (∑ j,(B i j)^2)=(v i)^2*S+(a^2-2*(v i)^2*a) := by
    calc
      _ = ∑ j,((v i)^2*(v j)^2+(if i=j then a^2-2*(v i)^2*a else 0)) := by
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [B]
        split_ifs with hij
        · subst j;ring
        · ring
      _ = _ := by
        rw [Finset.sum_add_distrib,← Finset.mul_sum]
        simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
        rfl
  have hbsum : (∑ i,∑ j,(B i j)^2)=S^2*((n : ℝ)-1)/(n : ℝ) := by
    simp only [hbrow,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_mul,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hsum : (∑ i,2*(v i)^2)=2*S := by rw [← Finset.mul_sum]
    rw [hsum]
    dsimp [a]
    field_simp
    ring
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin n))
    (fun ij => E ij.1 ij.2) (fun ij => B ij.1 ij.2)
  simp only [Fintype.sum_prod_type] at hCS
  rw [hcross,hbsum] at hCS
  have hSq : 0 < S^2 := sq_pos_of_pos hS
  apply (mul_le_mul_iff_right₀ hSq).mp
  convert hCS using 1 <;> ring

theorem solution (d : ℕ) (hd : 2 ≤ d)
    (E : Matrix (Fin (d-1)) (Fin (d-1)) ℝ) (hE : E.IsSymm) (htr : E.trace=0)
    (ε : ℝ) (v : Fin (d-1) → ℝ) (hv : v ≠ 0) (hev : E.mulVec v=ε • v) :
    ε^2 ≤ ((d : ℝ)-2)/((d : ℝ)-1)*(∑ i,∑ j,E i j^2) := by
  have hh := traceless_eigenvalue (show 0 < d-1 by omega) E htr ε v hv hev
  have hn : ((d-1 : ℕ) : ℝ)=(d : ℝ)-1 := by rw [Nat.cast_sub (by omega)];norm_num
  rw [hn] at hh
  convert hh using 1 <;> ring
