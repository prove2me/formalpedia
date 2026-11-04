-- Prove2me | solution 1 for PfisterCEP.graph_heisenberg_equations
-- status  : ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-11-04T02:02:56.880837+00:00
-- url     : https://prove2.me/submissions/23ae3c6a-b25c-4139-af4b-e0095bda56b2

import Mathlib
import Definitions.Def_PfisterCEP_IsCCR
import Definitions.Def_PfisterCEP_graphHamiltonian
import Definitions.Def_PfisterCEP_heisenbergGen

open PfisterCEP

namespace GraphHeisenbergProof

variable {A : Type*} [Ring A] [Algebra ℂ A]

private def commRight (x : A) : A →ₗ[ℂ] A where
  toFun y := y * x - x * y
  map_add' y z := by simp only [add_mul, mul_add]; abel
  map_smul' c y := by
    simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_sub, RingHom.id_apply]

private lemma commRight_mul (x y z : A) :
    commRight x (y * z) = y * commRight x z + commRight x y * z := by
  simp only [commRight, LinearMap.coe_mk, AddHom.coe_mk]
  noncomm_ring

private lemma quad_comm {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.IsSymm)
    (b : Fin N → A) (x : A) (k : Fin N) (r : ℂ)
    (h : ∀ n, commRight x (b n) = if k = n then r • (1 : A) else 0) :
    commRight x (∑ n, ∑ p, (G n p : ℂ) • (b n * b p)) =
      (r + r) • ∑ p, (G k p : ℂ) • b p := by
  classical
  simp only [map_sum, map_smul, commRight_mul, h, mul_ite, ite_mul,
    mul_zero, zero_mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, mul_one, one_mul,
    smul_add, smul_ite, smul_zero, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp
  simp_rw [hG.apply k]
  have hsc (p : Fin N) : G k p • r • b p = r • (G k p • b p) := smul_comm _ _ _
  simp only [hsc, ← Finset.smul_sum, add_smul]

end GraphHeisenbergProof

open GraphHeisenbergProof

theorem solution {A : Type*} [Ring A] [Algebra ℂ A] {N : ℕ}
    (a ad : Fin N → A) (hccr : IsCCR a ad) (ħ κ : ℝ) (hħ : ħ ≠ 0)
    (G : Matrix (Fin N) (Fin N) ℝ) (hG : G.IsSymm) (k : Fin N) :
    heisenbergGen ħ (graphHamiltonian ħ κ G a ad) (a k) =
      (κ : ℂ) • ∑ p, (G k p : ℂ) • ad p ∧
    heisenbergGen ħ (graphHamiltonian ħ κ G a ad) (ad k) =
      (κ : ℂ) • ∑ p, (G k p : ℂ) • a p := by
  classical
  have had (n : Fin N) : commRight (a k) (ad n) =
      if k = n then (-1 : ℂ) • (1 : A) else 0 := by
    change ad n * a k - a k * ad n = _
    rw [show ad n * a k - a k * ad n = -(a k * ad n - ad n * a k) by abel]
    rw [hccr.1 k n]
    split_ifs <;> simp
  have ha (n : Fin N) : commRight (ad k) (a n) =
      if k = n then (1 : ℂ) • (1 : A) else 0 := by
    change a n * ad k - ad k * a n = _
    rw [hccr.1 n k]
    by_cases h : k = n <;> simp [h, eq_comm]
  have hzeroa (n : Fin N) : commRight (a k) (a n) =
      if k = n then (0 : ℂ) • (1 : A) else 0 := by
    simp [commRight, hccr.2.1 n k]
  have hzeroad (n : Fin N) : commRight (ad k) (ad n) =
      if k = n then (0 : ℂ) • (1 : A) else 0 := by
    simp [commRight, hccr.2.2 n k]
  have hneg := quad_comm G hG ad (a k) k (-1) had
  have hpos := quad_comm G hG a (ad k) k 1 ha
  have hza := quad_comm G hG a (a k) k 0 hzeroa
  have hzd := quad_comm G hG ad (ad k) k 0 hzeroad
  simp only [zero_add, zero_smul] at hza hzd
  have hrev : (∑ n, ∑ p, (G n p : ℂ) • (a p * a n)) =
      ∑ n, ∑ p, (G n p : ℂ) • (a n * a p) := by
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro p _
    rw [hccr.2.1 p n]
  change (Complex.I / (ħ : ℂ)) • commRight (a k) (graphHamiltonian ħ κ G a ad) = _ ∧
    (Complex.I / (ħ : ℂ)) • commRight (ad k) (graphHamiltonian ħ κ G a ad) = _
  unfold graphHamiltonian
  rw [hrev]
  simp only [map_add, map_smul, hneg, hpos, hza, hzd, smul_zero, zero_add, add_zero, smul_smul]
  have hh : (ħ : ℂ) ≠ 0 := by exact_mod_cast hħ
  constructor <;> congr 1 <;> field_simp <;> ring_nf <;> simp [Complex.I_sq]
