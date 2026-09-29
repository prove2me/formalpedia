-- Prove2me | solution 1 for QuaternionAlgebra.IsOrder.exists_mem_dvd_nrd_forall_ne_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/ed07e516-837d-5d3f-b79e-17ab62611f4c

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_basis_span_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_QuaternionAlgebra_IsOrder_exists_mem_dvd_nrd_forall_ne_smul

set_option autoImplicit false

namespace NrdIsotropicModP

open QuaternionAlgebra MvPolynomial
open scoped Quaternion

def qform {R : Type*} [CommRing R] (N : Fin 4 → R) (T : Fin 4 → Fin 4 → R) (x : Fin 4 → R) : R :=
  N 0 * x 0 ^ 2 + N 1 * x 1 ^ 2 + N 2 * x 2 ^ 2 + N 3 * x 3 ^ 2 +
    T 0 1 * x 0 * x 1 + T 0 2 * x 0 * x 2 + T 0 3 * x 0 * x 3 +
    T 1 2 * x 1 * x 2 + T 1 3 * x 1 * x 3 + T 2 3 * x 2 * x 3

theorem map_qform {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (N : Fin 4 → R) (T : Fin 4 → Fin 4 → R) (x : Fin 4 → R) :
    f (qform N T x) = qform (fun i => f (N i)) (fun i j => f (T i j)) (fun i => f (x i)) := by
  simp only [qform, map_add, map_mul, map_pow]

variable {a b : ℚ}

def pol (u v : ℍ[ℚ, a, b]) : ℚ := nrd (u + v) - nrd u - nrd v

theorem nrd_lincomb (c : Fin 4 → ℚ) (B : Fin 4 → ℍ[ℚ, a, b]) :
    nrd (∑ i, c i • B i) = qform (fun i => nrd (B i)) (fun i j => pol (B i) (B j)) c := by
  rw [Fin.sum_univ_four]
  simp only [qform, pol]
  obtain ⟨p₀, p₁, p₂, p₃⟩ := B 0
  obtain ⟨q₀, q₁, q₂, q₃⟩ := B 1
  obtain ⟨r₀, r₁, r₂, r₃⟩ := B 2
  obtain ⟨s₀, s₁, s₂, s₃⟩ := B 3
  simp only [QuaternionAlgebra.smul_mk, QuaternionAlgebra.mk_add_mk, nrd_mk, smul_eq_mul]
  ring

theorem totalDegree_le_two_add {σ R : Type*} [CommSemiring R] {f g : MvPolynomial σ R}
    (hf : f.totalDegree ≤ 2) (hg : g.totalDegree ≤ 2) : (f + g).totalDegree ≤ 2 :=
  (totalDegree_add f g).trans (max_le hf hg)

theorem totalDegree_X_le {σ R : Type*} [CommSemiring R] (i : σ) : (X i : MvPolynomial σ R).totalDegree ≤ 1 := by
  refine (totalDegree_monomial_le _ _).trans ?_
  simp

theorem totalDegree_C_mul_X_mul_X {σ R : Type*} [CommSemiring R] (c : R) (i j : σ) :
    (C c * X i * X j : MvPolynomial σ R).totalDegree ≤ 2 := by
  refine (totalDegree_mul _ _).trans ?_
  have h1 : (C c * X i : MvPolynomial σ R).totalDegree ≤ 1 := by
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact totalDegree_X_le i
  have h2 : (X j : MvPolynomial σ R).totalDegree ≤ 1 := totalDegree_X_le j
  omega

theorem totalDegree_C_mul_X_pow_two {σ R : Type*} [CommSemiring R] (c : R) (i : σ) :
    (C c * X i ^ 2 : MvPolynomial σ R).totalDegree ≤ 2 := by
  rw [pow_two, ← mul_assoc]
  exact totalDegree_C_mul_X_mul_X c i i

theorem totalDegree_qform_le {R : Type*} [CommRing R] (N : Fin 4 → R) (T : Fin 4 → Fin 4 → R) :
    (qform (fun i => C (N i)) (fun i j => C (T i j)) (X : Fin 4 → MvPolynomial (Fin 4) R)).totalDegree ≤ 2 := by
  simp only [qform]
  refine totalDegree_le_two_add (totalDegree_le_two_add (totalDegree_le_two_add
    (totalDegree_le_two_add (totalDegree_le_two_add (totalDegree_le_two_add
    (totalDegree_le_two_add (totalDegree_le_two_add (totalDegree_le_two_add ?_ ?_) ?_) ?_) ?_)
    ?_) ?_) ?_) ?_) ?_
  exacts [totalDegree_C_mul_X_pow_two _ _, totalDegree_C_mul_X_pow_two _ _,
    totalDegree_C_mul_X_pow_two _ _, totalDegree_C_mul_X_pow_two _ _,
    totalDegree_C_mul_X_mul_X _ _ _, totalDegree_C_mul_X_mul_X _ _ _, totalDegree_C_mul_X_mul_X _ _ _,
    totalDegree_C_mul_X_mul_X _ _ _, totalDegree_C_mul_X_mul_X _ _ _, totalDegree_C_mul_X_mul_X _ _ _]

theorem main {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (p : ℕ) [Fact p.Prime] :
    ∃ h ∈ Λ, (∀ h' ∈ Λ, h ≠ (p : ℤ) • h') ∧
      ∃ n : ℤ, (n : ℚ) = QuaternionAlgebra.nrd h ∧ (p : ℤ) ∣ n := by
  classical
  obtain ⟨B, hBΛ, hspan⟩ := QuaternionAlgebra.IsOrder.exists_basis_span_eq hΛ

  have hN : ∀ i, ∃ n : ℤ, (n : ℚ) = nrd (B i) := fun i =>
    (QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hΛ (hBΛ i)).1
  choose N hN using hN
  have hT : ∀ i j, ∃ t : ℤ, (t : ℚ) = pol (B i) (B j) := by
    intro i j
    obtain ⟨m, hm⟩ := (QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hΛ
      (Λ.add_mem (hBΛ i) (hBΛ j))).1
    refine ⟨m - N i - N j, ?_⟩
    push_cast
    rw [hm, hN, hN]; rfl
  choose T hT using hT

  set f : MvPolynomial (Fin 4) (ZMod p) :=
    qform (fun i => C ((N i : ℤ) : ZMod p)) (fun i j => C ((T i j : ℤ) : ZMod p)) X with hf
  have hdeg : f.totalDegree < Fintype.card (Fin 4) := by
    rw [Fintype.card_fin]
    exact Nat.lt_of_le_of_lt (totalDegree_qform_le _ _) (by norm_num)
  have heval : ∀ x : Fin 4 → ZMod p, eval x f =
      qform (fun i => ((N i : ℤ) : ZMod p)) (fun i j => ((T i j : ℤ) : ZMod p)) x := by
    intro x
    rw [hf, map_qform]
    simp only [eval_C, eval_X]

  have hdvd := char_dvd_card_solutions p hdeg
  have h0 : eval (0 : Fin 4 → ZMod p) f = 0 := by
    rw [heval]; simp [qform]
  have hcard : 1 < Fintype.card {x : Fin 4 → ZMod p // eval x f = 0} := by
    have hpos : 0 < Fintype.card {x : Fin 4 → ZMod p // eval x f = 0} :=
      Fintype.card_pos_iff.mpr ⟨⟨0, h0⟩⟩
    exact lt_of_lt_of_le (Fact.out : p.Prime).one_lt (Nat.le_of_dvd hpos hdvd)
  obtain ⟨⟨x, hx⟩, hx0⟩ := Fintype.exists_ne_of_one_lt_card hcard ⟨0, h0⟩
  have hxne : x ≠ 0 := fun hz => hx0 (Subtype.ext hz)
  have hx' : qform (fun i => ((N i : ℤ) : ZMod p)) (fun i j => ((T i j : ℤ) : ZMod p)) x = 0 := by
    rw [← heval]; exact hx

  obtain ⟨c, hcx⟩ : ∃ c : Fin 4 → ℤ, ∀ i, ((c i : ℤ) : ZMod p) = x i :=
    ⟨fun i => ((x i).val : ℤ), fun i => by simp⟩
  obtain ⟨h, hh⟩ : ∃ h : ℍ[ℚ, a, b], h = ∑ i, c i • B i := ⟨_, rfl⟩
  have hmem : h ∈ Λ := by
    rw [hh]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hBΛ i)
  refine ⟨h, hmem, ?_, qform N T c, ?_, ?_⟩
  ·
    intro h' hh' heq
    rw [← hspan, Submodule.mem_span_range_iff_exists_fun] at hh'
    obtain ⟨y, hy⟩ := hh'
    have hlin : ∑ i, ((c i : ℚ) - (p : ℚ) * (y i : ℚ)) • B i = 0 := by
      have e1 : ∀ i, ((c i : ℚ) - (p : ℚ) * (y i : ℚ)) • B i = c i • B i - (p : ℤ) • (y i • B i) := by
        intro i
        rw [sub_smul, smul_smul, ← Int.cast_smul_eq_zsmul ℚ (c i), ← Int.cast_smul_eq_zsmul ℚ ((p : ℤ) * y i)]
        push_cast
        rfl
      simp_rw [e1]
      rw [Finset.sum_sub_distrib, ← Finset.smul_sum, hy, ← hh, heq, sub_self]
    have hli := Fintype.linearIndependent_iff.mp B.linearIndependent _ hlin
    apply hxne
    funext i
    have h2 : (c i : ℚ) = (p : ℚ) * (y i : ℚ) := sub_eq_zero.mp (hli i)
    have h3 : c i = (p : ℤ) * y i := by exact_mod_cast h2
    rw [Pi.zero_apply, ← hcx i, h3]
    simp
  ·
    have e2 : h = ∑ i, (c i : ℚ) • B i := by
      rw [hh]; exact Finset.sum_congr rfl fun i _ => (Int.cast_smul_eq_zsmul ℚ _ _).symm
    rw [e2, nrd_lincomb, show ((qform N T c : ℤ) : ℚ) = (Int.castRingHom ℚ) (qform N T c) from rfl, map_qform]
    simp only [eq_intCast, hN, hT]
  ·
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    rw [show ((qform N T c : ℤ) : ZMod p) = (Int.castRingHom (ZMod p)) (qform N T c) from rfl, map_qform]
    simpa only [eq_intCast, hcx] using hx'

end NrdIsotropicModP

open scoped Quaternion

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (p : ℕ) [Fact p.Prime] :
    ∃ h ∈ Λ, (∀ h' ∈ Λ, h ≠ (p : ℤ) • h') ∧
      ∃ n : ℤ, (n : ℚ) = QuaternionAlgebra.nrd h ∧ (p : ℤ) ∣ n :=
  NrdIsotropicModP.main hΛ p

end S_QuaternionAlgebra_IsOrder_exists_mem_dvd_nrd_forall_ne_smul
end P2MW
export P2MW.S_QuaternionAlgebra_IsOrder_exists_mem_dvd_nrd_forall_ne_smul (solution)
