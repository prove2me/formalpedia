-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P22.oddProperSectorMarginals
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T21:28:26.718731+00:00
-- url     : https://prove2.me/submissions/be542113-2e03-4491-8a88-f4edfab55d4f

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

open scoped ComplexConjugate ComplexOrder Matrix Kronecker

noncomputable section

namespace X8P22
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22 Matrix


theorem x8_to_mul {I : Type} [Fintype I] [DecidableEq I] (M N : I → Op Bool) :
    tensorOps M * tensorOps N = tensorOps (fun i => M i * N i) := by
  ext a b
  simp only [tensorOps, mul_apply]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.prod_mul_distrib]

theorem x8_to_one {I : Type} [Fintype I] [DecidableEq I] :
    tensorOps (fun _ : I => (1 : Op Bool)) = 1 := by
  ext a b
  simp only [tensorOps, one_apply]
  rw [Finset.prod_ite_zero]
  simp only [Finset.prod_const_one, Finset.mem_univ, true_implies]
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg (fun h' => h (funext h')), if_neg h]

theorem x8_to_trace {I : Type} [Fintype I] [DecidableEq I] (M : I → Op Bool) :
    (tensorOps M).trace = ∏ i, (M i).trace := by
  simp only [trace, diag, tensorOps]
  rw [Fintype.prod_sum]

theorem x8_to_neg1 (x : Op Bool) :
    tensorOps (fun _ : Fin 1 => -x) = -tensorOps (fun _ : Fin 1 => x) := by
  ext a b
  simp [tensorOps]

theorem x8_to_H {I : Type} [Fintype I] (M : I → Op Bool) :
    (tensorOps M)ᴴ = tensorOps (fun i => (M i)ᴴ) := by
  ext a b
  simp [tensorOps, conjTranspose_apply]

/-- the sector tensor product. -/
def x8st {m k : ℕ} (M : Fin k → Op (Bool × Qubits m)) : Op (Qubits k × Signals m k) :=
  fun a b => ∏ j, M j (a.1 j, fun i => a.2 (j,i)) (b.1 j, fun i => b.2 (j,i))

def x8e (m k : ℕ) : (Qubits k × Signals m k) ≃ (Fin k → Bool × Qubits m) where
  toFun c j := (c.1 j, fun i => c.2 (j,i))
  invFun g := (fun j => (g j).1, fun w => (g w.1).2 w.2)
  left_inv c := by ext <;> simp
  right_inv g := by funext j; simp

theorem x8_st_mul {m k : ℕ} (M N : Fin k → Op (Bool × Qubits m)) :
    x8st M * x8st N = x8st (fun j => M j * N j) := by
  ext a b
  simp only [x8st, mul_apply]
  rw [Fintype.prod_sum, ← (x8e m k).sum_comp]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.prod_mul_distrib]
  rfl

theorem x8_st_H {m k : ℕ} (M : Fin k → Op (Bool × Qubits m)) :
    (x8st M)ᴴ = x8st (fun j => (M j)ᴴ) := by
  ext a b
  simp [x8st, conjTranspose_apply]

def x8sz {m k : ℕ} (z : Fin k → Op (Qubits m)) : Op (Signals m k) :=
  fun s s' => ∏ j, z j (fun i => s (j,i)) (fun i => s' (j,i))

theorem x8_st_kron {m k : ℕ} (y : Fin k → Op Bool) (z : Fin k → Op (Qubits m)) :
    x8st (fun j => y j ⊗ₖ z j) = tensorOps y ⊗ₖ x8sz z := by
  ext a b
  simp only [x8st, kroneckerMap_apply, tensorOps, x8sz, Finset.prod_mul_distrib]

theorem x8_sz_one {m k : ℕ} : x8sz (fun _ : Fin k => (1 : Op (Qubits m))) = 1 := by
  ext s s'
  simp only [x8sz, one_apply]
  rw [Finset.prod_ite_zero]
  simp only [Finset.prod_const_one, Finset.mem_univ, true_implies]
  by_cases h : s = s'
  · subst h; simp
  · rw [if_neg, if_neg h]
    intro h'
    apply h; funext w
    exact congrFun (h' w.1) w.2

/-- abstract conjugation by a quarter rotation. -/
theorem x8_c2 : (((Real.sqrt 2)⁻¹ : ℂ)) * (((Real.sqrt 2)⁻¹ : ℂ)) = 2⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  simp

theorem x8_qr_H {I : Type} [Fintype I] [DecidableEq I] (M : Op I) (hM : Mᴴ = M) :
    (quarterRotation M)ᴴ = ((Real.sqrt 2)⁻¹ : ℂ) • (1 + Complex.I • M) := by
  unfold quarterRotation
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hM]
  simp only [star_inv₀, RCLike.star_def, Complex.conj_ofReal, Complex.conj_I]
  rw [neg_smul, sub_neg_eq_add]

theorem x8_qr_conj {I : Type} [Fintype I] [DecidableEq I] (M A : Op I) (hM : Mᴴ = M) :
    (quarterRotation M)ᴴ * A * quarterRotation M =
      (2⁻¹ : ℂ) • (A + Complex.I • (M * A - A * M) + M * A * M) := by
  rw [x8_qr_H M hM]
  unfold quarterRotation
  rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, x8_c2]
  congr 1
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, smul_sub, smul_smul, Complex.I_mul_I]
  rw [smul_add, smul_smul, Complex.I_mul_I]
  module

theorem x8_qr_comm {I : Type} [Fintype I] [DecidableEq I] (M A : Op I) (hM : Mᴴ = M)
    (hMM : M * M = 1) (h : A * M = M * A) :
    (quarterRotation M)ᴴ * A * quarterRotation M = A := by
  rw [x8_qr_conj M A hM, h, sub_self, smul_zero, add_zero, ← h, Matrix.mul_assoc, hMM,
    Matrix.mul_one, ← two_smul ℂ A, smul_smul]
  norm_num

theorem x8_qr_anti {I : Type} [Fintype I] [DecidableEq I] (M A : Op I) (hM : Mᴴ = M)
    (hMM : M * M = 1) (h : A * M = -(M * A)) :
    (quarterRotation M)ᴴ * A * quarterRotation M = Complex.I • (M * A) := by
  rw [x8_qr_conj M A hM, Matrix.mul_assoc M A M, h, Matrix.mul_neg, ← Matrix.mul_assoc, hMM,
    Matrix.one_mul]
  rw [sub_neg_eq_add, ← two_smul ℂ (M * A), smul_smul]
  have : A + (Complex.I * 2) • (M * A) + -A = (Complex.I * 2) • (M * A) := by abel
  rw [this, smul_smul]
  congr 1
  ring


theorem x8_ax_H (P : Axis) : (axisMatrix P)ᴴ = axisMatrix P := by
  cases P <;> ext i j <;> cases i <;> cases j <;>
    simp [axisMatrix, pauliX, pauliY, pauliZ, conjTranspose_apply]

theorem x8_ax_sq (P : Axis) : axisMatrix P * axisMatrix P = 1 := by
  cases P <;> ext i j <;> cases i <;> cases j <;>
    simp [axisMatrix, pauliX, pauliY, pauliZ, mul_apply, Fintype.sum_bool]

theorem x8_ax_anti (P Q : Axis) (h : P ≠ Q) :
    axisMatrix P * axisMatrix Q = -(axisMatrix Q * axisMatrix P) := by
  cases P <;> cases Q <;> simp at h <;> ext i j <;> cases i <;> cases j <;>
    simp [axisMatrix, pauliX, pauliY, pauliZ, mul_apply, Fintype.sum_bool]

theorem x8_ax_tr (P Q : Axis) (h : P ≠ Q) : (axisMatrix P * axisMatrix Q).trace = 0 := by
  cases P <;> cases Q <;> simp at h <;>
    simp [axisMatrix, pauliX, pauliY, pauliZ, mul_apply, Fintype.sum_bool, trace]


theorem x8_kk (a b c d : Op Bool) : (a ⊗ₖ (tensorOps fun _ : Fin 1 => b)) * (c ⊗ₖ (tensorOps fun _ : Fin 1 => d)) = (a * c) ⊗ₖ (tensorOps fun _ : Fin 1 => b * d) := by
  rw [← mul_kronecker_mul, x8_to_mul]

theorem neg_kronecker {I J : Type} (a : Op I) (b : Op J) : (-a) ⊗ₖ b = -(a ⊗ₖ b) := by
  ext; simp

theorem kronecker_neg {I J : Type} (a : Op I) (b : Op J) : a ⊗ₖ (-b) = -(a ⊗ₖ b) := by
  ext; simp

theorem x8_M_H (P : Axis) : (axisMatrix P ⊗ₖ (tensorOps fun _ : Fin 1 => axisMatrix P))ᴴ =
    axisMatrix P ⊗ₖ (tensorOps fun _ : Fin 1 => axisMatrix P) := by
  rw [conjTranspose_kronecker, x8_to_H, x8_ax_H]

theorem x8_M_sq (P : Axis) : (axisMatrix P ⊗ₖ (tensorOps fun _ : Fin 1 => axisMatrix P)) *
    (axisMatrix P ⊗ₖ (tensorOps fun _ : Fin 1 => axisMatrix P)) = 1 := by
  rw [x8_kk, x8_ax_sq, x8_to_one, one_kronecker_one]

theorem x8_sector_one (P Q : Axis) :
    (sectorEncoder 1 P Q)ᴴ * 1 * sectorEncoder 1 P Q = 1 := by
  unfold sectorEncoder
  simp only [Matrix.kronecker]
  rw [conjTranspose_mul]
  have e : ∀ A B C D : Op (Bool × Qubits 1), A * B * 1 * (C * D) = A * (B * 1 * C) * D := by
    intro A B C D; simp only [Matrix.mul_assoc]
  rw [e, x8_qr_comm _ _ (x8_M_H P) (x8_M_sq P) (by simp), Matrix.mul_one,
    ← Matrix.mul_one (quarterRotation (axisMatrix Q ⊗ₖ (tensorOps fun _ : Fin 1 => axisMatrix Q)))ᴴ,
    x8_qr_comm _ _ (x8_M_H Q) (x8_M_sq Q) (by simp)]

theorem x8_sector (P Q : Axis) (h : P ≠ Q) :
    (sectorEncoder 1 P Q)ᴴ * (1 ⊗ₖ (tensorOps fun _ : Fin 1 => axisMatrix P * axisMatrix Q)) * sectorEncoder 1 P Q =
      (-(axisMatrix Q * axisMatrix P)) ⊗ₖ 1 := by
  unfold sectorEncoder
  simp only [Matrix.kronecker]
  rw [conjTranspose_mul]
  have e : ∀ A B C D E : Op (Bool × Qubits 1), A * B * E * (C * D) = A * (B * E * C) * D := by
    intro A B C D E; simp only [Matrix.mul_assoc]
  have hpq := x8_ax_anti P Q h
  have hp := x8_ax_sq P
  have hqp : axisMatrix Q * axisMatrix P = -(axisMatrix P * axisMatrix Q) := by rw [hpq, neg_neg]
  have hq := x8_ax_sq Q
  rw [e, x8_qr_anti _ _ (x8_M_H P) (x8_M_sq P)]
  · rw [x8_kk, Matrix.mul_one, ← Matrix.mul_assoc, hp, Matrix.one_mul]
    rw [x8_qr_anti _ _ (x8_M_H Q) (x8_M_sq Q)]
    · rw [Matrix.mul_smul, x8_kk, smul_smul, Complex.I_mul_I, hq, x8_to_one, neg_one_smul,
        neg_kronecker]
    · rw [Matrix.mul_smul, Matrix.smul_mul, x8_kk, x8_kk, hq, hpq, neg_kronecker, smul_neg]
  · rw [x8_kk, x8_kk, Matrix.one_mul, Matrix.mul_one, ← Matrix.mul_assoc, hp, Matrix.one_mul,
      Matrix.mul_assoc, hqp, Matrix.mul_neg, ← Matrix.mul_assoc, hp, Matrix.one_mul, x8_to_neg1,
      kronecker_neg]

end X8P22
namespace X8P22
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22 Matrix

theorem x8_marg_tensor {W : Type} [Fintype W] [DecidableEq W] (J : Finset W) (M : W → Op Bool) :
    marginal J (tensorOps M) = (∏ w ∈ Jᶜ, (M w).trace) • tensorOps (fun j : J => M j) := by
  ext a b
  let g : W → Bool → Bool → ℂ := fun w s t =>
    if h : w ∈ J then (if s = a ⟨w, h⟩ ∧ t = b ⟨w, h⟩ then M w s t else 0)
    else (if s = t then M w s t else 0)
  have hs : ∀ x y : W → Bool, (if (∀ j : J, x j = a j) ∧ (∀ j : J, y j = b j) ∧
      (∀ w, w ∉ J → x w = y w) then tensorOps M x y else 0) = ∏ w, g w (x w) (y w) := by
    intro x y
    split_ifs with hc
    · simp only [tensorOps]
      refine Finset.prod_congr rfl fun w _ => ?_
      by_cases hw : w ∈ J
      · simp only [g, dif_pos hw, hc.1 ⟨w, hw⟩, hc.2.1 ⟨w, hw⟩, and_self, if_true]
      · simp only [g, dif_neg hw, hc.2.2 w hw, if_true]
    · symm
      apply Finset.prod_eq_zero_iff.mpr
      by_contra hne
      push_neg at hne
      apply hc
      refine ⟨fun j => ?_, fun j => ?_, fun w hw => ?_⟩
      · have := hne j.1 (Finset.mem_univ _)
        simp only [g, dif_pos j.2] at this
        by_contra h1; exact this (if_neg (by tauto))
      · have := hne j.1 (Finset.mem_univ _)
        simp only [g, dif_pos j.2] at this
        by_contra h1; exact this (if_neg (by tauto))
      · have := hne w (Finset.mem_univ _)
        simp only [g, dif_neg hw] at this
        by_contra h1; exact this (if_neg h1)
  simp only [marginal, hs]
  have h1 : ∑ x : W → Bool, ∑ y : W → Bool, ∏ w, g w (x w) (y w) = ∏ w, ∑ s, ∑ t, g w s t := by
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.prod_sum]
  rw [h1, ← Finset.prod_mul_prod_compl J, Matrix.smul_apply, smul_eq_mul, mul_comm]
  congr 1
  · refine Finset.prod_congr rfl fun w hw => ?_
    have hw' : w ∉ J := Finset.mem_compl.mp hw
    simp only [g, dif_neg hw', trace, diag]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_ite_eq]; simp
  · rw [← Finset.prod_coe_sort J]
    simp only [tensorOps]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [g, dif_pos j.2]
    rw [Finset.sum_eq_single (a j)]
    · rw [Finset.sum_eq_single (b j)]
      · simp
      · intro t _ ht; simp [ht]
      · simp
    · intro s _ hs; apply Finset.sum_eq_zero; intro t _; simp [hs]
    · simp

theorem x8_marg_smul {W : Type} [Fintype W] [DecidableEq W] (J : Finset W) (c : ℂ) (ρ : Op (W → Bool)) :
    marginal J (c • ρ) = c • marginal J ρ := by
  ext a b
  simp only [marginal, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> simp

theorem x8_marg_sum {W ι : Type} [Fintype W] [DecidableEq W] (J : Finset W) (s : Finset ι)
    (ρ : ι → Op (W → Bool)) :
    marginal J (∑ i ∈ s, ρ i) = ∑ i ∈ s, marginal J (ρ i) := by
  ext a b
  simp only [marginal, Matrix.sum_apply]
  rw [Finset.sum_comm (s := s)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm (s := s)]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> simp

theorem x8_main_opm (m k : ℕ) (hm : 2 ≤ m) (hodd : Odd m)
    (P Q : Axis) (hPQ : P ≠ Q) (rho : Op (Signals m k))
    (hc : ResourceCriterion P Q rho) (j : Fin k) (J : Finset (Wires m k))
    (hJ : J ⊂ Finset.univ.filter (fun w => w.1 = j)) :
    marginal J rho = ((Fintype.card (J → Bool) : ℂ)⁻¹) • (1 : Op (J → Bool)) := by
  have hne : ¬ Even m := Nat.not_even_iff_odd.mpr hodd
  unfold ResourceCriterion at hc
  rw [if_neg hne] at hc
  obtain ⟨α, hα0, hρ, -⟩ := hc
  rw [hρ, x8_marg_smul, x8_marg_sum]
  have hT : ∀ c : Qubits k, marginal J ((α c : ℂ) • sectorMoment m k P Q c) =
      if c = (fun _ => false) then (2 : ℂ) ^ (Jᶜ.card) • (1 : Op (J → Bool)) else 0 := by
    intro c
    rw [x8_marg_smul, sectorMoment, x8_marg_tensor]
    split_ifs with h0
    · subst h0
      simp only [hα0, Bool.false_eq_true, if_false, Complex.ofReal_one, one_smul]
      rw [x8_to_one]
      congr 1
      rw [Finset.prod_congr rfl (fun _ _ => (show (1 : Op Bool).trace = 2 by
        simp [trace]))]
      simp
    · have : ∃ w ∈ Jᶜ, c w.1 = true := by
        by_contra hn
        push_neg at hn
        apply h0
        funext j'
        by_contra hj'
        have hj'' : c j' = true := by simpa using hj'
        by_cases hjj : j' = j
        · subst hjj
          obtain ⟨w, hw1, hw2⟩ := Finset.exists_of_ssubset hJ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw1
          have := hn w (Finset.mem_compl.mpr hw2)
          rw [hw1] at this; simp [this] at hj''
        · have hw : ((j', ⟨0, by omega⟩) : Wires m k) ∉ J := by
            intro h
            have := hJ.1 h
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
            exact hjj this
          have := hn _ (Finset.mem_compl.mpr hw)
          simp [this] at hj''
      obtain ⟨w, hw, hcw⟩ := this
      rw [Finset.prod_eq_zero hw (by rw [if_pos hcw, remaining, trace_smul, x8_ax_tr P Q hPQ, smul_zero]),
        zero_smul, smul_zero]
  simp only [hT, Finset.sum_ite_eq', Finset.mem_univ, if_true, smul_smul]
  congr 1
  have hcard : (Jᶜ).card + J.card = k * m := by
    rw [Finset.card_compl, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    have := Finset.card_le_univ J
    simp only [Fintype.card_prod, Fintype.card_fin] at this
    omega
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  have h2 : (2 : ℂ) ^ (m * k) = 2 ^ Jᶜ.card * 2 ^ J.card := by
    rw [← pow_add, hcard, mul_comm]
  push_cast
  rw [h2]
  field_simp

end X8P22

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P22


open scoped ComplexConjugate ComplexOrder Matrix


local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

open QAlgorithms.Papers.Independent.Information100.P22 in
/-- Eq.(S69), PDF pp.14,43: initial resource marginal on any proper subset of one sector. -/
theorem solution (m k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k) (hodd : Odd m)
    (P Q : Axis) (hPQ : P ≠ Q)
    (R : EuclideanSpace ℂ (Signals m k × Signals m k)) (hR : IsState R)
    (hc : ResourceCriterion P Q (rhoS R)) (j : Fin k) (J : Finset (Wires m k))
    (hJ : J ⊂ Finset.univ.filter (fun w => w.1 = j)) :
    marginal J (rhoS R) = mixed (J → Bool) :=
  by
  rw [mixed]
  convert X8P22.x8_main_opm m k hm hodd P Q hPQ (rhoS R) hc j J hJ



