-- Prove2me | solution 1 for QKPSDP.proposition_3_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:45:01.774149+00:00
-- url     : https://prove2.me/submissions/f7931b5b-9eb3-430e-8bd9-603078f3b9ff

import Mathlib
import Definitions.Def_QKPSDP_Assumption1
import Definitions.Def_QKPSDP_K
import Definitions.Def_QKPSDP_IsRegular
import Definitions.Def_QKPSDP_N

namespace Aux_QKP31

open Matrix QKPSDP

variable {r : ℕ} [NeZero r]

theorem e_apply (j : Fin r) : e1 r j = if j = 0 then 1 else 0 := by
  simp [e1, Pi.single_apply]

theorem e_zero : e1 r 0 = 1 := by simp [e1]

theorem sum_e_mul (f : Fin r → ℝ) : ∑ j, e1 r j * f j = f 0 := by
  simp [e_apply]

theorem sum_mul_e (f : Fin r → ℝ) : ∑ j, f j * e1 r j = f 0 := by
  simp [e_apply]

theorem sum_e_sq : ∑ j : Fin r, e1 r j ^ 2 = 1 := by
  simp [e_apply]

theorem comb_apply {n : ℕ} (a : Fin n → ℝ) (τ : ℝ) (R : Matrix (Fin n) (Fin r) ℝ)
    (μ : Fin n → ℝ) (lam : ℝ) (i : Fin n) (j : Fin r) :
    ((diagonal μ * ((2 : ℝ) • R - vecMulVec (fun _ => (1 : ℝ)) (e1 r)) +
        lam • vecMulVec a ((2 : ℝ) • (a ᵥ* R) - τ • e1 r) : Matrix (Fin n) (Fin r) ℝ)) i j =
      μ i * (2 * R i j - e1 r j) + lam * (a i * (2 * (a ᵥ* R) j - τ * e1 r j)) := by
  simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.vecMulVec_apply, Pi.sub_apply, Pi.smul_apply, one_mul]

theorem vecMul_apply' {n : ℕ} (a : Fin n → ℝ) (R : Matrix (Fin n) (Fin r) ℝ) (j : Fin r) :
    (a ᵥ* R) j = ∑ i, a i * R i j := by
  simp [Matrix.vecMul, dotProduct]

theorem mulVec_e {n : ℕ} (R : Matrix (Fin n) (Fin r) ℝ) (i : Fin n) : (R *ᵥ e1 r) i = R i 0 := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mul_e _

theorem diag_apply' {n : ℕ} (R : Matrix (Fin n) (Fin r) ℝ) (i : Fin n) :
    (R * Rᵀ).diag i = ∑ j, R i j ^ 2 := by
  simp [Matrix.diag_apply, Matrix.mul_apply, sq]

end Aux_QKP31

open Matrix QKPSDP Aux_QKP31 in
theorem solution {n r : ℕ} [NeZero r] (a : Fin n → ℝ) (τ : ℝ) (ha : Assumption1 a τ) :
    {R : Matrix (Fin n) (Fin r) ℝ | R ∈ K a τ ∧ ¬ QKPSDP.IsRegular a τ R} = N a τ := by
  obtain ⟨hn, hai, hS⟩ := ha
  have hτ : 0 < τ := by
    have := hai ⟨0, by omega⟩
    linarith
  ext R
  simp only [Set.mem_setOf_eq, N, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hK1, hK2⟩, hnreg⟩
    unfold QKPSDP.IsRegular at hnreg
    push_neg at hnreg
    obtain ⟨μ, lam, hcomb, hne⟩ := hnreg
    have hE : ∀ i j, μ i * (2 * R i j - e1 r j) +
        lam * (a i * (2 * (a ᵥ* R) j - τ * e1 r j)) = 0 := by
      intro i j
      rw [← comb_apply a τ R μ lam i j, hcomb]
      rfl
    have hh : ∀ i, ∑ j, R i j ^ 2 = R i 0 := by
      intro i
      have := congrFun hK2 i
      rw [diag_apply', mulVec_e] at this
      exact this
    set A : Fin r → ℝ := fun j => (a ᵥ* R) j with hAdef
    have hA0 : a ⬝ᵥ (R *ᵥ e1 r) = A 0 := by
      simp only [hAdef, vecMul_apply', dotProduct, mulVec_e]
    have hg : ∑ j, A j ^ 2 = τ * A 0 := by
      have := hK1
      rw [hA0] at this
      simp only [dotProduct] at this
      have e : ∑ j, (a ᵥ* R) j * (a ᵥ* R) j = ∑ j, A j ^ 2 := by
        apply Finset.sum_congr rfl; intro j _; simp [hAdef, sq]
      linarith
    set w : Fin r → ℝ := fun j => 2 * A j - τ * e1 r j with hwdef
    have hE' : ∀ i j, μ i * (2 * R i j - e1 r j) + lam * (a i * w j) = 0 := hE
    have rowhalf : ∀ i, (∀ j, 2 * R i j - e1 r j = 0) → False := by
      intro i hi
      have hR : ∀ j, R i j = e1 r j / 2 := fun j => by linarith [hi j]
      have h1 := hh i
      simp only [hR] at h1
      have h2 : ∑ j : Fin r, (e1 r j / 2) ^ 2 = 1 / 4 := by
        have : ∀ j : Fin r, (e1 r j / 2) ^ 2 = e1 r j ^ 2 / 4 := fun j => by ring
        simp only [this, ← Finset.sum_div, sum_e_sq]
      rw [h2, e_apply, if_pos rfl] at h1
      norm_num at h1
    have hlam : lam ≠ 0 := by
      intro hl
      have hμ : μ ≠ 0 := fun h => hne h hl
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hμ
      apply rowhalf i
      intro j
      have := hE' i j
      rw [hl, zero_mul, add_zero] at this
      exact (mul_eq_zero.mp this).resolve_left hi
    have hw : ∃ j, w j ≠ 0 := by
      by_contra hc
      push_neg at hc
      have hAj : ∀ j, A j = τ * e1 r j / 2 := fun j => by
        have := hc j; simp only [hwdef] at this; linarith
      have h1 : ∑ j, A j ^ 2 = τ ^ 2 / 4 := by
        simp only [hAj]
        have : ∀ j : Fin r, (τ * e1 r j / 2) ^ 2 = τ ^ 2 / 4 * e1 r j ^ 2 := fun j => by ring
        simp only [this, ← Finset.mul_sum, sum_e_sq, mul_one]
      rw [h1, hAj 0, e_apply, if_pos rfl] at hg
      nlinarith
    have hμ : ∀ i, μ i ≠ 0 := by
      intro i hi
      obtain ⟨j, hj⟩ := hw
      have := hE' i j
      rw [hi, zero_mul, zero_add] at this
      have hai' := (hai i).1
      rcases mul_eq_zero.mp this with h | h
      · exact hlam h
      · rcases mul_eq_zero.mp h with h' | h'
        · linarith
        · exact hj h'
    set c : Fin n → ℝ := fun i => -lam * a i / μ i with hcdef
    have hR : ∀ i j, 2 * R i j - e1 r j = c i * w j := by
      intro i j
      have h1 : 2 * R i j - e1 r j = (-lam * a i * w j) / μ i := by
        rw [eq_div_iff (hμ i)]
        linear_combination hE' i j
      rw [h1]
      simp only [hcdef]
      ring
    set W := ∑ j, w j ^ 2 with hWdef
    have hcW : ∀ i, c i ^ 2 * W = 1 := by
      intro i
      have h1 := hh i
      have hRij : ∀ j, R i j = (e1 r j + c i * w j) / 2 := fun j => by linarith [hR i j]
      simp only [hRij] at h1
      have h2 : ∑ j, ((e1 r j + c i * w j) / 2) ^ 2 =
          (∑ j, e1 r j ^ 2) / 4 + c i / 2 * ∑ j, e1 r j * w j + c i ^ 2 / 4 * W := by
        rw [hWdef, Finset.sum_div, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro j _; ring
      rw [h2, sum_e_sq, sum_e_mul, e_apply, if_pos rfl] at h1
      nlinarith
    set S := ∑ i, a i with hSdef
    set C := ∑ i, a i * c i with hCdef
    have hwj : ∀ j, (1 - C) * w j = (S - τ) * e1 r j := by
      intro j
      have h2A : 2 * A j = S * e1 r j + C * w j := by
        simp only [hAdef, vecMul_apply', Finset.mul_sum, hSdef, hCdef, Finset.sum_mul,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _
        linear_combination (a i) * hR i j
      have hwe : w j = S * e1 r j + C * w j - τ * e1 r j := by
        have h0 : w j = 2 * A j - τ * e1 r j := rfl
        linarith [h2A]
      linear_combination hwe
    have hC : C ≠ 1 := by
      intro h1
      have := hwj 0
      rw [h1, e_apply, if_pos rfl] at this
      linarith
    have hwz : ∀ j, j ≠ 0 → w j = 0 := by
      intro j hj
      have := hwj j
      rw [e_apply, if_neg hj, mul_zero] at this
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (by linarith : C = 1) hC
      · exact h
    have hW : W = w 0 ^ 2 := by
      rw [hWdef, Finset.sum_eq_single (0 : Fin r)]
      · intro j _ hj; rw [hwz j hj]; ring
      · intro h; exact absurd (Finset.mem_univ _) h
    set v : Fin n → ℝ := fun i => (1 + c i * w 0) / 2 with hvdef
    have hcw : ∀ i, c i * w 0 = 1 ∨ c i * w 0 = -1 := by
      intro i
      have := hcW i
      rw [hW] at this
      have h' : (c i * w 0 - 1) * (c i * w 0 + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp h' with h | h
      · left; linarith
      · right; linarith
    have hv01 : ∀ i, v i = 0 ∨ v i = 1 := by
      intro i
      rcases hcw i with h | h
      · right; simp only [hvdef, h]; norm_num
      · left; simp only [hvdef, h]; norm_num
    have hRv : ∀ i j, R i j = v i * e1 r j := by
      intro i j
      have := hR i j
      by_cases hj : j = 0
      · subst hj
        rw [e_apply, if_pos rfl] at this ⊢
        simp only [hvdef]
        linarith
      · rw [hwz j hj, e_apply, if_neg hj] at this
        rw [e_apply, if_neg hj]
        linarith
    have hAv : ∀ j, A j = (a ⬝ᵥ v) * e1 r j := by
      intro j
      simp only [hAdef, vecMul_apply', hRv, dotProduct, Finset.sum_mul, mul_assoc]
    have hav : (a ⬝ᵥ v) ^ 2 = τ * (a ⬝ᵥ v) := by
      have := hg
      simp only [hAv, mul_pow, ← Finset.mul_sum, sum_e_sq, mul_one, e_zero] at this
      linarith
    have hRe : R = vecMulVec v (e1 r) := by
      ext i j; rw [Matrix.vecMulVec_apply]; exact hRv i j
    by_cases hz : a ⬝ᵥ v = 0
    · left
      have hv0 : ∀ i, v i = 0 := by
        have hnn : ∀ i ∈ Finset.univ, 0 ≤ a i * v i := fun i _ => by
          rcases hv01 i with h | h <;> rw [h] <;> nlinarith [(hai i).1]
        have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz
        intro i
        have h1 := this i (Finset.mem_univ _)
        rcases mul_eq_zero.mp h1 with h | h
        · linarith [(hai i).1]
        · exact h
      rw [hRe]
      ext i j
      simp [Matrix.vecMulVec_apply, hv0 i]
    · right
      refine ⟨v, hv01, ?_, hRe⟩
      have : (a ⬝ᵥ v) * (a ⬝ᵥ v - τ) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hz
      · linarith
  · rintro (rfl | ⟨v, hv01, hav, rfl⟩)
    · refine ⟨⟨by simp, by ext i; simp⟩, ?_⟩
      intro hreg
      have := (hreg (fun i => -τ * a i) 1 ?_).2
      · norm_num at this
      · ext i j
        rw [comb_apply]
        simp
        ring
    · have hRv : ∀ i j, vecMulVec v (e1 r) i j = v i * e1 r j := fun i j => Matrix.vecMulVec_apply _ _ _ _
      have hA : ∀ j, (a ᵥ* vecMulVec v (e1 r)) j = (a ⬝ᵥ v) * e1 r j := by
        intro j
        rw [vecMul_apply']
        simp only [hRv, dotProduct, Finset.sum_mul, mul_assoc]
      have hv2 : ∀ i, v i ^ 2 = v i := by
        intro i; rcases hv01 i with h | h <;> rw [h] <;> norm_num
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have h1 : (a ᵥ* vecMulVec v (e1 r)) ⬝ᵥ (a ᵥ* vecMulVec v (e1 r)) = τ ^ 2 := by
          have hA' : ∀ j, (a ᵥ* vecMulVec v (e1 r)) j = τ * e1 r j := fun j => by rw [hA, hav]
          simp only [dotProduct, hA']
          have : ∀ j : Fin r, τ * e1 r j * (τ * e1 r j) = τ ^ 2 * e1 r j ^ 2 := fun j => by ring
          simp only [this, ← Finset.mul_sum, sum_e_sq, mul_one]
        have h2 : a ⬝ᵥ (vecMulVec v (e1 r) *ᵥ e1 r) = τ := by
          simp only [dotProduct, mulVec_e, hRv, e_zero, mul_one]
          exact hav
        rw [h1, h2]; ring
      · ext i
        rw [diag_apply', mulVec_e]
        simp only [hRv, mul_pow, ← Finset.mul_sum, sum_e_sq, mul_one, e_zero]
        exact hv2 i
      · intro hreg
        have := (hreg (fun i => -τ * a i * (2 * v i - 1)) 1 ?_).2
        · norm_num at this
        · ext i j
          rw [comb_apply, hA, hav, hRv]
          simp only [Matrix.zero_apply]
          have h1 : (2 * v i - 1) ^ 2 = 1 := by
            rcases hv01 i with h | h <;> rw [h] <;> norm_num
          have : -τ * a i * (2 * v i - 1) * (2 * (v i * e1 r j) - e1 r j) +
              1 * (a i * (2 * (τ * e1 r j) - τ * e1 r j)) =
              τ * a i * e1 r j * (1 - (2 * v i - 1) ^ 2) := by ring
          rw [this, h1]; ring
