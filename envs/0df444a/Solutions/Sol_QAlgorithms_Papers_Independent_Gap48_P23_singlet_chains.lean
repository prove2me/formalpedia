-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P23.singlet_chains
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:08:12.891178+00:00
-- url     : https://prove2.me/submissions/8981802c-23f3-4c8f-9f45-e0c4eb24c64a

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23
noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

theorem g74g_snoc_mk {d L : ℕ} (z : Fin (L+1) → Fin d) (c : Fin d) (i : ℕ) (h : i < L+2) :
    (Fin.snoc z c : Fin (L+2) → Fin d) ⟨i, h⟩ = if hi : i < L+1 then z ⟨i, hi⟩ else c := by
  simp [Fin.snoc]

theorem g74g_networkChain_succ {d : ℕ} (L : ℕ) (M : Fin (L+1) → Op (Fin d)) :
    networkChain (L+1) M = networkChain L (fun j => M j.castSucc) * M (Fin.last L) := by
  funext a b
  simp only [networkChain, Matrix.mul_apply, Finset.sum_mul]
  rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (L+2) => Fin d)) (fun z : Fin (L+2) → Fin d => if z 0 = a ∧ z ⟨L+1, by omega⟩ = b then ∏ j : Fin (L+1), M j (z ⟨j.val, by omega⟩) (z ⟨j.val+1, by omega⟩) else (0:ℂ))]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_eq_single b, Finset.sum_eq_single (z ⟨L, by omega⟩)]
  · have h0 : (Fin.snoc z b : Fin (L+2) → Fin d) 0 = z 0 := by
      simpa using g74g_snoc_mk z b 0
    have hL : (Fin.snoc z b : Fin (L+2) → Fin d) ⟨L+1, by omega⟩ = b := by
      simp [g74g_snoc_mk]
    simp only [Fin.snocEquiv_apply, Fin.prod_univ_castSucc, h0, hL, and_true, ite_mul, zero_mul]
    refine if_congr Iff.rfl ?_ rfl
    congr 1
    · refine Finset.prod_congr rfl fun x _ => ?_
      simp only [g74g_snoc_mk, Fin.val_castSucc, dif_pos (Nat.lt_succ_of_lt x.isLt),
        dif_pos (Nat.succ_lt_succ x.isLt)]
    · simp [g74g_snoc_mk]
  · intro m _ hm
    rw [if_neg (fun h => hm h.2.symm), zero_mul]
  · simp
  · intro c _ hc
    simp [g74g_snoc_mk, hc]
  · simp

theorem g74g_networkChain_zero {d : ℕ} (M : Fin 0 → Op (Fin d)) :
    networkChain 0 M = 1 := by
  funext a b
  simp only [networkChain, Finset.univ_eq_empty, Finset.prod_empty]
  rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin d)).symm]
  by_cases h : a = b
  · subst h; simp
  · simp [h]

theorem g74g_networkChain_nat {d : ℕ} (g : ℕ → Op (Fin d)) (L : ℕ) :
    networkChain (L+1) (fun j => g j.val) = networkChain L (fun j => g j.val) * g L := by
  rw [g74g_networkChain_succ]
  rfl

theorem g74g_networkChain_const {d : ℕ} (M : Op (Fin d)) (L : ℕ) :
    networkChain L (fun _ => M) = M ^ L := by
  induction L with
  | zero => rw [g74g_networkChain_zero, pow_zero]
  | succ L ih =>
    have := g74g_networkChain_nat (fun _ => M) L
    rw [this, ih, pow_succ]

theorem g74g_networkChain_smul {d : ℕ} (s : ℕ → ℂ) (M : Op (Fin d)) (L : ℕ) :
    networkChain L (fun j => s j.val • M) = (∏ j ∈ Finset.range L, s j) • M ^ L := by
  induction L with
  | zero => rw [g74g_networkChain_zero]; simp
  | succ L ih =>
    have := g74g_networkChain_nat (fun j => s j • M) L
    rw [this, ih, Finset.prod_range_succ, pow_succ, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

theorem g74g_networkChain_pair {d : ℕ} (g : ℕ → Op (Fin d)) (k : ℕ) :
    networkChain (2*k) (fun j => g j.val) =
      (List.ofFn fun j : Fin k => g (2*j.val) * g (2*j.val+1)).prod := by
  induction k with
  | zero => simp [g74g_networkChain_zero]
  | succ k ih =>
    have h1 := g74g_networkChain_nat g (2*k+1)
    have h2 := g74g_networkChain_nat g (2*k)
    rw [show 2*(k+1) = 2*k+1+1 by ring, h1, h2, ih, List.ofFn_succ', List.prod_concat]
    simp [mul_assoc]

theorem g74g_reversed (M : Op (Fin 2)) (hM : M.transpose = -M) (k extra : ℕ) (he : extra ≤ 2)
    (reverse : Fin (k+1) → Bool) :
    networkChain (2*k+extra) (reversedKetFactors k extra M reverse) =
      (-1:ℂ)^(reversalCount k extra reverse) • networkChain (2*k+extra) (fun _ => M) := by
  set P : ℕ → Prop := fun n => if h : n/2 < k+1 then n%2 = 0 ∧ reverse ⟨n/2,h⟩ = true else False
    with hP
  have hfac : reversedKetFactors k extra M reverse =
      fun j => (if P j.val then (-1:ℂ) else 1) • M := by
    funext j
    have h : j.val/2 < k+1 := by have := j.isLt; omega
    simp only [reversedKetFactors, hP, dif_pos h]
    split_ifs <;> simp [hM]
  rw [hfac, g74g_networkChain_smul (fun n => if P n then (-1:ℂ) else 1), g74g_networkChain_const]
  congr 1
  rw [← Fin.prod_univ_eq_prod_range, Finset.prod_ite, Finset.prod_const_one, mul_one,
    Finset.prod_const]
  rfl

/-- PDF p.48, Corollary A.4: all three unnormalized singlet chains and every
allowed ket reversal; the closed contraction includes the final bra. -/
theorem solution (k : ℕ) :
    networkChain (2*k) (fun _ => singletMatrix) = singletMatrix^(2*k) ∧
    singletMatrix^(2*k) = (-1:ℂ)^k • (1 : Op (Fin 2)) ∧
    bilinearVectorize (networkChain (2*k+1) (fun _ => singletMatrix)) =
      bilinearVectorize ((-1:ℂ)^k • singletMatrix) ∧
    (networkChain (2*k+2) (fun _ => singletMatrix)).trace = 2*(-1:ℂ)^(k+1) ∧
    (∀ (extra : ℕ), extra ≤ 2 → ∀ reverse : Fin (k+1) → Bool,
      networkChain (2*k+extra) (reversedKetFactors k extra singletMatrix reverse) =
        (-1:ℂ)^(reversalCount k extra reverse) • networkChain (2*k+extra) (fun _ => singletMatrix)) := by
  have hS2 : singletMatrix ^ 2 = -1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [singletMatrix, sq, Matrix.mul_apply, Fin.sum_univ_two]
  have hneg : ∀ m : ℕ, (-(1 : Op (Fin 2)))^m = (-1:ℂ)^m • (1 : Op (Fin 2)) := by
    intro m
    rw [show (-(1:Op (Fin 2))) = (-1:ℂ) • (1 : Op (Fin 2)) by simp, smul_pow, one_pow]
  have hpow : ∀ m : ℕ, singletMatrix^(2*m) = (-1:ℂ)^m • (1 : Op (Fin 2)) := by
    intro m; rw [pow_mul, hS2, hneg]
  have hT : singletMatrix.transpose = -singletMatrix := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [singletMatrix]
  refine ⟨g74g_networkChain_const _ _, hpow k, ?_, ?_, ?_⟩
  · rw [g74g_networkChain_const, pow_succ, hpow, Matrix.smul_mul, Matrix.one_mul]
  · rw [g74g_networkChain_const, show 2*k+2 = 2*(k+1) by ring, hpow, Matrix.trace_smul,
      Matrix.trace_one]
    simp [mul_comm]
  · intro extra he reverse
    exact g74g_reversed _ hT k extra he reverse


end
