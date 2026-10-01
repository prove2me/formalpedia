-- Prove2me | solution 1 for ShorAlgorithms.QFT.qft_circuit_eq
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T16:02:38.283175+00:00
-- url     : https://prove2.me/submissions/179cf6b3-acbd-4c8f-928f-41c29eb25708

import Mathlib
import Definitions.Def_ShorAlgorithms_QFT_BitStrings
import Definitions.Def_ShorAlgorithms_QFT_Circuit
open ShorAlgorithms.QFT
namespace AQFTCircuit
noncomputable def phase {l : ℕ} (j k : Fin l) (b : Fin l → Fin 2) : ℂ :=
  Complex.exp (((Real.pi / 2 ^ ((k : ℕ) - j) * (b j : ℕ) * (b k : ℕ) : ℝ) : ℂ) * Complex.I)

lemma apply_S {l : ℕ} (j k : Fin l) (hjk : j ≠ k) (ψ : (Fin l → Fin 2) → ℂ) (b : Fin l → Fin 2) :
    applyGate (Gate.S j k) ψ b = ψ b * phase j k b := by
  simp only [applyGate, applyTwoBit, Smat, Matrix.diagonal_apply, Prod.mk.injEq]
  simp only [ite_and, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Function.update_eq_self]
  simp only [← ite_and, ← mul_ite, ← Prod.mk.injEq]
  have hf (x y : Fin 2) : (if (x, y) = (1, 1) then
      Complex.exp (((Real.pi / 2 ^ ((k : ℕ) - j) : ℝ) : ℂ) * Complex.I) else 1) =
      Complex.exp (((Real.pi / 2 ^ ((k : ℕ) - j) * (x : ℕ) * (y : ℕ) : ℝ) : ℂ) * Complex.I) := by
    fin_cases x <;> fin_cases y <;> norm_num
  rw [hf]
  rfl

lemma Rmat_phase (a b : Fin 2) : Rmat a b =
    (Real.sqrt 2 : ℂ)⁻¹ * Complex.exp (((Real.pi * (a : ℕ) * (b : ℕ) : ℝ) : ℂ) * Complex.I) := by
  fin_cases a <;> fin_cases b <;> norm_num [Rmat, Complex.exp_pi_mul_I]


noncomputable def phaseRow {l : ℕ} (a : Fin l → Fin 2) (j : Fin l) (b : Fin l → Fin 2) : ℂ :=
  ∏ k : Fin l, if j < k then
    Complex.exp (((Real.pi / 2 ^ ((k : ℕ) - j) * (a j : ℕ) * (b k : ℕ) : ℝ) : ℂ) * Complex.I) else 1

noncomputable def row {l : ℕ} (a : Fin l → Fin 2) (j : Fin l) (b : Fin l → Fin 2) : ℂ :=
  Rmat (a j) (b j) * phaseRow a j b

noncomputable def upperProd {l : ℕ} (a : Fin l → Fin 2) (m : ℕ) (b : Fin l → Fin 2) : ℂ :=
  ∏ i : Fin l, if m ≤ (i : ℕ) then row a i b else 1

noncomputable def partialState {l : ℕ} (a : Fin l → Fin 2) (m : ℕ) (b : Fin l → Fin 2) : ℂ :=
  if ∀ i : Fin l, (i : ℕ) < m → b i = a i then upperProd a m b else 0

lemma phaseRow_update {l : ℕ} (a b : Fin l → Fin 2) (i j : Fin l) (hij : j ≤ i) (v : Fin 2) :
    phaseRow a i (Function.update b j v) = phaseRow a i b := by
  classical
  unfold phaseRow
  apply Finset.prod_congr rfl
  intro k _
  by_cases hik : i < k
  · simp [hik, Function.update_of_ne (ne_of_gt (lt_of_le_of_lt hij hik))]
  · simp [hik]

lemma upperProd_update {l : ℕ} (a b : Fin l → Fin 2) (j : Fin l) (v : Fin 2) :
    upperProd a ((j : ℕ) + 1) (Function.update b j v) = upperProd a ((j : ℕ) + 1) b := by
  classical
  unfold upperProd
  apply Finset.prod_congr rfl
  intro i _
  by_cases hji : (j : ℕ) + 1 ≤ i
  · have hlt : j < i := by exact_mod_cast hji
    simp [hji, row, Function.update_of_ne hlt.ne', phaseRow_update a b i j hlt.le v]
  · simp [hji]

lemma upperProd_step {l : ℕ} (a b : Fin l → Fin 2) (j : Fin l) :
    upperProd a (j : ℕ) b = row a j b * upperProd a ((j : ℕ) + 1) b := by
  classical
  unfold upperProd
  have he (i : Fin l) : (if (j : ℕ) ≤ i then row a i b else 1) =
      (if i = j then row a j b else 1) * (if (j : ℕ) + 1 ≤ i then row a i b else 1) := by
    by_cases hij : i = j
    · subst i; simp
    · by_cases hlt : j < i
      · simp [hij, hlt.le, show (j : ℕ) + 1 ≤ i by exact_mod_cast hlt]
      · have hgt : i < j := lt_of_le_of_ne (le_of_not_gt hlt) hij
        simp [hij, show ¬ (j : ℕ) ≤ i by exact_mod_cast not_le_of_gt hgt,
          show ¬ (j : ℕ) + 1 ≤ i by omega]
  simp_rw [he]
  simp only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]

lemma run_S {l : ℕ} (j : Fin l) (ks : List (Fin l)) (hk : ∀ k ∈ ks, j ≠ k)
    (ψ : (Fin l → Fin 2) → ℂ) (b : Fin l → Fin 2) :
    runCircuit (ks.map (Gate.S j)) ψ b = ψ b * (ks.map (fun k => phase j k b)).prod := by
  induction ks generalizing ψ with
  | nil => simp [runCircuit]
  | cons k ks ih =>
    have he : runCircuit ((k :: ks).map (Gate.S j)) ψ =
        runCircuit (ks.map (Gate.S j)) (applyGate (Gate.S j k) ψ) := rfl
    rw [he, ih (fun i hi => hk i (by simp [hi])), apply_S j k (hk k (by simp))]
    simp [mul_assoc]

lemma phase_list {l : ℕ} (j : Fin l) (b : Fin l → Fin 2) :
    ((((List.finRange l).reverse.filter fun k => decide (j < k)).map fun k => phase j k b).prod) =
      phaseRow b j b := by
  classical
  rw [← List.prod_toFinset _ (List.Nodup.filter _ (by simpa using List.nodup_finRange l))]
  simp only [List.toFinset_filter, List.toFinset_reverse, List.toFinset_finRange, decide_eq_true_eq,
    Finset.prod_filter, phaseRow, phase]

noncomputable def block {l : ℕ} (j : Fin l) : List (Gate l) :=
  (((List.finRange l).reverse.filter fun k => decide (j < k)).map fun k => Gate.S j k) ++ [Gate.R j]

lemma run_block {l : ℕ} (j : Fin l) (ψ : (Fin l → Fin 2) → ℂ) :
    runCircuit (block j) ψ = applyGate (Gate.R j) (fun b => ψ b * phaseRow b j b) := by
  classical
  have hS : runCircuit (((List.finRange l).reverse.filter fun k => decide (j < k)).map (Gate.S j)) ψ =
      fun b => ψ b * phaseRow b j b := by
    funext b
    rw [run_S j _ (by intro k hk; have := (List.mem_filter.mp hk).2; simp only [decide_eq_true_eq] at this; exact this.ne), phase_list]
  simp only [block, runCircuit, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change applyGate (Gate.R j) (runCircuit _ ψ) = _
  rw [hS]

lemma partial_support {l : ℕ} (a b : Fin l → Fin 2) (j : Fin l) (u : Fin 2) :
    (∀ i : Fin l, (i : ℕ) < (j : ℕ) + 1 → Function.update b j u i = a i) ↔
      u = a j ∧ ∀ i : Fin l, (i : ℕ) < j → b i = a i := by
  constructor
  · intro h
    constructor
    · simpa using h j (by omega)
    · intro i hi
      simpa [Function.update_of_ne (show i ≠ j by intro hij; subst i; omega)] using h i (by omega)
  · rintro ⟨hu, h⟩ i hi
    by_cases hij : i = j
    · subst i; simpa using hu
    · have hlt : (i : ℕ) < j := by
        have hne : (i : ℕ) ≠ j := by intro he; exact hij (Fin.ext he)
        omega
      simpa [Function.update_of_ne hij] using h i hlt

lemma partial_S {l : ℕ} (a b : Fin l → Fin 2) (j : Fin l) :
    partialState a ((j : ℕ) + 1) b * phaseRow b j b =
      partialState a ((j : ℕ) + 1) b * phaseRow a j b := by
  classical
  by_cases h : ∀ i : Fin l, (i : ℕ) < (j : ℕ) + 1 → b i = a i
  · have hj : b j = a j := h j (by omega)
    simp only [phaseRow, hj]
  · simp only [partialState, if_neg h, zero_mul]

lemma partial_step {l : ℕ} (a : Fin l → Fin 2) (j : Fin l) :
    runCircuit (block j) (partialState a ((j : ℕ) + 1)) = partialState a (j : ℕ) := by
  classical
  rw [run_block]
  have hf : (fun b => partialState a ((j : ℕ) + 1) b * phaseRow b j b) =
      (fun b => partialState a ((j : ℕ) + 1) b * phaseRow a j b) := by
    funext b
    exact partial_S a b j
  rw [hf]
  funext b
  simp only [applyGate, applyOneBit]
  simp only [partialState, partial_support, upperProd_update, phaseRow_update a b j j le_rfl]
  by_cases h : ∀ i : Fin l, (i : ℕ) < (j : ℕ) → b i = a i
  · rw [if_pos h]
    simp only [and_iff_left h, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [upperProd_step]
    simp only [row]
    ring
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro u _
    rw [if_neg (by rintro ⟨_, hh⟩; exact h hh)]
    simp

lemma partial_initial {l : ℕ} (a : Fin l → Fin 2) : partialState a l = basisState a := by
  classical
  funext b
  have he : (∀ i : Fin l, (i : ℕ) < l → b i = a i) ↔ b = a := by
    constructor
    · intro h; funext i; exact h i i.isLt
    · rintro rfl; simp
  have hp : upperProd a l b = 1 := by
    unfold upperProd
    apply Finset.prod_eq_one
    intro i _
    simp only [not_le_of_gt i.isLt, if_false]
  simp only [partialState, basisState, he, hp]

lemma partial_zero {l : ℕ} (a b : Fin l → Fin 2) : partialState a 0 b = ∏ j : Fin l, row a j b := by
  simp [partialState, upperProd]

lemma run_low {l : ℕ} (a : Fin l → Fin 2) (m : ℕ) (hm : m ≤ l) :
    runCircuit (((List.finRange l).take m).reverse.flatMap block) (partialState a m) = partialState a 0 := by
  induction m with
  | zero => simp [runCircuit]
  | succ m ih =>
    have hml : m < l := by omega
    let j : Fin l := ⟨m, hml⟩
    have ht : (List.finRange l).take (m + 1) = (List.finRange l).take m ++ [j] := by
      rw [List.take_succ_eq_append_getElem (by simpa using hml)]
      congr 2
      apply Fin.ext
      simp [j]
    rw [ht, List.reverse_append]
    simp only [List.reverse_singleton, List.singleton_append, List.flatMap_cons]
    simp only [runCircuit, List.foldl_append]
    change runCircuit (((List.finRange l).take m).reverse.flatMap block)
      (runCircuit (block j) (partialState a ((j : ℕ) + 1))) = _
    rw [partial_step]
    exact ih (by omega)

lemma circuit_product {l : ℕ} (a b : Fin l → Fin 2) :
    runCircuit (qftGates l) (basisState a) b = ∏ j : Fin l, row a j b := by
  have h := run_low a l le_rfl
  rw [partial_initial] at h
  rw [show (List.finRange l).take l = List.finRange l from List.take_of_length_le (by simp)] at h
  have hg : ((List.finRange l).reverse.flatMap block) = qftGates l := rfl
  rw [hg] at h
  rw [h, partial_zero]

lemma phaseRow_exp {l : ℕ} (a b : Fin l → Fin 2) (j : Fin l) :
    phaseRow a j b = Complex.exp (((∑ k : Fin l, if j < k then
      Real.pi / 2 ^ ((k : ℕ) - j) * (a j : ℕ) * (b k : ℕ) else 0 : ℝ) : ℂ) * Complex.I) := by
  classical
  unfold phaseRow
  have he (k : Fin l) : (if j < k then
      Complex.exp (((Real.pi / 2 ^ ((k : ℕ) - j) * (a j : ℕ) * (b k : ℕ) : ℝ) : ℂ) * Complex.I) else 1) =
      Complex.exp (((if j < k then Real.pi / 2 ^ ((k : ℕ) - j) * (a j : ℕ) * (b k : ℕ) else 0 : ℝ) : ℂ) * Complex.I) := by
    by_cases h : j < k <;> simp [h]
  simp_rw [he]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_sum, Finset.sum_mul]

lemma row_exp {l : ℕ} (a b : Fin l → Fin 2) (j : Fin l) :
    row a j b = (Real.sqrt 2 : ℂ)⁻¹ * Complex.exp
      (((Real.pi * (a j : ℕ) * (b j : ℕ) + ∑ k : Fin l, if j < k then
        Real.pi / 2 ^ ((k : ℕ) - j) * (a j : ℕ) * (b k : ℕ) else 0 : ℝ) : ℂ) * Complex.I) := by
  rw [row, Rmat_phase, phaseRow_exp, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

lemma sqrt_pow_two (l : ℕ) : Real.sqrt ((2 : ℝ) ^ l) = (Real.sqrt 2) ^ l := by
  induction l with
  | zero => simp
  | succ l ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

lemma path_amplitude (l : ℕ) (a b : Fin l → Fin 2) :
    runCircuit (qftGates l) (basisState a) b =
      ((Real.sqrt (2 ^ l) : ℝ) : ℂ)⁻¹ *
        Complex.exp
          (((∑ j : Fin l, Real.pi * ((a j : ℕ) : ℝ) * ((b j : ℕ) : ℝ)) +
              ∑ j : Fin l, ∑ k : Fin l,
                if j < k then
                  Real.pi / 2 ^ ((k : ℕ) - (j : ℕ)) * ((a j : ℕ) : ℝ) * ((b k : ℕ) : ℝ)
                else 0 : ℝ) * Complex.I) := by
  rw [circuit_product]
  simp_rw [row_exp]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Complex.exp_sum, sqrt_pow_two, Complex.ofReal_pow, inv_pow]
  congr 1
  congr 1
  simp only [Complex.ofReal_add, Complex.ofReal_sum, add_mul, Finset.sum_add_distrib,
    Finset.sum_mul]

end AQFTCircuit

namespace AQFT

lemma ratio_le {l : ℕ} (j k : Fin l) (hjk : j ≤ k) :
    (2 : ℝ) ^ (j : ℕ) * 2 ^ (k.rev : ℕ) / 2 ^ l = 1 / (2 * 2 ^ ((k : ℕ) - j)) := by
  have hn : (j : ℕ) + (k.rev : ℕ) + ((k : ℕ) - j) + 1 = l := by
    simp only [Fin.val_rev]
    omega
  have he : (2 : ℝ) ^ (j : ℕ) * 2 ^ (k.rev : ℕ) * 2 ^ ((k : ℕ) - j) * 2 = 2 ^ l := by
    rw [← pow_add, ← pow_add, ← pow_succ, hn]
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  nlinarith

lemma ratio_gt {l : ℕ} (j k : Fin l) (hjk : k < j) :
    (2 : ℝ) ^ (j : ℕ) * 2 ^ (k.rev : ℕ) / 2 ^ l = 2 ^ ((j : ℕ) - k - 1) := by
  have hn : (j : ℕ) + (k.rev : ℕ) = ((j : ℕ) - k - 1) + l := by
    simp only [Fin.val_rev]
    omega
  rw [← pow_add, hn, pow_add]
  field_simp

lemma pair_phase {l : ℕ} (a b : Fin l → Fin 2) (j k : Fin l) :
    Complex.exp (((if j ≤ k then
      Real.pi / 2 ^ ((k : ℕ) - j) * ((a j : ℕ) : ℝ) * ((b k : ℕ) : ℝ) else 0 : ℝ) : ℂ) * Complex.I) =
    Complex.exp (((2 * Real.pi * (2 : ℝ) ^ (j : ℕ) * 2 ^ (k.rev : ℕ) /
      2 ^ l * (a j : ℕ) * (b k : ℕ) : ℝ) : ℂ) * Complex.I) := by
  by_cases hjk : j ≤ k
  · rw [if_pos hjk]
    congr 3
    have hr := ratio_le j k hjk
    calc Real.pi / 2 ^ ((k : ℕ) - j) * ((a j : ℕ) : ℝ) * ((b k : ℕ) : ℝ)
        = (2 * Real.pi) * (1 / (2 * 2 ^ ((k : ℕ) - j))) * (a j : ℕ) * (b k : ℕ) := by ring
      _ = _ := by rw [← hr]; ring
  · rw [if_neg hjk]
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
    have hr := ratio_gt j k (lt_of_not_ge hjk)
    have he : 2 * Real.pi * (2 : ℝ) ^ (j : ℕ) * 2 ^ (k.rev : ℕ) /
      2 ^ l * (a j : ℕ) * (b k : ℕ) =
      (2 ^ ((j : ℕ) - k - 1) * (a j : ℕ) * (b k : ℕ) : ℕ) * (2 * Real.pi) := by
      push_cast
      rw [show 2 * Real.pi * (2 : ℝ) ^ (j : ℕ) * 2 ^ (k.rev : ℕ) / 2 ^ l =
        (2 * Real.pi) * ((2 : ℝ) ^ (j : ℕ) * 2 ^ (k.rev : ℕ) / 2 ^ l) by ring, hr]
      ring
    rw [he]
    push_cast
    rw [mul_assoc]
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      (Complex.exp_nat_mul_two_pi_mul_I (2 ^ ((j : ℕ) - k - 1) * (a j : ℕ) * (b k : ℕ))).symm

lemma sum_phase {l : ℕ} (a b : Fin l → Fin 2) :
    (∑ j : Fin l, ∑ k : Fin l, if j ≤ k then
      Real.pi / 2 ^ ((k : ℕ) - j) * ((a j : ℕ) : ℝ) * ((b k : ℕ) : ℝ) else 0) =
    (∑ j : Fin l, Real.pi * ((a j : ℕ) : ℝ) * ((b j : ℕ) : ℝ)) +
      ∑ j : Fin l, ∑ k : Fin l, if j < k then
        Real.pi / 2 ^ ((k : ℕ) - j) * ((a j : ℕ) : ℝ) * ((b k : ℕ) : ℝ) else 0 := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have he (k : Fin l) : (if j ≤ k then Real.pi / 2 ^ ((k : ℕ) - j) * ((a j : ℕ) : ℝ) * ((b k : ℕ) : ℝ) else 0) =
      (if k = j then Real.pi * ((a j : ℕ) : ℝ) * ((b j : ℕ) : ℝ) else 0) +
      (if j < k then Real.pi / 2 ^ ((k : ℕ) - j) * ((a j : ℕ) : ℝ) * ((b k : ℕ) : ℝ) else 0) := by
    rcases lt_trichotomy j k with h | rfl | h
    · simp [h.le, h, h.ne']
    · simp
    · simp [not_le_of_gt h, not_lt_of_gt h, h.ne]
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma reversed_value {l : ℕ} (b : Fin l → Fin 2) :
    (bitsVal (bitRev b) : ℝ) = ∑ k : Fin l, (2 : ℝ) ^ (k.rev : ℕ) * (b k : ℕ) := by
  simp only [bitsVal, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, bitRev]
  simpa [Fin.revPerm] using (Equiv.sum_comp Fin.revPerm (fun k : Fin l => (2 : ℝ) ^ (k.rev : ℕ) * (b k : ℕ)))

lemma phase_identity (l : ℕ) (a b : Fin l → Fin 2) :
    Complex.exp
        (((∑ j : Fin l, Real.pi * ((a j : ℕ) : ℝ) * ((b j : ℕ) : ℝ)) +
            ∑ j : Fin l, ∑ k : Fin l,
              if j < k then
                Real.pi / 2 ^ ((k : ℕ) - (j : ℕ)) * ((a j : ℕ) : ℝ) * ((b k : ℕ) : ℝ)
              else 0 : ℝ) * Complex.I) =
      Complex.exp (2 * Real.pi * Complex.I * (bitsVal a : ℂ) * (bitsVal (bitRev b) : ℂ) /
        2 ^ l) := by
  classical
  have he : (∑ j : Fin l, ∑ k : Fin l,
      2 * Real.pi * (2 : ℝ) ^ (j : ℕ) * 2 ^ (k.rev : ℕ) / 2 ^ l * (a j : ℕ) * (b k : ℕ)) =
      2 * Real.pi * (bitsVal a : ℝ) * (bitsVal (bitRev b) : ℝ) / 2 ^ l := by
    rw [reversed_value]
    simp only [bitsVal, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [← sum_phase]
  calc
    _ = Complex.exp (((∑ j : Fin l, ∑ k : Fin l,
        2 * Real.pi * (2 : ℝ) ^ (j : ℕ) * 2 ^ (k.rev : ℕ) / 2 ^ l * (a j : ℕ) * (b k : ℕ)) : ℝ) * Complex.I) := by
      simp only [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
      simp_rw [pair_phase]
    _ = _ := by
      rw [he]
      congr 1
      push_cast
      ring

end AQFT

theorem solution (l : ℕ) (a : Fin l → Fin 2) :
    runCircuit (qftGates l) (basisState a) =
      fun b => ((Real.sqrt (2 ^ l) : ℝ) : ℂ)⁻¹ *
        Complex.exp (2 * Real.pi * Complex.I * (bitsVal a : ℂ) * (bitsVal (bitRev b) : ℂ) /
          2 ^ l)  := by
  funext b
  rw [AQFTCircuit.path_amplitude, AQFT.phase_identity]
