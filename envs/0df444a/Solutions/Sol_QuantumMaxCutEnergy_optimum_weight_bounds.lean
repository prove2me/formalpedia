-- Prove2me | solution 1 for QuantumMaxCutEnergy.optimum_weight_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-31T23:54:49.953605+00:00
-- url     : https://prove2.me/submissions/f04068a7-b8d8-484a-ab83-2158df179bf9

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib.Tactic
import Mathlib.Data.NNRat.BigOperators

noncomputable section
open scoped BigOperators
namespace QuantumMaxCutEnergy

def totalWeight {n : ℕ} (w : Weights n) : ℝ := ∑ e, (w e : ℝ)

lemma normSq_sub_bound (z v : ℂ) :
    Complex.normSq (z - v) ≤ 2 * Complex.normSq z + 2 * Complex.normSq v := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  nlinarith [sq_nonneg (z.re + v.re), sq_nonneg (z.im + v.im)]

def swapBasis {n : ℕ} (a b : Fin n) : Basis n ≃ Basis n where
  toFun x := x ∘ Equiv.swap a b
  invFun x := x ∘ Equiv.swap a b
  left_inv x := by funext i; simp [Function.comp_def]
  right_inv x := by funext i; simp [Function.comp_def]

lemma squaredNorm_swap_sum {n : ℕ} (ψ : Wave n) (a b : Fin n) :
    (∑ x, Complex.normSq (ψ (x ∘ Equiv.swap a b))) = squaredNorm ψ := by
  exact (swapBasis a b).sum_comp (fun x => Complex.normSq (ψ x))

lemma energy_nonnegative {n : ℕ} (w : Weights n)
    (ψ : Wave n) : 0 ≤ energy w ψ := by
  apply Finset.sum_nonneg
  intro e _
  apply mul_nonneg
  · positivity
  · exact Finset.sum_nonneg (fun x _ => Complex.normSq_nonneg _)

lemma energy_upper_bound {n : ℕ} (w : Weights n)
    (ψ : Wave n) :
    energy w ψ ≤ 2 * totalWeight w * squaredNorm ψ := by
  have edge_bound (a b : Fin n) :
      (∑ x, Complex.normSq (ψ x - ψ (x ∘ Equiv.swap a b))) ≤ 4 * squaredNorm ψ := by
    calc
      _ ≤ ∑ x, (2 * Complex.normSq (ψ x) +
            2 * Complex.normSq (ψ (x ∘ Equiv.swap a b))) :=
        Finset.sum_le_sum (fun x _ => normSq_sub_bound _ _)
      _ = 4 * squaredNorm ψ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          squaredNorm_swap_sum]
        unfold squaredNorm
        ring
  calc
    energy w ψ ≤ ∑ e, (w e : ℝ) / 2 * (4 * squaredNorm ψ) := by
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_left (edge_bound _ _) (by positivity)
    _ = ∑ e, (w e : ℝ) * (2 * squaredNorm ψ) := by
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = 2 * totalWeight w * squaredNorm ψ := by
      rw [← Finset.sum_mul]
      unfold totalWeight
      ring

end QuantumMaxCutEnergy

namespace QuantumMaxCutEnergy.BaselineSemantic

def ket {n : ℕ} (b : Basis n) : Wave n := fun x => if x = b then 1 else 0

def cutWeight {n : ℕ} (w : Weights n) (b : Basis n) : ℝ :=
  ∑ e, if b e.val.1 = b e.val.2 then 0 else (w e : ℝ)

lemma squaredNorm_ket {n : ℕ} (b : Basis n) : squaredNorm (ket b) = 1 := by
  classical
  simp [squaredNorm, ket]

lemma sum_delta_difference {α : Type} [Fintype α] [DecidableEq α] (a b : α) :
    (∑ x, Complex.normSq
      ((if x = a then (1 : ℂ) else 0) - (if x = b then (1 : ℂ) else 0))) =
      if a = b then 0 else 2 := by
  classical
  by_cases h : a = b
  · subst b
    simp
  · have hp : ∀ x, Complex.normSq
        ((if x = a then (1 : ℂ) else 0) - (if x = b then (1 : ℂ) else 0)) =
        (if x = a then (1 : ℝ) else 0) + (if x = b then (1 : ℝ) else 0) := by
      intro x
      by_cases ha : x = a
      · subst x
        simp [h]
      · by_cases hb : x = b
        · subst x
          simp [Ne.symm h]
        · simp [ha, hb]
    simp_rw [hp]
    rw [Finset.sum_add_distrib]
    norm_num [h]

lemma ket_swap {n : ℕ} (b x : Basis n) (i j : Fin n) :
    ket b (x ∘ Equiv.swap i j) = ket (b ∘ Equiv.swap i j) x := by
  classical
  have h : (x ∘ Equiv.swap i j = b) ↔ (x = b ∘ Equiv.swap i j) := by
    constructor <;> intro h
    · have hh := congrArg (fun f => f ∘ Equiv.swap i j) h
      simpa only [Function.comp_def, Equiv.swap_apply_self] using hh
    · subst x
      funext k
      simp [Function.comp_def]
  simp only [ket, h]

lemma eq_swap_iff {n : ℕ} (b : Basis n) (i j : Fin n) :
    (b = b ∘ Equiv.swap i j) ↔ b i = b j := by
  constructor
  · intro h
    simpa using congrFun h i
  · intro h
    funext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp_all [Equiv.swap_apply_def]

lemma pairEnergy_ket {n : ℕ} (b : Basis n) (i j : Fin n) :
    (∑ x, Complex.normSq (ket b x - ket b (x ∘ Equiv.swap i j))) =
      if b i = b j then 0 else 2 := by
  simp_rw [ket_swap]
  change (∑ x, Complex.normSq
    ((if x = b then (1 : ℂ) else 0) -
      (if x = b ∘ Equiv.swap i j then (1 : ℂ) else 0))) = _
  rw [sum_delta_difference]
  simp only [eq_swap_iff]

lemma energy_ket {n : ℕ} (w : Weights n) (b : Basis n) :
    energy w (ket b) = cutWeight w b := by
  classical
  unfold energy cutWeight
  apply Finset.sum_congr rfl
  intro e _
  change (w e : ℝ) / 2 *
    (∑ x, Complex.normSq (ket b x - ket b (x ∘ Equiv.swap e.val.1 e.val.2))) = _
  rw [pairEnergy_ket]
  split_ifs <;> ring

def flipBit {n : ℕ} (i : Fin n) (b : Basis n) : Basis n :=
  Function.update b i (!(b i))

lemma flipBit_involutive {n : ℕ} (i : Fin n) : Function.Involutive (flipBit i) := by
  intro b
  funext k
  by_cases hk : k = i
  · subst k
    simp [flipBit]
  · simp [flipBit, hk]

lemma uniform_cut_pair {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (∑ b : Basis n, if b i = b j then (0 : ℝ) else 1) =
      (Fintype.card (Basis n) : ℝ) / 2 := by
  classical
  let f : Basis n → ℝ := fun b => if b i = b j then 0 else 1
  have hflip (b : Basis n) : f (flipBit i b) = 1 - f b := by
    simp only [f, flipBit, Function.update_self,
      Function.update_of_ne (Ne.symm hij)]
    cases hi : b i <;> cases hj : b j <;> norm_num
  have hs : (∑ b, f b) = ∑ b : Basis n, (1 - f b) := by
    calc
      (∑ b, f b) = ∑ b, f (flipBit i b) :=
        ((flipBit_involutive i).bijective.sum_comp f).symm
      _ = _ := by simp_rw [hflip]
  rw [Finset.sum_sub_distrib] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hs
  change (∑ b, f b) = _
  linarith

lemma uniform_cut_sum {n : ℕ} (w : Weights n) :
    (∑ b : Basis n, cutWeight w b) =
      (Fintype.card (Basis n) : ℝ) / 2 * ∑ e, (w e : ℝ) := by
  classical
  unfold cutWeight
  rw [Finset.sum_comm]
  calc
    (∑ e, ∑ b : Basis n, if b e.val.1 = b e.val.2 then 0 else (w e : ℝ)) =
        ∑ e, (w e : ℝ) * ((Fintype.card (Basis n) : ℝ) / 2) := by
      apply Finset.sum_congr rfl
      intro e _
      have h := uniform_cut_pair e.val.1 e.val.2 (ne_of_lt e.property)
      rw [← h, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> ring
    _ = _ := by rw [← Finset.sum_mul]; ring

lemma uniform_basis_energy_sum {n : ℕ} (w : Weights n) :
    (∑ b : Basis n, energy w (ket b)) =
      (Fintype.card (Basis n) : ℝ) / 2 * ∑ e, (w e : ℝ) := by
  simp_rw [energy_ket]
  exact uniform_cut_sum w

def uniformBasisEnergy {n : ℕ} (w : Weights n) : ℝ :=
  (∑ b : Basis n, energy w (ket b)) /
    (Fintype.card (Basis n) : ℝ)

lemma uniformBasisEnergy_eq {n : ℕ} (w : Weights n) :
    uniformBasisEnergy w = (∑ e, (w e : ℝ)) / 2 := by
  have hcard : (Fintype.card (Basis n) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold uniformBasisEnergy
  rw [uniform_basis_energy_sum]
  field_simp

lemma uniformBasis_quarter_of_upper {n : ℕ} (w : Weights n) (ψ : Wave n)
    (hψ : squaredNorm ψ = 1)
    (hupper : energy w ψ ≤
      2 * (∑ e, (w e : ℝ)) * squaredNorm ψ) :
    (1 / 4 : ℝ) * energy w ψ ≤
      uniformBasisEnergy w := by
  rw [uniformBasisEnergy_eq]
  rw [hψ] at hupper
  linarith

end QuantumMaxCutEnergy.BaselineSemantic

namespace QuantumMaxCutEnergy

open BaselineSemantic

lemma energy_values_nonempty (G : Input) :
    {v : ℝ | ∃ ψ : Wave G.n, squaredNorm ψ = 1 ∧ v = energy G.weights ψ}.Nonempty := by
  refine ⟨_, _, squaredNorm_ket (fun _ => false), rfl⟩

lemma energy_values_bddAbove (G : Input) :
    BddAbove {v : ℝ | ∃ ψ : Wave G.n, squaredNorm ψ = 1 ∧ v = energy G.weights ψ} := by
  refine ⟨2 * totalWeight G.weights, ?_⟩
  rintro v ⟨ψ, hψ, rfl⟩
  simpa [hψ] using energy_upper_bound G.weights ψ

lemma energy_le_optimum (G : Input) (ψ : Wave G.n) (hψ : squaredNorm ψ = 1) :
    energy G.weights ψ ≤ optimum G := by
  exact le_csSup (energy_values_bddAbove G) ⟨ψ, hψ, rfl⟩

lemma optimum_le_two_totalWeight (G : Input) :
    optimum G ≤ 2 * totalWeight G.weights := by
  apply csSup_le (energy_values_nonempty G)
  rintro v ⟨ψ, hψ, rfl⟩
  simpa [hψ] using energy_upper_bound G.weights ψ

lemma half_totalWeight_le_optimum (G : Input) :
    totalWeight G.weights / 2 ≤ optimum G := by
  have hcard : (0 : ℝ) < (Fintype.card (Basis G.n) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have havg : uniformBasisEnergy G.weights ≤ optimum G := by
    unfold uniformBasisEnergy
    apply (div_le_iff₀ hcard).2
    calc
      (∑ b : Basis G.n, energy G.weights (ket b)) ≤
          ∑ _b : Basis G.n, optimum G := by
        exact Finset.sum_le_sum (fun b _ => energy_le_optimum G (ket b) (squaredNorm_ket b))
      _ = optimum G * (Fintype.card (Basis G.n) : ℝ) := by
        simp [mul_comm]
  simpa [uniformBasisEnergy_eq, totalWeight] using havg

lemma quarter_optimum_le_half_totalWeight (G : Input) :
    (0.25 : ℝ) * optimum G ≤ totalWeight G.weights / 2 := by
  have h := optimum_le_two_totalWeight G
  linarith

end QuantumMaxCutEnergy

theorem solution (G : QuantumMaxCutEnergy.Input) :
    (∑ e, (G.weights e : ℝ)) / 2 ≤ QuantumMaxCutEnergy.optimum G ∧
      QuantumMaxCutEnergy.optimum G ≤ 2 * (∑ e, (G.weights e : ℝ)) := by
  constructor
  · simpa only [QuantumMaxCutEnergy.totalWeight] using
      QuantumMaxCutEnergy.half_totalWeight_le_optimum G
  · simpa only [QuantumMaxCutEnergy.totalWeight] using
      QuantumMaxCutEnergy.optimum_le_two_totalWeight G

#print axioms solution
