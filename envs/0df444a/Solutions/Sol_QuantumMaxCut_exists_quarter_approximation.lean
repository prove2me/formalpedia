-- Prove2me | solution 1 for QuantumMaxCut.exists_quarter_approximation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-31T22:04:42.424238+00:00
-- url     : https://prove2.me/submissions/11bee644-f671-49e4-8fae-013e8bc2864b

import Definitions.Def_QuantumMaxCutApproximationModel
import Mathlib.Data.Complex.Basic
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fin.Embedding
import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Tactic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith




noncomputable section
open scoped BigOperators
namespace QuantumMaxCut

def totalWeight {n : ℕ} (w : Weights n) : ℝ := ∑ e, (w e : ℝ)

lemma normSq_sub_bound (z v : ℂ) :
    Complex.normSq (z - v) ≤ 2 * Complex.normSq z + 2 * Complex.normSq v := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  nlinarith [sq_nonneg (z.re + v.re), sq_nonneg (z.im + v.im)]

def swapBasis {m : ℕ} (a b : Fin m) : Basis m ≃ Basis m where
  toFun x := x ∘ Equiv.swap a b
  invFun x := x ∘ Equiv.swap a b
  left_inv x := by funext i; simp [Function.comp_def]
  right_inv x := by funext i; simp [Function.comp_def]

lemma squaredNorm_swap_sum {m : ℕ} (ψ : Wave m) (a b : Fin m) :
    (∑ x, Complex.normSq (ψ (x ∘ Equiv.swap a b))) = squaredNorm ψ := by
  exact (swapBasis a b).sum_comp (fun x => Complex.normSq (ψ x))

lemma energy_nonnegative {n m : ℕ} (w : Weights n)
    (sites : Fin n ↪ Fin m) (ψ : Wave m) : 0 ≤ energy w sites ψ := by
  apply Finset.sum_nonneg
  intro e _
  apply mul_nonneg
  · positivity
  · exact Finset.sum_nonneg (fun x _ => Complex.normSq_nonneg _)

lemma energy_upper_bound {n m : ℕ} (w : Weights n)
    (sites : Fin n ↪ Fin m) (ψ : Wave m) :
    energy w sites ψ ≤ 2 * totalWeight w * squaredNorm ψ := by
  have edge_bound (a b : Fin m) :
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
    energy w sites ψ ≤ ∑ e, (w e : ℝ) / 2 * (4 * squaredNorm ψ) := by
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

end QuantumMaxCut



noncomputable section

namespace QuantumMaxCut.BaselineSemantic

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
    energy w (Function.Embedding.refl _) (ket b) = cutWeight w b := by
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
    (∑ b : Basis n, energy w (Function.Embedding.refl _) (ket b)) =
      (Fintype.card (Basis n) : ℝ) / 2 * ∑ e, (w e : ℝ) := by
  simp_rw [energy_ket]
  exact uniform_cut_sum w

def uniformBasisEnergy {n : ℕ} (w : Weights n) : ℝ :=
  (∑ b : Basis n, energy w (Function.Embedding.refl _) (ket b)) /
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
    (hupper : energy w (Function.Embedding.refl _) ψ ≤
      2 * (∑ e, (w e : ℝ)) * squaredNorm ψ) :
    (1 / 4 : ℝ) * energy w (Function.Embedding.refl _) ψ ≤
      uniformBasisEnergy w := by
  rw [uniformBasisEnergy_eq]
  rw [hψ] at hupper
  linarith

end QuantumMaxCut.BaselineSemantic

namespace QuantumMaxCut.BellBaseline

def left {n : ℕ} (i : Fin n) : Fin (n + n) := i.castAdd n
def right {n : ℕ} (i : Fin n) : Fin (n + n) := i.natAdd n

lemma left_ne_right {n : ℕ} (i j : Fin n) : left i ≠ right j := by
  intro h
  have hh := congrArg Fin.val h
  simp only [left, right, Fin.val_castAdd, Fin.val_natAdd] at hh
  omega

lemma right_ne_left {n : ℕ} (i j : Fin n) : right i ≠ left j :=
  Ne.symm (left_ne_right j i)

@[simp] lemma left_eq_left {n : ℕ} {i j : Fin n} : left i = left j ↔ i = j := by
  simp [left, Fin.ext_iff]

@[simp] lemma right_eq_right {n : ℕ} {i j : Fin n} : right i = right j ↔ i = j := by
  simp [right, Fin.ext_iff]

def bellCondition {n : ℕ} (S : Finset (Fin n)) (x : Basis (n + n)) : Prop :=
  ∀ j, if j ∈ S then x (left j) = x (right j)
    else x (left j) = false ∧ x (right j) = false

def partialBell {n : ℕ} (S : Finset (Fin n)) : Wave (n + n) := by
  classical
  exact fun x => if bellCondition S x then ((Real.sqrt 2 : ℂ)⁻¹) ^ S.card else 0

def bellWave (n : ℕ) : Wave (n + n) :=
  fun x => if ∀ i : Fin n, x (i.castAdd n) = x (i.natAdd n)
    then ((Real.sqrt 2 : ℂ)⁻¹) ^ n else 0

lemma condition_step_zero {n : ℕ} (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S)
    (x : Basis (n + n)) :
    bellCondition S
      (Function.update
        (Function.update x (right i) (if x (left i) then !(x (right i)) else x (right i)))
        (left i) false) ↔ bellCondition (insert i S) x := by
  unfold bellCondition
  constructor <;> intro h j
  · by_cases hji : j = i
    · subst j
      have hh := h i
      simp only [hi, if_false, Function.update_self, true_and] at hh
      simp only [Finset.mem_insert_self, if_true]
      cases hx : x (left i) <;> cases hy : x (right i) <;>
        simp_all [Function.update, left_ne_right, right_ne_left]
    · have hh := h j
      simpa [Finset.mem_insert, hji, Function.update_of_ne,
        left_ne_right, right_ne_left] using hh
  · by_cases hji : j = i
    · subst j
      have hh := h i
      simp only [Finset.mem_insert_self, if_true] at hh
      simp only [hi, if_false, Function.update_self, true_and]
      cases hx : x (left i) <;> cases hy : x (right i) <;>
        simp_all [Function.update, right_ne_left]
    · have hh := h j
      simpa [Finset.mem_insert, hji, Function.update_of_ne,
        left_ne_right, right_ne_left] using hh

lemma condition_step_one_false {n : ℕ} (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S)
    (x : Basis (n + n)) :
    ¬bellCondition S
      (Function.update
        (Function.update x (right i) (if x (left i) then !(x (right i)) else x (right i)))
        (left i) true) := by
  intro h
  have hh := h i
  simp [hi] at hh

lemma bell_step {n : ℕ} (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    applyGate (.cx (left i) (right i) (left_ne_right i i))
      (applyGate (.h (left i)) (partialBell S)) = partialBell (insert i S) := by
  classical
  funext x
  simp only [applyGate]
  have h0 := condition_step_zero S i hi x
  have h1 := condition_step_one_false S i hi x
  simp only [partialBell, h0, h1, if_false, mul_zero, add_zero,
    Finset.card_insert_of_notMem hi, pow_succ]
  split_ifs <;> simp [div_eq_mul_inv]

lemma condition_empty {n : ℕ} (x : Basis (n + n)) :
    bellCondition (∅ : Finset (Fin n)) x ↔ x = (fun _ => false) := by
  constructor
  · intro h
    have hh : ∀ j, x (left j) = false ∧ x (right j) = false := by
      simpa [bellCondition] using h
    funext k
    exact Fin.addCases (fun i => (hh i).1) (fun i => (hh i).2) k
  · intro h
    subst x
    simp [bellCondition]

lemma partialBell_empty {n : ℕ} :
    partialBell (∅ : Finset (Fin n)) =
      (fun x => if x = (fun _ => false) then (1 : ℂ) else 0) := by
  funext x
  simp only [partialBell, condition_empty, Finset.card_empty, pow_zero]

def bellGates {n : ℕ} (i : Fin n) : List (Gate (n + n)) :=
  [.h (left i), .cx (left i) (right i) (left_ne_right i i)]

def bellCircuit (n : ℕ) : Circuit :=
  ⟨n + n, (List.finRange n).flatMap bellGates⟩

lemma fold_bellGates {n : ℕ} (l : List (Fin n)) (hn : l.Nodup)
    (S : Finset (Fin n)) (hs : ∀ i ∈ l, i ∉ S) :
    (l.flatMap bellGates).foldl (fun ψ gate => applyGate gate ψ) (partialBell S) =
      partialBell (S ∪ l.toFinset) := by
  induction l generalizing S with
  | nil => simp
  | cons i l ih =>
      simp only [List.nodup_cons] at hn
      simp only [List.flatMap_cons, List.foldl_append, bellGates,
        List.foldl_cons, List.foldl_nil]
      rw [bell_step S i (hs i (by simp))]
      have hs' : ∀ j ∈ l, j ∉ insert i S := by
        intro j hj
        simp only [Finset.mem_insert, not_or]
        constructor
        · intro hji
          subst j
          exact hn.1 hj
        · exact hs j (by simp [hj])
      rw [ih hn.2 (insert i S) hs']
      congr 1
      ext j
      simp

theorem bellCircuit_state (n : ℕ) : (bellCircuit n).state = bellWave n := by
  change ((List.finRange n).flatMap bellGates).foldl
    (fun ψ gate => applyGate gate ψ)
    (fun x => if x = (fun _ => false) then 1 else 0) = bellWave n
  rw [← partialBell_empty]
  rw [fold_bellGates (List.finRange n) (List.nodup_finRange n) ∅ (by simp)]
  have hl : (List.finRange n).toFinset = Finset.univ := by ext i; simp
  rw [hl, Finset.empty_union]
  funext x
  simp [partialBell, bellCondition, bellWave, left, right]

end QuantumMaxCut.BellBaseline

namespace QuantumMaxCut.BellBaseline
open BaselineSemantic

def diagonalWave (n : ℕ) (c : ℂ) : Wave (n + n) :=
  fun x => if ∀ i : Fin n, x (i.castAdd n) = x (i.natAdd n) then c else 0

lemma bellWave_eq_diagonalWave (n : ℕ) :
    bellWave n = diagonalWave n (((Real.sqrt 2 : ℂ)⁻¹) ^ n) := rfl

lemma diagonalWave_append {n : ℕ} (c : ℂ) (b a : Basis n) :
    diagonalWave n c (Fin.append b a) = c * ket a b := by
  classical
  simp only [diagonalWave, Fin.append_left, Fin.append_right, ← funext_iff, ket]
  split_ifs <;> simp_all

lemma squaredNorm_diagonalWave (n : ℕ) (c : ℂ) :
    squaredNorm (diagonalWave n c) =
      (Fintype.card (Basis n) : ℝ) * Complex.normSq c := by
  classical
  unfold squaredNorm
  rw [← (Fin.appendEquiv n n).sum_comp]
  change (∑ ba : Basis n × Basis n,
    Complex.normSq (diagonalWave n c (Fin.append ba.1 ba.2))) = _
  rw [Fintype.sum_prod_type]
  simp_rw [diagonalWave_append]
  simp [ket, apply_ite]

lemma append_swap_left {n : ℕ} (b a : Basis n) (i j : Fin n) :
    (Fin.append b a) ∘ Equiv.swap (i.castAdd n) (j.castAdd n) =
      Fin.append (b ∘ Equiv.swap i j) a := by
  funext k
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k
  · by_cases hki : k = i
    · subst k
      simp [Function.comp_def]
    · by_cases hkj : k = j
      · subst k
        simp [Function.comp_def]
      · simp [Function.comp_def, Equiv.swap_apply_def, hki, hkj]
  · have hi : k.natAdd n ≠ i.castAdd n := by
      intro h
      have hv := congrArg Fin.val h
      change n + k.val = i.val at hv
      omega
    have hj : k.natAdd n ≠ j.castAdd n := by
      intro h
      have hv := congrArg Fin.val h
      change n + k.val = j.val at hv
      omega
    change Fin.append b a
      ((Equiv.swap (i.castAdd n) (j.castAdd n)) (k.natAdd n)) =
        Fin.append (b ∘ Equiv.swap i j) a (k.natAdd n)
    rw [Equiv.swap_apply_of_ne_of_ne hi hj]
    simp only [Fin.append_right]

lemma pairEnergy_diagonalWave {n : ℕ} (c : ℂ) (i j : Fin n) :
    (∑ x : Basis (n + n), Complex.normSq
      (diagonalWave n c x - diagonalWave n c
        (x ∘ Equiv.swap (i.castAdd n) (j.castAdd n)))) =
      Complex.normSq c * ∑ a : Basis n, ∑ b : Basis n,
        Complex.normSq (ket a b - ket a (b ∘ Equiv.swap i j)) := by
  classical
  rw [← (Fin.appendEquiv n n).sum_comp]
  change (∑ ba : Basis n × Basis n, Complex.normSq
    (diagonalWave n c (Fin.append ba.1 ba.2) - diagonalWave n c
      ((Fin.append ba.1 ba.2) ∘ Equiv.swap (i.castAdd n) (j.castAdd n)))) = _
  rw [Fintype.sum_prod_type]
  simp_rw [append_swap_left, diagonalWave_append, ← mul_sub, map_mul]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_comm]

lemma energy_diagonalWave {n : ℕ} (w : Weights n) (c : ℂ) :
    energy w (Fin.castAddEmb n) (diagonalWave n c) =
      Complex.normSq c * ∑ a : Basis n,
        energy w (Function.Embedding.refl _) (ket a) := by
  classical
  unfold energy
  simp only [Fin.castAddEmb_apply, Function.Embedding.refl_apply]
  simp_rw [pairEnergy_diagonalWave]
  calc
    (∑ e, (w e : ℝ) / 2 * (Complex.normSq c *
      ∑ a : Basis n, ∑ b : Basis n,
        Complex.normSq (ket a b - ket a (b ∘ Equiv.swap e.val.1 e.val.2)))) =
      ∑ e, ∑ a : Basis n, Complex.normSq c * ((w e : ℝ) / 2 *
        ∑ b : Basis n, Complex.normSq
          (ket a b - ket a (b ∘ Equiv.swap e.val.1 e.val.2))) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.mul_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ a : Basis n, ∑ e, Complex.normSq c * ((w e : ℝ) / 2 *
        ∑ b : Basis n, Complex.normSq
          (ket a b - ket a (b ∘ Equiv.swap e.val.1 e.val.2))) := Finset.sum_comm
    _ = _ := by simp_rw [Finset.mul_sum]

lemma normSq_bellCoefficient (n : ℕ) :
    Complex.normSq (((Real.sqrt 2 : ℂ)⁻¹) ^ n) = (1 / 2 : ℝ) ^ n := by
  have hs : Complex.normSq (Real.sqrt 2 : ℂ) = 2 := by
    rw [Complex.normSq_ofReal]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [map_pow, Complex.normSq_inv, hs]
  norm_num

lemma card_basis (n : ℕ) : Fintype.card (Basis n) = 2 ^ n := by
  simp [Basis]

lemma squaredNorm_bellWave (n : ℕ) : squaredNorm (bellWave n) = 1 := by
  rw [bellWave_eq_diagonalWave, squaredNorm_diagonalWave,
    normSq_bellCoefficient, card_basis]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [← mul_pow]
  norm_num

lemma energy_bellWave {n : ℕ} (w : Weights n) :
    energy w (Fin.castAddEmb n) (bellWave n) = (∑ e, (w e : ℝ)) / 2 := by
  rw [bellWave_eq_diagonalWave, energy_diagonalWave, uniform_basis_energy_sum]
  have hc : Complex.normSq (((Real.sqrt 2 : ℂ)⁻¹) ^ n) *
      (Fintype.card (Basis n) : ℝ) = 1 := by
    have h := squaredNorm_bellWave n
    rw [bellWave_eq_diagonalWave, squaredNorm_diagonalWave] at h
    rw [mul_comm]
    exact h
  calc
    Complex.normSq (((Real.sqrt 2 : ℂ)⁻¹) ^ n) *
      ((Fintype.card (Basis n) : ℝ) / 2 * ∑ e, (w e : ℝ)) =
        (Complex.normSq (((Real.sqrt 2 : ℂ)⁻¹) ^ n) *
          (Fintype.card (Basis n) : ℝ)) * ((∑ e, (w e : ℝ)) / 2) := by ring
    _ = _ := by rw [hc]; ring

end QuantumMaxCut.BellBaseline

namespace QuantumMaxCut.BellBaseline

def bellAlgorithm : Algorithm := fun G => bellCircuit G.n

theorem bellAlgorithm_normalized (G : Input) :
    squaredNorm (bellAlgorithm G).state = 1 := by
  change squaredNorm (bellCircuit G.n).state = 1
  rw [bellCircuit_state]
  exact squaredNorm_bellWave G.n

theorem bellAlgorithm_quarter : ApproximationRatio bellAlgorithm (1 / 4 : ℝ) := by
  intro G
  refine ⟨by change G.n ≤ G.n + G.n; omega, ?_⟩
  intro ψ hψ
  change (1 / 4 : ℝ) * energy G.weights (Function.Embedding.refl _) ψ ≤
    energy G.weights (Fin.castAddEmb G.n) (bellCircuit G.n).state
  rw [bellCircuit_state, energy_bellWave]
  have hu := energy_upper_bound G.weights (Function.Embedding.refl _) ψ
  rw [hψ] at hu
  unfold totalWeight at hu
  linarith

end QuantumMaxCut.BellBaseline




open Turing StateTransition
namespace QMCBellRuntime
open QuantumMaxCut

abbrev Stack := Fin 7
abbrev Label := Fin 15
abbrev inputStack : Stack := 0
abbrev outputStack : Stack := 1
abbrev remainingStack : Stack := 2
abbrev indexStack : Stack := 3
abbrev targetStack : Stack := 4
abbrev tempStack : Stack := 5
abbrev bufferStack : Stack := 6

def copyStmt (src : Stack) (again restore : Label) :
    TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool) :=
  .pop src (fun _ x => x) (.branch (fun x => x.isSome)
    (.push bufferStack (fun _ => true) (.push tempStack (fun _ => true)
      (.goto (fun _ => again))))
    (.goto (fun _ => restore)))

def restoreStmt (src : Stack) (again next : Label) :
    TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool) :=
  .pop tempStack (fun _ x => x) (.branch (fun x => x.isSome)
    (.push src (fun _ => true) (.goto (fun _ => again)))
    (.goto (fun _ => next)))

def program (l : Label) : TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool) :=
  match l.val with
  | 0 => .pop inputStack (fun _ x => x) (.branch (fun x => x == some true)
      (.push remainingStack (fun _ => true) (.push targetStack (fun _ => true)
        (.push bufferStack (fun _ => true) (.push bufferStack (fun _ => true)
          (.goto (fun _ => 0))))))
      (.push bufferStack (fun _ => false) (.goto (fun _ => 1))))
  | 1 => .pop inputStack (fun _ x => x) (.branch (fun x => x.isSome)
      (.goto (fun _ => 1)) (.goto (fun _ => 2)))
  | 2 => .pop remainingStack (fun _ x => x) (.branch (fun x => x.isSome)
      (.push bufferStack (fun _ => false) (.push bufferStack (fun _ => false)
        (.goto (fun _ => 9))))
      (.goto (fun _ => 6)))
  | 3 => .push bufferStack (fun _ => false) (.push bufferStack (fun _ => true)
      (.push bufferStack (fun _ => false) (.goto (fun _ => 11))))
  | 4 => .push bufferStack (fun _ => false) (.goto (fun _ => 13))
  | 5 => .push bufferStack (fun _ => false) (.push indexStack (fun _ => true)
      (.push targetStack (fun _ => true) (.goto (fun _ => 2))))
  | 6 => .pop indexStack (fun _ x => x) (.branch (fun x => x.isSome)
      (.goto (fun _ => 6)) (.goto (fun _ => 7)))
  | 7 => .pop targetStack (fun _ x => x) (.branch (fun x => x.isSome)
      (.goto (fun _ => 7)) (.goto (fun _ => 8)))
  | 8 => .pop bufferStack (fun _ x => x) (.branch (fun x => x.isSome)
      (.push outputStack (fun x => x.getD false) (.goto (fun _ => 8)))
      (.load (fun _ => none) .halt))
  | 9 => copyStmt indexStack 9 10
  | 10 => restoreStmt indexStack 10 3
  | 11 => copyStmt indexStack 11 12
  | 12 => restoreStmt indexStack 12 4
  | 13 => copyStmt targetStack 13 14
  | _ => restoreStmt targetStack 14 5

abbrev machine : FinTM2 where
  K := Stack
  k₀ := inputStack
  k₁ := outputStack
  Γ _ := Bool
  Λ := Label
  main := 0
  σ := Option Bool
  initialState := none
  m := program

structure Stacks where
  input : List Bool := []
  output : List Bool := []
  remaining : List Bool := []
  index : List Bool := []
  target : List Bool := []
  temp : List Bool := []
  buffer : List Bool := []

def cfg (l : Option Label) (v : Option Bool) (s : Stacks) : machine.Cfg :=
  ⟨l, v, ![s.input, s.output, s.remaining, s.index, s.target, s.temp, s.buffer]⟩

def one_step {a b : machine.Cfg} (h : machine.step a = some b) :
    EvalsToInTime machine.step a (some b) 1 where
  steps := 1
  evals_in_steps := by change machine.step a = some b; exact h
  steps_le_m := le_rfl

def weaken {a : machine.Cfg} {b : Option machine.Cfg} {m n : ℕ}
    (h : EvalsToInTime machine.step a b m) (hmn : m ≤ n) :
    EvalsToInTime machine.step a b n :=
  ⟨h.toEvalsTo, h.steps_le_m.trans hmn⟩

lemma step_parse_true (v : Option Bool) (s : Stacks) :
    machine.step (cfg (some 0) v {s with input := true :: s.input}) =
      some (cfg (some 0) (some true) {s with
        remaining := true :: s.remaining, target := true :: s.target,
        buffer := true :: true :: s.buffer}) := by
  simp [FinTM2.step, TM2.step, TM2.stepAux, program, cfg, Function.update,
    funext_iff, Fin.forall_fin_succ, inputStack, outputStack, remainingStack, indexStack, targetStack, tempStack, bufferStack] <;> congr 2 <;> funext k <;> fin_cases k <;> rfl

lemma step_parse_false (v : Option Bool) (s : Stacks) :
    machine.step (cfg (some 0) v {s with input := false :: s.input}) =
      some (cfg (some 1) (some false) {s with buffer := false :: s.buffer}) := by
  simp [FinTM2.step, TM2.step, TM2.stepAux, program, cfg, Function.update,
    funext_iff, Fin.forall_fin_succ, inputStack, outputStack, remainingStack, indexStack, targetStack, tempStack, bufferStack] <;> congr 2 <;> funext k <;> fin_cases k <;> rfl

lemma step_discard_nil (v : Option Bool) (s : Stacks) (h : s.input = []) :
    machine.step (cfg (some 1) v s) = some (cfg (some 2) none s) := by
  simp [FinTM2.step, TM2.step, TM2.stepAux, program, cfg, Function.update,
    funext_iff, Fin.forall_fin_succ, h, inputStack, outputStack, remainingStack, indexStack, targetStack, tempStack, bufferStack] <;> congr 2 <;> funext k <;> fin_cases k <;> rfl

lemma step_discard_cons (v : Option Bool) (b : Bool) (s : Stacks) :
    machine.step (cfg (some 1) v {s with input := b :: s.input}) =
      some (cfg (some 1) (some b) s) := by
  cases b <;> simp [FinTM2.step, TM2.step, TM2.stepAux, program, cfg, Function.update,
    funext_iff, Fin.forall_fin_succ, inputStack, outputStack, remainingStack, indexStack, targetStack, tempStack, bufferStack] <;> congr 2 <;> funext k <;> fin_cases k <;> rfl

lemma step_loop_true (v : Option Bool) (s : Stacks) :
    machine.step (cfg (some 2) v {s with remaining := true :: s.remaining}) =
      some (cfg (some 9) (some true) {s with buffer := false :: false :: s.buffer}) := by
  simp [FinTM2.step, TM2.step, TM2.stepAux, program, cfg, Function.update,
    funext_iff, Fin.forall_fin_succ, inputStack, outputStack, remainingStack, indexStack, targetStack, tempStack, bufferStack] <;> congr 2 <;> funext k <;> fin_cases k <;> rfl

lemma step_loop_nil (v : Option Bool) (s : Stacks) (h : s.remaining = []) :
    machine.step (cfg (some 2) v s) = some (cfg (some 6) none s) := by
  simp [FinTM2.step, TM2.step, TM2.stepAux, program, cfg, Function.update,
    funext_iff, Fin.forall_fin_succ, h, inputStack, outputStack, remainingStack, indexStack, targetStack, tempStack, bufferStack] <;> congr 2 <;> funext k <;> fin_cases k <;> rfl

lemma step_afterH (v : Option Bool) (s : Stacks) :
    machine.step (cfg (some 3) v s) = some (cfg (some 11) v
      {s with buffer := false :: true :: false :: s.buffer}) := by
  simp [FinTM2.step, TM2.step, TM2.stepAux, program, cfg, Function.update,
    funext_iff, Fin.forall_fin_succ, inputStack, outputStack, remainingStack, indexStack, targetStack, tempStack, bufferStack] <;> congr 2 <;> funext k <;> fin_cases k <;> rfl

lemma step_afterControl (v : Option Bool) (s : Stacks) :
    machine.step (cfg (some 4) v s) = some (cfg (some 13) v
      {s with buffer := false :: s.buffer}) := by
  simp [FinTM2.step, TM2.step, TM2.stepAux, program, cfg, Function.update,
    funext_iff, Fin.forall_fin_succ, inputStack, outputStack, remainingStack, indexStack, targetStack, tempStack, bufferStack] <;> congr 2 <;> funext k <;> fin_cases k <;> rfl

lemma step_afterTarget (v : Option Bool) (s : Stacks) :
    machine.step (cfg (some 5) v s) = some (cfg (some 2) v
      {s with buffer := false :: s.buffer, index := true :: s.index, target := true :: s.target}) := by
  simp [FinTM2.step, TM2.step, TM2.stepAux, program, cfg, Function.update,
    funext_iff, Fin.forall_fin_succ, inputStack, outputStack, remainingStack, indexStack, targetStack, tempStack, bufferStack] <;> congr 2 <;> funext k <;> fin_cases k <;> rfl

def unary (n : ℕ) : List Bool := List.replicate n true ++ [false]

def block (n i : ℕ) : List Bool :=
  [false, false] ++ unary i ++ [true, false] ++ unary i ++ unary (n + i)

def bellCode (n : ℕ) : List Bool :=
  unary (2 * n) ++ (List.range n).flatMap (block n)

def encodeGateUnary {n : ℕ} : Gate n → List Bool
  | .h i => [false, false] ++ unary i.val
  | .t i => [false, true] ++ unary i.val
  | .cx i j _ => [true, false] ++ unary i.val ++ unary j.val

def encodeCircuitUnary (C : Circuit) : List Bool :=
  unary C.qubits ++ C.gates.flatMap encodeGateUnary

def bellGates (n : ℕ) : List (Gate (n + n)) :=
  (List.finRange n).flatMap (fun i =>
    let q : Fin (n + n) := i.castAdd n
    let a : Fin (n + n) := i.natAdd n
    [.h q, .cx q a (by
      intro h
      have hh := congrArg Fin.val h
      change i.val = n + i.val at hh
      have hi := i.isLt
      omega)])

def bellAlgorithm (G : Input) : Circuit := ⟨G.n + G.n, bellGates G.n⟩

end QMCBellRuntime



open Turing StateTransition
namespace QMCBellRuntime

abbrev CopyPhase := Fin 3

def copyLabel (p : CopyPhase) : Label :=
  if p = 0 then 9 else if p = 1 then 11 else 13

def restoreLabel (p : CopyPhase) : Label :=
  if p = 0 then 10 else if p = 1 then 12 else 14

def nextLabel (p : CopyPhase) : Label :=
  if p = 0 then 3 else if p = 1 then 4 else 5

def sourceList (p : CopyPhase) (s : Stacks) : List Bool :=
  if p = 2 then s.target else s.index

def copyFrame (p : CopyPhase) (s : Stacks) (source temp : ℕ)
    (buffer : List Bool) : Stacks :=
  if p = 2 then
    {s with
      target := List.replicate source true,
      temp := List.replicate temp true, buffer := buffer}
  else
    {s with
      index := List.replicate source true,
      temp := List.replicate temp true, buffer := buffer}

lemma step_copy_nil (p : CopyPhase) (s : Stacks) (t : ℕ)
    (buffer : List Bool) (v : Option Bool) :
    machine.step (cfg (some (copyLabel p)) v (copyFrame p s 0 t buffer)) =
      some (cfg (some (restoreLabel p)) none (copyFrame p s 0 t buffer)) := by
  fin_cases p <;>
    simp [FinTM2.step, TM2.step, TM2.stepAux, program, copyStmt, cfg,
      copyFrame, copyLabel, restoreLabel, inputStack, outputStack,
      remainingStack, indexStack, targetStack, tempStack, bufferStack] <;>
    congr 2 <;> funext k <;> fin_cases k <;> rfl

lemma step_copy_cons (p : CopyPhase) (s : Stacks) (k t : ℕ)
    (buffer : List Bool) (v : Option Bool) :
    machine.step (cfg (some (copyLabel p)) v (copyFrame p s (k + 1) t buffer)) =
      some (cfg (some (copyLabel p)) (some true)
        (copyFrame p s k (t + 1) (true :: buffer))) := by
  fin_cases p <;>
    simp [FinTM2.step, TM2.step, TM2.stepAux, program, copyStmt, cfg,
      copyFrame, copyLabel, restoreLabel, List.replicate_succ, inputStack, outputStack,
      remainingStack, indexStack, targetStack, tempStack, bufferStack] <;>
    congr 2 <;> funext j <;> fin_cases j <;> rfl

lemma step_restore_nil (p : CopyPhase) (s : Stacks) (k : ℕ)
    (buffer : List Bool) (v : Option Bool) :
    machine.step (cfg (some (restoreLabel p)) v (copyFrame p s k 0 buffer)) =
      some (cfg (some (nextLabel p)) none (copyFrame p s k 0 buffer)) := by
  fin_cases p <;>
    simp [FinTM2.step, TM2.step, TM2.stepAux, program, restoreStmt, cfg,
      copyFrame, restoreLabel, nextLabel, inputStack, outputStack,
      remainingStack, indexStack, targetStack, tempStack, bufferStack] <;>
    congr 2 <;> funext j <;> fin_cases j <;> rfl

lemma step_restore_cons (p : CopyPhase) (s : Stacks) (k t : ℕ)
    (buffer : List Bool) (v : Option Bool) :
    machine.step (cfg (some (restoreLabel p)) v (copyFrame p s k (t + 1) buffer)) =
      some (cfg (some (restoreLabel p)) (some true)
        (copyFrame p s (k + 1) t buffer)) := by
  fin_cases p <;>
    simp [FinTM2.step, TM2.step, TM2.stepAux, program, restoreStmt, cfg,
      copyFrame, restoreLabel, nextLabel, List.replicate_succ, inputStack, outputStack,
      remainingStack, indexStack, targetStack, tempStack, bufferStack] <;>
    congr 2 <;> funext j <;> fin_cases j <;> rfl

def copy_phase_runs (p : CopyPhase) (s : Stacks) (k t : ℕ)
    (buffer : List Bool) (v : Option Bool) :
    EvalsToInTime machine.step
      (cfg (some (copyLabel p)) v (copyFrame p s k t buffer))
      (some (cfg (some (restoreLabel p)) none
        (copyFrame p s 0 (k + t) (List.replicate k true ++ buffer))))
      (k + 1) := by
  induction k generalizing t buffer v with
  | zero => simpa using one_step (step_copy_nil p s t buffer v)
  | succ k ih =>
      have h := EvalsToInTime.trans machine.step 1 (k + 1) _ _ _
        (one_step (step_copy_cons p s k t buffer v))
        (ih (t + 1) (true :: buffer) (some true))
      have hout : List.replicate k true ++ true :: buffer =
          List.replicate (k + 1) true ++ buffer := by
        simp [List.replicate_succ', List.append_assoc]
      have hcount : k + (t + 1) = (k + 1) + t := by omega
      simpa [hcount, hout, Nat.add_assoc] using h

def restore_phase_runs (p : CopyPhase) (s : Stacks) (t k : ℕ)
    (buffer : List Bool) (v : Option Bool) :
    EvalsToInTime machine.step
      (cfg (some (restoreLabel p)) v (copyFrame p s k t buffer))
      (some (cfg (some (nextLabel p)) none (copyFrame p s (t + k) 0 buffer)))
      (t + 1) := by
  induction t generalizing k v with
  | zero => simpa using one_step (step_restore_nil p s k buffer v)
  | succ t ih =>
      have h := EvalsToInTime.trans machine.step 1 (t + 1) _ _ _
        (one_step (step_restore_cons p s k t buffer v))
        (ih (k + 1) (some true))
      have hcount : t + (k + 1) = (t + 1) + k := by omega
      simpa [hcount, Nat.add_assoc] using h

lemma copyFrame_eq (p : CopyPhase) (s : Stacks) (k : ℕ) (buffer : List Bool)
    (hsource : sourceList p s = List.replicate k true) (htemp : s.temp = []) :
    copyFrame p s k 0 buffer = {s with buffer := buffer} := by
  fin_cases p <;> cases s <;> simp_all [copyFrame, sourceList]

/-- Copy the source unary counter to the buffer and restore the source.
The temporary stack is empty again, and every other stack is unchanged. -/
def copy_restore_runs (p : CopyPhase) (s : Stacks) (k : ℕ) (v : Option Bool)
    (hsource : sourceList p s = List.replicate k true) (htemp : s.temp = []) :
    EvalsToInTime machine.step (cfg (some (copyLabel p)) v s)
      (some (cfg (some (nextLabel p)) none
        {s with buffer := List.replicate k true ++ s.buffer}))
      (2 * k + 2) := by
  have h := EvalsToInTime.trans machine.step (k + 1) (k + 1) _ _ _
    (copy_phase_runs p s k 0 s.buffer v)
    (by simpa using restore_phase_runs p s k 0 (List.replicate k true ++ s.buffer) none)
  have hstart := copyFrame_eq p s k s.buffer hsource htemp
  have hend := copyFrame_eq p s k (List.replicate k true ++ s.buffer) hsource htemp
  have hs : ({s with buffer := s.buffer} : Stacks) = s := by cases s; rfl
  rw [hstart, hs, hend] at h
  simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

def copy_index_to_three (s : Stacks) (k : ℕ) (v : Option Bool)
    (hsource : s.index = List.replicate k true) (htemp : s.temp = []) :
    EvalsToInTime machine.step (cfg (some 9) v s)
      (some (cfg (some 3) none {s with buffer := List.replicate k true ++ s.buffer}))
      (2 * k + 2) := by
  simpa [copyLabel, nextLabel, sourceList] using copy_restore_runs 0 s k v hsource htemp

def copy_index_to_four (s : Stacks) (k : ℕ) (v : Option Bool)
    (hsource : s.index = List.replicate k true) (htemp : s.temp = []) :
    EvalsToInTime machine.step (cfg (some 11) v s)
      (some (cfg (some 4) none {s with buffer := List.replicate k true ++ s.buffer}))
      (2 * k + 2) := by
  simpa [copyLabel, nextLabel, sourceList] using copy_restore_runs 1 s k v hsource htemp

def copy_target_to_five (s : Stacks) (k : ℕ) (v : Option Bool)
    (hsource : s.target = List.replicate k true) (htemp : s.temp = []) :
    EvalsToInTime machine.step (cfg (some 13) v s)
      (some (cfg (some 5) none {s with buffer := List.replicate k true ++ s.buffer}))
      (2 * k + 2) := by
  simpa [copyLabel, nextLabel, sourceList] using copy_restore_runs 2 s k v hsource htemp

def copyI9_runs (s : Stacks) (k : ℕ)
    (hsrc : s.index = List.replicate k true) (ht : s.temp = []) (v : Option Bool) :=
  copy_index_to_three s k v hsrc ht

def copyI11_runs (s : Stacks) (k : ℕ)
    (hsrc : s.index = List.replicate k true) (ht : s.temp = []) (v : Option Bool) :=
  copy_index_to_four s k v hsrc ht

def copyJ13_runs (s : Stacks) (k : ℕ)
    (hsrc : s.target = List.replicate k true) (ht : s.temp = []) (v : Option Bool) :=
  copy_target_to_five s k v hsrc ht


end QMCBellRuntime



open Turing StateTransition
namespace QMCBellRuntime

def parsed (n : ℕ) (xs : List Bool) : Stacks :=
  {input := xs, remaining := List.replicate n true,
   target := List.replicate n true, buffer := List.replicate (2 * n) true}

def parse_runs (n m : ℕ) (xs : List Bool) (v : Option Bool) :
    EvalsToInTime machine.step
      (cfg (some 0) v (parsed m (List.replicate n true ++ false :: xs)))
      (some (cfg (some 1) (some false)
        {parsed (m + n) xs with buffer := false :: List.replicate (2 * (m + n)) true}))
      (n + 1) := by
  induction n generalizing m v with
  | zero => simpa [parsed] using one_step (step_parse_false v (parsed m xs))
  | succ n ih =>
      have hs := step_parse_true v (parsed m (List.replicate n true ++ false :: xs))
      have hi := ih (m + 1) (some true)
      have hc := EvalsToInTime.trans machine.step 1 (n + 1) _ _ _ (one_step hs) hi
      simpa [parsed, List.replicate_succ, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hc

def discard_runs (xs : List Bool) (s : Stacks) (v : Option Bool) :
    EvalsToInTime machine.step (cfg (some 1) v {s with input := xs})
      (some (cfg (some 2) none {s with input := []})) (xs.length + 1) := by
  induction xs generalizing v with
  | nil => exact one_step (step_discard_nil v _ rfl)
  | cons b xs ih =>
      have hs := step_discard_cons v b {s with input := xs}
      have hc := EvalsToInTime.trans machine.step 1 (xs.length + 1) _ _ _
        (one_step hs) (ih (some b))
      simpa [Nat.add_assoc] using hc

lemma step_cleanI_nil (v : Option Bool) (s : Stacks) :
    machine.step (cfg (some 6) v {s with index := []}) =
      some (cfg (some 7) none {s with index := []}) := by
  simp [FinTM2.step, TM2.step, TM2.stepAux, program, cfg, Function.update,
    inputStack, outputStack, remainingStack, indexStack, targetStack, tempStack, bufferStack]
    <;> congr 2 <;> funext k <;> fin_cases k <;> rfl

lemma step_cleanI_cons (v : Option Bool) (b : Bool) (s : Stacks) :
    machine.step (cfg (some 6) v {s with index := b :: s.index}) =
      some (cfg (some 6) (some b) s) := by
  cases b <;>
    simp [FinTM2.step, TM2.step, TM2.stepAux, program, cfg, Function.update,
      inputStack, outputStack, remainingStack, indexStack, targetStack, tempStack, bufferStack]
    <;> congr 2 <;> funext k <;> fin_cases k <;> rfl

def cleanI_runs (xs : List Bool) (s : Stacks) (v : Option Bool) :
    EvalsToInTime machine.step (cfg (some 6) v {s with index := xs})
      (some (cfg (some 7) none {s with index := []})) (xs.length + 1) := by
  induction xs generalizing v with
  | nil => exact one_step (step_cleanI_nil v s)
  | cons b xs ih =>
      have hc := EvalsToInTime.trans machine.step 1 (xs.length + 1) _ _ _
        (one_step (step_cleanI_cons v b {s with index := xs})) (ih (some b))
      simpa [Nat.add_assoc] using hc

lemma step_cleanJ_nil (v : Option Bool) (s : Stacks) :
    machine.step (cfg (some 7) v {s with target := []}) =
      some (cfg (some 8) none {s with target := []}) := by
  simp [FinTM2.step, TM2.step, TM2.stepAux, program, cfg, Function.update,
    inputStack, outputStack, remainingStack, indexStack, targetStack, tempStack, bufferStack]
    <;> congr 2 <;> funext k <;> fin_cases k <;> rfl

lemma step_cleanJ_cons (v : Option Bool) (b : Bool) (s : Stacks) :
    machine.step (cfg (some 7) v {s with target := b :: s.target}) =
      some (cfg (some 7) (some b) s) := by
  cases b <;>
    simp [FinTM2.step, TM2.step, TM2.stepAux, program, cfg, Function.update,
      inputStack, outputStack, remainingStack, indexStack, targetStack, tempStack, bufferStack]
    <;> congr 2 <;> funext k <;> fin_cases k <;> rfl

def cleanJ_runs (xs : List Bool) (s : Stacks) (v : Option Bool) :
    EvalsToInTime machine.step (cfg (some 7) v {s with target := xs})
      (some (cfg (some 8) none {s with target := []})) (xs.length + 1) := by
  induction xs generalizing v with
  | nil => exact one_step (step_cleanJ_nil v s)
  | cons b xs ih =>
      have hc := EvalsToInTime.trans machine.step 1 (xs.length + 1) _ _ _
        (one_step (step_cleanJ_cons v b {s with target := xs})) (ih (some b))
      simpa [Nat.add_assoc] using hc

lemma step_reverse_nil (v : Option Bool) (s : Stacks) :
    machine.step (cfg (some 8) v {s with buffer := []}) =
      some (cfg none none {s with buffer := []}) := by
  simp [FinTM2.step, TM2.step, TM2.stepAux, program, cfg, Function.update,
    inputStack, outputStack, remainingStack, indexStack, targetStack, tempStack, bufferStack]
    <;> congr 2 <;> funext k <;> fin_cases k <;> rfl

lemma step_reverse_cons (v : Option Bool) (b : Bool) (s : Stacks) :
    machine.step (cfg (some 8) v {s with buffer := b :: s.buffer}) =
      some (cfg (some 8) (some b) {s with output := b :: s.output}) := by
  cases b <;>
    simp [FinTM2.step, TM2.step, TM2.stepAux, program, cfg, Function.update,
      inputStack, outputStack, remainingStack, indexStack, targetStack, tempStack, bufferStack]
    <;> congr 2 <;> funext k <;> fin_cases k <;> rfl

def reverse_runs (xs ys : List Bool) (s : Stacks) (v : Option Bool) :
    EvalsToInTime machine.step (cfg (some 8) v {s with buffer := xs, output := ys})
      (some (cfg none none {s with buffer := [], output := xs.reverse ++ ys}))
      (xs.length + 1) := by
  induction xs generalizing ys v with
  | nil => simpa using one_step (step_reverse_nil v {s with output := ys})
  | cons b xs ih =>
      have hs := step_reverse_cons v b {s with buffer := xs, output := ys}
      have hc := EvalsToInTime.trans machine.step 1 (xs.length + 1) _ _ _
        (one_step hs) (ih (b :: ys) (some b))
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using hc

end QMCBellRuntime



open Turing StateTransition
namespace QMCBellRuntime

def loopStacks (n i r : ℕ) (bs : List Bool) : Stacks :=
  {remaining := List.replicate r true, index := List.replicate i true,
   target := List.replicate (n + i) true, buffer := bs}

def joinSteps {a b : machine.Cfg} {c : Option machine.Cfg} {m n : ℕ}
    (h₁ : EvalsToInTime machine.step a (some b) m)
    (h₂ : EvalsToInTime machine.step b c n) :
    EvalsToInTime machine.step a c (m + n) := by
  simpa [Nat.add_comm] using EvalsToInTime.trans machine.step m n a b c h₁ h₂

def body_runs (n i r : ℕ) (bs : List Bool) (v : Option Bool) :
    EvalsToInTime machine.step (cfg (some 2) v (loopStacks n i (r + 1) bs))
      (some (cfg (some 2) none
        (loopStacks n (i + 1) r ((block n i).reverse ++ bs))))
      (2 * n + 6 * i + 10) := by
  let s₁ := loopStacks n i r (false :: false :: bs)
  let s₂ := {s₁ with buffer := List.replicate i true ++ s₁.buffer}
  let s₃ := {s₂ with buffer := false :: true :: false :: s₂.buffer}
  let s₄ := {s₃ with buffer := List.replicate i true ++ s₃.buffer}
  let s₅ := {s₄ with buffer := false :: s₄.buffer}
  let s₆ := {s₅ with buffer := List.replicate (n + i) true ++ s₅.buffer}
  have h₀ := one_step (step_loop_true v (loopStacks n i r bs))
  have h₁ := copyI9_runs s₁ i rfl rfl (some true)
  have h₂ := one_step (step_afterH none s₂)
  have h₃ := copyI11_runs s₃ i rfl rfl none
  have h₄ := one_step (step_afterControl none s₄)
  have h₅ := copyJ13_runs s₅ (n + i) rfl rfl none
  have h₆ := one_step (step_afterTarget none s₆)
  have hc := joinSteps (joinSteps (joinSteps (joinSteps (joinSteps (joinSteps h₀ h₁) h₂) h₃) h₄) h₅) h₆
  convert hc using 1 <;>
    simp [s₁, s₂, s₃, s₄, s₅, s₆, loopStacks, block, unary,
      List.replicate_succ, List.reverse_append, List.append_assoc,
      Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;>
    simp only [← Nat.add_assoc, List.replicate_succ] <;> omega

def loop_runs (r i n : ℕ) (bs : List Bool) (v : Option Bool) :
    EvalsToInTime machine.step (cfg (some 2) v (loopStacks n i r bs))
      (some (cfg (some 6) none (loopStacks n (i + r) 0
        (((List.range' i r).flatMap (block n)).reverse ++ bs))))
      (r * (2 * n + 6 * (i + r) + 10) + 1) := by
  induction r generalizing i bs v with
  | zero =>
      simpa [loopStacks] using one_step (step_loop_nil v (loopStacks n i 0 bs) rfl)
  | succ r ih =>
      have hb := body_runs n i r bs v
      have hi := ih (i + 1) ((block n i).reverse ++ bs) none
      have hc := joinSteps hb hi
      have hc' : EvalsToInTime machine.step (cfg (some 2) v (loopStacks n i (r + 1) bs))
          (some (cfg (some 6) none (loopStacks n (i + (r + 1)) 0
            (((List.range' i (r + 1)).flatMap (block n)).reverse ++ bs))))
          ((2 * n + 6 * i + 10) +
            (r * (2 * n + 6 * ((i + 1) + r) + 10) + 1)) := by
        simpa [List.range'_succ, List.flatMap_cons, List.reverse_append,
          List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc
      exact weaken hc' (by nlinarith)

lemma map_val_finRange (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp

lemma encode_bellAlgorithm (G : QuantumMaxCut.Input) :
    encodeCircuitUnary (bellAlgorithm G) = bellCode G.n := by
  simp only [encodeCircuitUnary, bellAlgorithm, bellGates, bellCode, Nat.two_mul]
  congr 1
  rw [← map_val_finRange G.n]
  rw [List.flatMap_map]
  simp only [List.flatMap_assoc, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    encodeGateUnary]
  apply congrArg (fun f => (List.finRange G.n).flatMap f)
  funext i
  simp [block, Nat.add_comm, List.append_assoc]

lemma length_flatMap_le {α β : Type} (xs : List α) (f : α → List β) (k : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ k) : (xs.flatMap f).length ≤ xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have hi := ih (fun y hy => h y (by simp [hy]))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      nlinarith

lemma bellCode_length (n : ℕ) : (bellCode n).length ≤ 4 * n ^ 2 + 9 * n + 1 := by
  have h := length_flatMap_le (List.range n) (block n) (4 * n + 7) (by
    intro i hi
    have hi' := List.mem_range.mp hi
    simp only [block, unary, List.length_append, List.length_replicate, List.length_cons,
      List.length_nil]
    omega)
  simp only [List.length_range] at h
  simp only [bellCode, unary, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil]
  nlinarith

end QMCBellRuntime



open Turing StateTransition
noncomputable section
namespace QMCBellRuntime
open QuantumMaxCut

def finalStacks (n : ℕ) : Stacks :=
  {index := List.replicate n true, target := List.replicate (2 * n) true,
   buffer := (bellCode n).reverse}

lemma init_cfg_eq (xs : List Bool) :
    initList machine xs = cfg (some 0) none {input := xs} := by
  simp [initList, cfg, inputStack]
    <;> congr 1 <;> funext k <;> fin_cases k <;> rfl

lemma halt_cfg_eq (ys : List Bool) :
    haltList machine ys = cfg none none {output := ys} := by
  simp [haltList, cfg, outputStack]
    <;> congr 1 <;> funext k <;> fin_cases k <;> rfl

def machine_runs (n : ℕ) (xs : List Bool) :
    TM2OutputsInTime machine (List.replicate n true ++ false :: xs)
      (some (bellCode n)) (100 * (n + xs.length + 2) ^ 2) := by
  let bs := (unary (2 * n)).reverse
  let sp : Stacks := {parsed n [] with buffer := false :: List.replicate (2 * n) true}
  have hp := parse_runs n 0 xs none
  have hd := discard_runs xs sp (some false)
  have hl := loop_runs n 0 n bs none
  have hi := cleanI_runs (List.replicate n true) (finalStacks n) none
  have hj := cleanJ_runs (List.replicate (2 * n) true)
    {finalStacks n with index := []} none
  have hr := reverse_runs (bellCode n).reverse []
    {finalStacks n with index := [], target := []} none
  have hp' : EvalsToInTime machine.step
      (cfg (some 0) none {input := List.replicate n true ++ false :: xs})
      (some (cfg (some 1) (some false) {sp with input := xs})) (n + 1) := by
    simpa [sp, parsed] using hp
  have hd' : EvalsToInTime machine.step (cfg (some 1) (some false) {sp with input := xs})
      (some (cfg (some 2) none (loopStacks n 0 n bs))) (xs.length + 1) := by
    simpa [sp, parsed, loopStacks, bs, unary, List.reverse_append] using hd
  have hl' : EvalsToInTime machine.step (cfg (some 2) none (loopStacks n 0 n bs))
      (some (cfg (some 6) none (finalStacks n))) (n * (8 * n + 10) + 1) := by
    convert hl using 1 <;>
      simp [loopStacks, finalStacks, bs, bellCode, List.reverse_append,
        ← List.range_eq_range', Nat.two_mul] <;> omega
  have hi' : EvalsToInTime machine.step (cfg (some 6) none (finalStacks n))
      (some (cfg (some 7) none {finalStacks n with index := []})) (n + 1) := by
    simpa [finalStacks] using hi
  have hj' : EvalsToInTime machine.step (cfg (some 7) none {finalStacks n with index := []})
      (some (cfg (some 8) none {finalStacks n with index := [], target := []}))
      (2 * n + 1) := by
    simpa [finalStacks] using hj
  have hr' : EvalsToInTime machine.step
      (cfg (some 8) none {finalStacks n with index := [], target := []})
      (some (cfg none none {output := bellCode n})) ((bellCode n).length + 1) := by
    simpa [finalStacks] using hr
  have hc := joinSteps (joinSteps (joinSteps (joinSteps (joinSteps hp' hd') hl') hi') hj') hr'
  have hb := bellCode_length n
  have ht : (n + 1 + (xs.length + 1) + (n * (8 * n + 10) + 1) +
      (n + 1) + (2 * n + 1) + ((bellCode n).length + 1)) ≤
      100 * (n + xs.length + 2) ^ 2 := by
    nlinarith [Nat.zero_le n, Nat.zero_le xs.length, Nat.zero_le (n * xs.length)]
  have hw := weaken hc ht
  simpa [TM2OutputsInTime, init_cfg_eq, halt_cfg_eq] using hw

def inputBody (G : Input) : List Bool :=
  (List.finRange G.n).flatMap (fun i =>
    (List.finRange G.n).flatMap (fun j =>
      if hij : i < j then
        let q := G.weights ⟨(i, j), hij⟩
        encodeNumber q.num ++ encodeNumber q.den
      else []))

lemma input_encoding (G : Input) :
    encodeInput G = List.replicate G.n true ++ false :: inputBody G := by
  simp [encodeInput, inputBody, List.append_assoc]

def bellPolynomial : Polynomial ℕ := 100 * (Polynomial.X + 1) ^ 2

def bell_runtime : Turing.TM2ComputableInPolyTime encodeInput encodeCircuitUnary bellAlgorithm where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := bellPolynomial
  outputsFun G := by
    have h := machine_runs G.n (inputBody G)
    simpa [input_encoding, encode_bellAlgorithm, bellPolynomial, List.length_append,
      List.length_replicate, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_add, Nat.add_assoc] using h


end QMCBellRuntime

namespace QuantumMaxCut

lemma baseline_algorithms_agree :
    QMCBellRuntime.bellAlgorithm = BellBaseline.bellAlgorithm := by
  rfl

theorem quarter_internal_certificate :
    ∃ A : Algorithm, PolynomialTime A ∧ ApproximationRatio A (0.25 : ℝ) := by
  refine ⟨QMCBellRuntime.bellAlgorithm, ?_, ?_⟩
  · unfold PolynomialTime
    refine ⟨?_⟩
    have hgate (n : ℕ) : @encodeGate n = @QMCBellRuntime.encodeGateUnary n := by
      funext gate
      cases gate <;> rfl
    have hcode : encodeCircuit = QMCBellRuntime.encodeCircuitUnary := by
      funext circuit
      simp only [encodeCircuit, QMCBellRuntime.encodeCircuitUnary,
        QMCBellRuntime.unary, hgate]
    rw [hcode]
    exact QMCBellRuntime.bell_runtime
  · rw [baseline_algorithms_agree]
    convert BellBaseline.bellAlgorithm_quarter using 1 <;> norm_num

end QuantumMaxCut


theorem solution :
    ∃ A : QuantumMaxCut.Algorithm,
      QuantumMaxCut.PolynomialTime A ∧
      QuantumMaxCut.ApproximationRatio A (0.25 : ℝ) :=
  QuantumMaxCut.quarter_internal_certificate

#print axioms solution
