-- Prove2me | solution 1 for UnderstandingML.backprop_gradient
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T12:55:18.143475+00:00
-- url     : https://prove2.me/submissions/64bd84ab-53b4-442d-b1cb-a9983f3ec7bd

import Definitions.Def_UnderstandingML_NeuralNetworks
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

open MeasureTheory

namespace UnderstandingML

/-- Forward-mode derivative of `o_{r,k}` with respect to the weight `w t i j`. -/
noncomputable def fwdD (σ : ℝ → ℝ) (G : LayeredGraph) (w : ℕ → ℕ → ℕ → ℝ) (x : ℕ → ℝ)
    (t i j : ℕ) : ℕ → ℕ → ℝ
  | 0 => fun _ => 0
  | r + 1 => fun k => deriv σ (netInput σ G w x r k) *
      (∑ l ∈ Finset.range (G.width r), (if (k, l) ∈ G.edges r then w r k l else 0) *
          fwdD σ G w x t i j r l +
        (if r = t ∧ k = i then netOutput σ G w x t j else 0))

lemma updateWeight_self (w : ℕ → ℕ → ℕ → ℝ) (t i j : ℕ) : updateWeight w t i j (w t i j) = w := by
  funext t' i' j'
  unfold updateWeight
  split_ifs with h
  · obtain ⟨rfl, rfl, rfl⟩ := h; rfl
  · rfl

lemma fwdD_eq_zero (σ : ℝ → ℝ) (G : LayeredGraph) (w : ℕ → ℕ → ℕ → ℝ) (x : ℕ → ℝ)
    (t i j : ℕ) : ∀ r, r ≤ t → ∀ k, fwdD σ G w x t i j r k = 0 := by
  intro r
  induction r with
  | zero => intro _ _; rfl
  | succ r ih =>
    intro hr k
    have hr' : r ≤ t := by omega
    have hne : r ≠ t := by omega
    simp [fwdD, ih hr', hne]

lemma hasDerivAt_netOutput (σ : ℝ → ℝ) (hσ : Differentiable ℝ σ) (G : LayeredGraph)
    (w : ℕ → ℕ → ℕ → ℝ) (x : ℕ → ℝ) (t i j : ℕ) (he : (i, j) ∈ G.edges t) :
    ∀ r k, HasDerivAt (fun s ↦ netOutput σ G (updateWeight w t i j s) x r k)
      (fwdD σ G w x t i j r k) (w t i j) := by
  intro r
  induction r with
  | zero => intro k; exact hasDerivAt_const _ _
  | succ r ih =>
    intro k
    -- derivative of each coefficient
    have hc : ∀ l, HasDerivAt
        (fun s ↦ if (k, l) ∈ G.edges r then updateWeight w t i j s r k l else 0)
        (if (k, l) ∈ G.edges r ∧ r = t ∧ k = i ∧ l = j then 1 else 0) (w t i j) := by
      intro l
      by_cases hkl : (k, l) ∈ G.edges r
      · by_cases h : r = t ∧ k = i ∧ l = j
        · obtain ⟨rfl, rfl, rfl⟩ := h
          simp only [hkl, and_self, if_true, updateWeight]
          exact hasDerivAt_id' _
        · simp only [hkl, h, if_true, and_false, if_false, updateWeight]
          exact hasDerivAt_const _ _
      · simp only [hkl, if_false, false_and]
        exact hasDerivAt_const _ _
    have hin : HasDerivAt
        (fun s ↦ ∑ l ∈ Finset.range (G.width r),
          (if (k, l) ∈ G.edges r then updateWeight w t i j s r k l else 0) *
            netOutput σ G (updateWeight w t i j s) x r l)
        (∑ l ∈ Finset.range (G.width r),
          ((if (k, l) ∈ G.edges r ∧ r = t ∧ k = i ∧ l = j then 1 else 0) *
              netOutput σ G (updateWeight w t i j (w t i j)) x r l +
            (if (k, l) ∈ G.edges r then updateWeight w t i j (w t i j) r k l else 0) *
              fwdD σ G w x t i j r l)) (w t i j) := by
      apply HasDerivAt.fun_sum
      intro l _
      exact (hc l).mul (ih l)
    have hout := ((hσ _).hasDerivAt).comp (w t i j) hin
    show HasDerivAt (fun s ↦ σ (∑ l ∈ Finset.range (G.width r),
          (if (k, l) ∈ G.edges r then updateWeight w t i j s r k l else 0) *
            netOutput σ G (updateWeight w t i j s) x r l)) _ _
    refine hout.congr_deriv ?_
    rw [updateWeight_self]
    simp only [fwdD, netInput]
    congr 1
    rw [Finset.sum_add_distrib, add_comm]
    congr 1
    by_cases h : r = t ∧ k = i
    · obtain ⟨rfl, rfl⟩ := h
      have hj : j ∈ Finset.range (G.width r) :=
        Finset.mem_range.mpr (G.edges_valid r _ he).2
      rw [Finset.sum_eq_single_of_mem j hj]
      · simp [he]
      · intro l _ hl
        simp [hl]
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro l _
      have : ¬ ((k, l) ∈ G.edges r ∧ r = t ∧ k = i ∧ l = j) := fun h' => h ⟨h'.2.1, h'.2.2.1⟩
      simp [this]

lemma backprop_sum_invariant (σ : ℝ → ℝ) (G : LayeredGraph)
    (w : ℕ → ℕ → ℕ → ℝ) (x y : ℕ → ℝ) (t i j : ℕ) (he : (i, j) ∈ G.edges t) :
    ∀ r, t + 1 ≤ r → r ≤ G.depth →
      ∑ k ∈ Finset.range (G.width r), backDelta σ G w x y r k * fwdD σ G w x t i j r k =
      backDelta σ G w x y (t + 1) i * deriv σ (netInput σ G w x t i) * netOutput σ G w x t j := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
    intro _
    have hi : i ∈ Finset.range (G.width (t + 1)) :=
      Finset.mem_range.mpr (G.edges_valid t _ he).1
    rw [Finset.sum_eq_single_of_mem i hi]
    · simp [fwdD, fwdD_eq_zero σ G w x t i j t le_rfl]
      ring
    · intro k _ hk
      simp [fwdD, fwdD_eq_zero σ G w x t i j t le_rfl, hk]
  | succ r hr ih =>
    intro hrT
    rw [← ih (by omega)]
    have hδ : ∀ l, backDelta σ G w x y r l = ∑ k ∈ Finset.range (G.width (r + 1)),
        (if (k, l) ∈ G.edges r then w r k l else 0) * backDelta σ G w x y (r + 1) k *
          deriv σ (netInput σ G w x r k) := by
      intro l
      unfold backDelta
      obtain ⟨s, hs⟩ : ∃ s, G.depth - r = s + 1 := ⟨G.depth - r - 1, by omega⟩
      rw [hs]
      simp only [backDeltaAux]
      have h1 : G.depth - s = r + 1 := by omega
      have h2 : G.depth - s - 1 = r := by omega
      have h3 : G.depth - (r + 1) = s := by omega
      rw [h1, h3, Nat.add_sub_cancel]
    have hrt : r ≠ t := by omega
    simp only [fwdD, hrt, false_and, if_false, add_zero]
    simp_rw [hδ, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ => ?_))
    ring

theorem backprop_gradient_aux (σ : ℝ → ℝ) (hσ : Differentiable ℝ σ) (G : LayeredGraph)
    (w : ℕ → ℕ → ℕ → ℝ) (x y : ℕ → ℝ) (t i j : ℕ) (ht : t < G.depth) (he : (i, j) ∈ G.edges t) :
    HasDerivAt (fun s ↦ netLoss σ G (updateWeight w t i j s) x y)
      (backDelta σ G w x y (t + 1) i * deriv σ (netInput σ G w x t i) * netOutput σ G w x t j)
      (w t i j) := by
  have hsum := backprop_sum_invariant σ G w x y t i j he G.depth (by omega) le_rfl
  rw [← hsum]
  unfold netLoss
  have hd : HasDerivAt (fun s ↦ (1 / 2 : ℝ) * ∑ k ∈ Finset.range (G.width G.depth),
      (netOutput σ G (updateWeight w t i j s) x G.depth k - y k) ^ 2)
      ((1 / 2 : ℝ) * ∑ k ∈ Finset.range (G.width G.depth),
        (2 : ℝ) * (netOutput σ G (updateWeight w t i j (w t i j)) x G.depth k - y k) ^ 1 *
          fwdD σ G w x t i j G.depth k) (w t i j) := by
    apply HasDerivAt.const_mul
    apply HasDerivAt.fun_sum
    intro k _
    exact ((hasDerivAt_netOutput σ hσ G w x t i j he G.depth k).sub_const (y k)).pow 2
  refine hd.congr_deriv ?_
  rw [updateWeight_self, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [backDelta, Nat.sub_self, backDeltaAux]
  ring

end UnderstandingML

open UnderstandingML in
theorem solution (σ : ℝ → ℝ) (hσ : Differentiable ℝ σ) (G : LayeredGraph)
    (w : ℕ → ℕ → ℕ → ℝ) (x y : ℕ → ℝ) (t i j : ℕ) (ht : t < G.depth) (he : (i, j) ∈ G.edges t) :
    HasDerivAt (fun s ↦ netLoss σ G (updateWeight w t i j s) x y)
      (backDelta σ G w x y (t + 1) i * deriv σ (netInput σ G w x t i) * netOutput σ G w x t j)
      (w t i j) :=
  backprop_gradient_aux σ hσ G w x y t i j ht he
