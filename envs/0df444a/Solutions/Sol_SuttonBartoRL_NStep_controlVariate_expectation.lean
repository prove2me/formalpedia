-- Prove2me | solution 1 for SuttonBartoRL.NStep.controlVariate_expectation
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T18:29:28.816194+00:00
-- url     : https://prove2.me/submissions/c4f209a6-d968-4668-948a-8cc2f918fdea

import Mathlib
import Definitions.Def_SuttonBartoRL_NStep_MDP
import Definitions.Def_SuttonBartoRL_NStep_Trajectories

open SuttonBartoRL.NStep

section NS
variable {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

theorem nbρ (π b : Policy S A) (hcov : ∀ s a, 0 < π.prob s a → 0 < b.prob s a) (s : S) (a : A) :
    b.prob s a * (π.prob s a / b.prob s a) = π.prob s a := by
  by_cases hb0 : b.prob s a = 0
  · have : π.prob s a = 0 := by
      rcases (π.nonneg s a).lt_or_eq with h | h
      · have := hcov s a h; rw [hb0] at this; exact absurd this (lt_irrefl 0)
      · exact h.symm
    rw [hb0, this]; simp
  · field_simp

theorem segExp_succ (M : MDP S A) (π : Policy S A) (n : ℕ) (s : S)
    (F : Segment M (n+1) → ℝ) :
    segmentExpectation M π (n+1) s F = ∑ x : A × S × M.R,
      π.prob s x.1 * M.p s x.1 x.2.1 (x.2.2 : ℝ) *
        segmentExpectation M π n x.2.1 (fun τ' => F (Fin.cons x τ')) := by
  unfold segmentExpectation
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => A × S × M.R)).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro τ' _
  simp only [Fin.consEquiv, Equiv.coe_fn_mk]
  simp only [segmentProb, Fin.cons_zero, Fin.tail_cons]
  ring

theorem sumX (M : MDP S A) (g : A → S → ℝ → ℝ) :
    ∑ x : A × S × M.R, g x.1 x.2.1 (x.2.2 : ℝ) = ∑ a, ∑ s', ∑ r ∈ M.R, g a s' r := by
  rw [Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro a _
  rw [Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro s' _
  exact Finset.sum_coe_sort M.R (g a s')

theorem segTot (M : MDP S A) (π : Policy S A) :
    ∀ n s, segmentExpectation M π n s (fun _ => 1) = 1 := by
  intro n
  induction n with
  | zero => intro s; simp [segmentExpectation, segmentProb]
  | succ n ih =>
    intro s
    rw [segExp_succ]
    simp only [ih, mul_one]
    have := sumX M (fun a s' r => π.prob s a * M.p s a s' r)
    try simp only at this
    rw [this]
    simp_rw [← Finset.mul_sum, M.p_sum, mul_one, π.sum_one]

theorem segLin (M : MDP S A) (π : Policy S A) (n : ℕ) (s : S) (f : Segment M n → ℝ)
    (c1 c2 : ℝ) : segmentExpectation M π n s (fun τ => c1 * f τ + c2) =
      c1 * segmentExpectation M π n s f + c2 := by
  have h := segTot M π n s
  unfold segmentExpectation at *
  calc ∑ τ, segmentProb M π n s τ * (c1 * f τ + c2)
      = ∑ τ, (c1 * (segmentProb M π n s τ * f τ) + c2 * (segmentProb M π n s τ * 1)) :=
        Finset.sum_congr rfl fun τ _ => by ring
    _ = c1 * ∑ τ, segmentProb M π n s τ * f τ + c2 * ∑ τ, segmentProb M π n s τ * 1 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = _ := by rw [h]; ring

theorem lin1 (M : MDP S A) (π : Policy S A) (n : ℕ) (s : S) (f : Segment M n → ℝ)
    (a r g c : ℝ) : segmentExpectation M π n s (fun τ => a * (r + g * f τ) + c) =
      a * (r + g * segmentExpectation M π n s f) + c := by
  rw [show (fun τ => a * (r + g * f τ) + c) = (fun τ => (a * g) * f τ + (a * r + c)) from
    funext fun τ => by ring, segLin]
  ring

theorem lin2 (M : MDP S A) (π : Policy S A) (n : ℕ) (s : S) (f : Segment M n → ℝ)
    (a r g : ℝ) : segmentExpectation M π n s (fun τ => a * (r + g * f τ)) =
      a * (r + g * segmentExpectation M π n s f) := by
  rw [show (fun τ => a * (r + g * f τ)) = (fun τ => (a * g) * f τ + (a * r)) from
    funext fun τ => by ring, segLin]
  ring

theorem lin3 (M : MDP S A) (π : Policy S A) (n : ℕ) (s : S) (f : Segment M n → ℝ)
    (r g : ℝ) : segmentExpectation M π n s (fun τ => r + g * f τ) =
      r + g * segmentExpectation M π n s f := by
  rw [show (fun τ => r + g * f τ) = (fun τ => g * f τ + r) from
    funext fun τ => by ring, segLin]
  ring

theorem segStates_cons (M : MDP S A) {n : ℕ} (s : S) (x : A × S × M.R) (τ' : Segment M n)
    (j : Fin (n+1)) :
    segmentStates M s (Fin.cons x τ' : Segment M (n+1)) j.succ = segmentStates M x.2.1 τ' j := by
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [segmentStates]
  · simp [segmentStates]

theorem nstep_cons (M : MDP S A) (γ : ℝ) (V : S → ℝ) {n : ℕ} (s : S) (x : A × S × M.R)
    (τ' : Segment M n) :
    nStepReturnOn M γ V s (Fin.cons x τ' : Segment M (n+1)) =
      (x.2.2 : ℝ) + γ * nStepReturnOn M γ V x.2.1 τ' := by
  unfold nStepReturnOn
  rw [Fin.sum_univ_succ, ← Fin.succ_last, segStates_cons]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, one_mul, Fin.val_succ]
  have e : ∀ k : Fin n, γ ^ ((k : ℕ) + 1) * ((τ' k).2.2 : ℝ) = γ * (γ ^ (k : ℕ) * (τ' k).2.2) :=
    fun k => by ring
  simp only [e, ← Finset.mul_sum]
  ring

theorem cv_main (M : MDP S A) (π b : Policy S A) (hcov : ∀ s a, 0 < π.prob s a → 0 < b.prob s a)
    (γ : ℝ) (V : S → ℝ) : ∀ n s,
    segmentExpectation M b n s (controlVariateReturnOn M π b γ V n s) =
      expectedNStepReturn M π γ V n s ∧
    segmentExpectation M b n s (perDecisionReturnOn M π b γ V n s) =
      expectedNStepReturn M π γ V n s := by
  intro n
  induction n with
  | zero =>
    intro s
    have h := segTot M b 0 s
    have h' := segTot M π 0 s
    unfold segmentExpectation at h h'
    simp only [expectedNStepReturn, segmentExpectation, controlVariateReturnOn,
      perDecisionReturnOn, nStepReturnOn]
    simp [segmentProb, segmentStates]
  | succ n ih =>
    intro s
    unfold expectedNStepReturn
    rw [segExp_succ, segExp_succ, segExp_succ]
    simp only [controlVariateReturnOn, perDecisionReturnOn, nstep_cons, Fin.cons_zero,
      Fin.tail_cons, lin1, lin2, lin3, fun s => (ih s).1, fun s => (ih s).2]
    unfold expectedNStepReturn
    set H : S → ℝ → ℝ := fun s' r => r + γ * segmentExpectation M π n s' (nStepReturnOn M γ V s')
    have hb : ∀ x : A × S × M.R, b.prob s x.1 * (π.prob s x.1 / b.prob s x.1) = π.prob s x.1 :=
      fun x => nbρ π b hcov s x.1
    have hz : ∑ x : A × S × M.R, (b.prob s x.1 - π.prob s x.1) * M.p s x.1 x.2.1 (x.2.2 : ℝ) *
        V s = 0 := by
      have := sumX M (fun a s' r => (b.prob s a - π.prob s a) * M.p s a s' r * V s)
      try simp only at this
      rw [this]
      have e : ∀ a, ∑ s', ∑ r ∈ M.R, (b.prob s a - π.prob s a) * M.p s a s' r * V s =
          (b.prob s a - π.prob s a) * V s := by
        intro a
        rw [show (∑ s', ∑ r ∈ M.R, (b.prob s a - π.prob s a) * M.p s a s' r * V s) =
          ((b.prob s a - π.prob s a) * V s) * ∑ s', ∑ r ∈ M.R, M.p s a s' r by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s' _
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro r _; ring]
        rw [M.p_sum, mul_one]
      simp_rw [e]
      rw [← Finset.sum_mul, Finset.sum_sub_distrib, b.sum_one, π.sum_one]; ring
    constructor
    · calc _ = ∑ x : A × S × M.R, (π.prob s x.1 * M.p s x.1 x.2.1 (x.2.2 : ℝ) * H x.2.1 x.2.2 +
            (b.prob s x.1 - π.prob s x.1) * M.p s x.1 x.2.1 (x.2.2 : ℝ) * V s) := by
            apply Finset.sum_congr rfl; intro x _
            simp only [H]
            linear_combination (M.p s x.1 x.2.1 (x.2.2 : ℝ) * (x.2.2 + γ *
              segmentExpectation M π n x.2.1 (nStepReturnOn M γ V x.2.1)) -
              M.p s x.1 x.2.1 (x.2.2 : ℝ) * V s) * hb x
        _ = _ := by
            rw [Finset.sum_add_distrib, hz, add_zero]
    · apply Finset.sum_congr rfl; intro x _
      linear_combination (M.p s x.1 x.2.1 (x.2.2 : ℝ) * (x.2.2 + γ *
        segmentExpectation M π n x.2.1 (nStepReturnOn M γ V x.2.1))) * hb x
end NS

theorem solution {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A]
    (M : MDP S A) (π b : Policy S A) (hcov : ∀ s a, 0 < π.prob s a → 0 < b.prob s a)
    (γ : ℝ) (V : S → ℝ) (n : ℕ) (s : S) :
    segmentExpectation M b n s (controlVariateReturnOn M π b γ V n s) =
        segmentExpectation M b n s (perDecisionReturnOn M π b γ V n s) ∧
      segmentExpectation M b n s (controlVariateReturnOn M π b γ V n s) =
        expectedNStepReturn M π γ V n s := by
  obtain ⟨h1, h2⟩ := cv_main M π b hcov γ V n s
  exact ⟨h1.trans h2.symm, h1⟩
