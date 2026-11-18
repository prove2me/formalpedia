-- Prove2me | solution 1 for OWMR.fifo_running_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-17T20:48:09.778195+00:00
-- url     : https://prove2.me/submissions/000f38a9-b041-401d-9e76-c494e6cbdafb

import Theorems.Thm_OWMR_fifo_engine_invariants
import Theorems.Thm_OWMR_F_properties

/-!
Lemma 8 (FIFO Holding and Backlog Cost Bound). In every period after the initialization, the
retailer positions including outstanding requests `P̂_i` (pinned down by the request rule, as in
`fifo_engine_invariants`) dominate the physical positions `P_i`, the warehouse stock `W` is
nonnegative, and `W ∑_i (P̂_i - P_i) = 0` (exhaustive service), by the queue invariants. With
`Δ = ∑_i (P̂_i - P_i)`, the slope bound of `F_i` gives `F_i(P_i) ≤ F_i(P̂_i) + p (P̂_i - P_i)`,
`h W + p Δ = φ(W - Δ)`, the mirror identity `W - Δ = E + ∑_i (a_i - P̂_i)` holds, and `φ` is
subadditive.
-/

open MeasureTheory
open scoped ENNReal NNReal
open OWMR

namespace L8

lemma whLoss_add (h p a b : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) :
    whLoss h p (a + b) ≤ whLoss h p a + whLoss h p b := by
  unfold whLoss
  have k1 : max (a + b) 0 ≤ max a 0 + max b 0 :=
    max_le (add_le_add (le_max_left _ _) (le_max_left _ _))
      (add_nonneg (le_max_right _ _) (le_max_right _ _))
  have k2 : max (-(a + b)) 0 ≤ max (-a) 0 + max (-b) 0 :=
    max_le (by linarith [le_max_left (-a) 0, le_max_left (-b) 0])
      (add_nonneg (le_max_right _ _) (le_max_right _ _))
  have := mul_le_mul_of_nonneg_left k1 hh
  have := mul_le_mul_of_nonneg_left k2 hp
  linarith

lemma whLoss_sum {ι : Type} (s : Finset ι) (h p : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p)
    (a : ι → ℝ) : whLoss h p (∑ i ∈ s, a i) ≤ ∑ i ∈ s, whLoss h p (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [whLoss]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (whLoss_add h p _ _ hh hp).trans (add_le_add le_rfl ih)

/-- The algebraic core of Lemma 8. -/
lemma core {n : ℕ} (h p : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) (F : Fin n → ℝ → ℝ)
    (hF : ∀ i y y', y ≤ y' → F i y - p * (y' - y) ≤ F i y')
    (W : ℝ) (hW : 0 ≤ W) (P Ph a : Fin n → ℝ) (hP : ∀ i, P i ≤ Ph i)
    (hWΔ : W * ∑ i, (Ph i - P i) = 0) :
    h * W + ∑ i, F i (P i)
      ≤ whLoss h p (W + ∑ i, (P i - a i)) + ∑ i, (F i (Ph i) + whLoss h p (a i - Ph i)) := by
  set D := ∑ i, (Ph i - P i) with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun i _ => by linarith [hP i]
  have h1 : ∀ i, F i (P i) ≤ F i (Ph i) + p * (Ph i - P i) := fun i => by
    have := hF i (P i) (Ph i) (hP i)
    linarith
  have h2 : h * W + p * D = whLoss h p (W - D) := by
    unfold whLoss
    rcases eq_or_lt_of_le hD0 with hz | hz
    · rw [← hz]
      simp only [mul_zero, add_zero, sub_zero, max_eq_left hW, max_eq_right (neg_nonpos.2 hW)]
    · have hW0 : W = 0 := by
        rcases mul_eq_zero.1 hWΔ with h' | h'
        · exact h'
        · exact absurd h' hz.ne'
      rw [hW0, zero_sub, mul_zero, zero_add, max_eq_right (by linarith), mul_zero, zero_add,
        neg_neg, max_eq_left hD0]
  have h3 : W - D = (W + ∑ i, (P i - a i)) + ∑ i, (a i - Ph i) := by
    have e : ∑ i, (P i - a i) + ∑ i, (a i - Ph i) = -D := by
      rw [← Finset.sum_add_distrib, hD, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    linarith
  have h4 := whLoss_add h p (W + ∑ i, (P i - a i)) (∑ i, (a i - Ph i)) hh hp
  have h5 := whLoss_sum Finset.univ h p hh hp (fun i => a i - Ph i)
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h1 i
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [Finset.sum_add_distrib]
  rw [h3] at h2
  linarith

end L8

open L8 in
theorem solution {n : ℕ} (N : Network n) (hN : N.Standing) (x : InitState n)
    (hx : x.Valid) (c : FIFOChoice n) (hc : IsFIFOChoice N c)
    (d : ℕ → DemandVec n) (act : ℕ → Prop) [DecidablePred act]
    (hact : ∀ t, act t ↔ (N.Tpipe ≤ t + 1 ∧ ∀ i, x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
      - ∑ s ∈ Finset.range t, ((d s i : ℝ≥0) : ℝ) ≤ c.S i))
    (Ph : ℕ → Fin n → ℝ)
    (hPh0 : ∀ i, Ph 0 i = if act 0 then c.S i else x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s)
    (hPh : ∀ t i, Ph (t + 1) i = if act (t + 1) then
        (if act t then (if Ph t i - ((d t i : ℝ≥0) : ℝ) ≤ c.s i then c.S i
          else Ph t i - ((d t i : ℝ≥0) : ℝ)) else c.S i)
      else x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
        - ∑ s ∈ Finset.range (t + 1), ((d s i : ℝ≥0) : ℝ))
    (t : ℕ) (ht : act t) :
    let W := Policy.whStock N x (fifoPolicy N x c).toPolicy () d t
    let P : Fin n → ℝ := fun i => x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s
      + ∑ r ∈ Finset.range (t + 1), (fifoPolicy N x c).toPolicy.dispatch r () d i
      - ∑ r ∈ Finset.range t, ((d r i : ℝ≥0) : ℝ)
    let E := W + ∑ i, (P i - c.a i)
    N.h * W + ∑ i, N.F i (P i)
      ≤ whLoss N.h N.p E + ∑ i, (N.F i (Ph t i) + whLoss N.h N.p (c.a i - Ph t i)) := by
  intro W P E
  -- Definition 1 uses `s_i ≤ S_i` and `s₀ ≤ S₀`
  have hsS : ∀ i, c.s i ≤ c.S i := by
    intro i
    rcases (hN.K_nonneg i).lt_or_eq with hK | hK
    · obtain ⟨sh, Sh, s', S', hcan, hhalf, hsel, -⟩ := hc.1 i hK
      rcases hsel with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
      · rw [h1, h2]; exact hcan.1.le
      · rw [h1, h2]; exact hhalf.2.1.le
    · exact (hc.2.1 i hK.symm).1.le
  have hs0 : c.s0 ≤ c.S0 := hc.2.2.1
  -- the supplier position (the solution of its recursion)
  let Yp : ℕ → ℝ := fun t => Nat.rec (motive := fun _ => ℝ)
    (x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
      + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i))
    (fun t y => (if act t ∧ y ≤ c.s0 then c.S0 else y) - ∑ i, ((d t i : ℝ≥0) : ℝ)) t
  have hY0 : Yp 0 = x.W + ∑ s ∈ Finset.range N.L0, x.supPipe s
      + ∑ i, (x.I i + ∑ s ∈ Finset.range (N.L i), x.retPipe i s - c.a i) := rfl
  have hY : ∀ t, Yp (t + 1) = (if act t ∧ Yp t ≤ c.s0 then c.S0 else Yp t)
      - ∑ i, ((d t i : ℝ≥0) : ℝ) := fun t => rfl
  obtain ⟨-, hW0, hPle, hWΔ, -⟩ :=
    fifo_engine_invariants N hN x hx c hsS hs0 d act hact Yp hY0 hY Ph hPh0 hPh
  have hF : ∀ i y y', y ≤ y' → N.F i y - N.p * (y' - y) ≤ N.F i y' := fun i =>
    (F_properties N hN i).2.2.2
  exact core N.h N.p hN.h_pos.le hN.p_pos.le N.F hF W (hW0 t) P (Ph t) c.a (fun i => hPle t i)
    (hWΔ t)
