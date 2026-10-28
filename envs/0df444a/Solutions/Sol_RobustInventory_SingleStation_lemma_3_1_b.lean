-- Prove2me | solution 1 for RobustInventory.SingleStation.lemma_3_1_b
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:24:00.12065+00:00
-- url     : https://prove2.me/submissions/06739c3a-fad3-4741-b5ab-340b35061b7e

import Mathlib
import Definitions.Def_RobustInventory_SingleStation_Deviation
import Definitions.Def_RobustInventory_SingleStation_Robust

-- carved verbatim out of submission 22bfc764-f2d6-45b5-9153-7576bb19ecce, lines 367-429

section
set_option autoImplicit false

open RobustInventory.SingleStation in
theorem RI32_stock_step (x0 : ℝ) (w : ℕ → ℝ) (k : ℕ) :
    orderUpToStock x0 w w (k+1) = orderUpToStock x0 w w k + orderUpTo x0 w w k - w k := by
  show max (orderUpToStock x0 w w k) (w k) - w k
    = orderUpToStock x0 w w k + max (w k - orderUpToStock x0 w w k) 0 - w k
  rcases le_total (orderUpToStock x0 w w k) (w k) with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

open RobustInventory.SingleStation in
theorem RI32_stock_eq (M : Model) (w : ℕ → ℝ) (k : ℕ) :
    M.stock w (orderUpTo M.x0 w w) k = orderUpToStock M.x0 w w (k+1) := by
  induction k with
  | zero =>
    rw [RI32_stock_step]
    simp only [Model.stock, zero_add, Finset.sum_range_one, orderUpToStock]
    ring
  | succ n ih =>
    rw [RI32_stock_step]
    simp only [Model.stock] at ih ⊢
    rw [Finset.sum_range_succ, ← add_assoc, ih]
    ring

theorem RI32_maxsub (a b : ℝ) : max a b - b = max (a - b) 0 := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (by linarith)]; ring
  · rw [max_eq_left h, max_eq_left (by linarith)]

open RobustInventory.SingleStation Finset in
theorem RI32_stock_closed (M : Model) (w : ℕ → ℝ) (hw : ∀ k < M.T, 0 ≤ w k) :
    ∀ k < M.T, orderUpToStock M.x0 w w (k+1) = max (M.x0 - ∑ i ∈ range (k+1), w i) 0 := by
  intro k
  induction k with
  | zero =>
    intro _
    show max M.x0 (w 0) - w 0 = max (M.x0 - ∑ i ∈ range (0+1), w i) 0
    rw [RI32_maxsub, zero_add, Finset.sum_range_one]
  | succ n ih =>
    intro hn
    have hw' := hw (n+1) hn
    have ih' := ih (by omega)
    show max (orderUpToStock M.x0 w w (n+1)) (w (n+1)) - w (n+1)
      = max (M.x0 - ∑ i ∈ range (n+1+1), w i) 0
    rw [RI32_maxsub, ih', Finset.sum_range_succ _ (n+1)]
    rcases le_total (M.x0 - ∑ i ∈ range (n+1), w i) 0 with h | h
    · rw [max_eq_right h, max_eq_right (by linarith), max_eq_right (by linarith)]
    · rw [max_eq_left h, sub_add_eq_sub_sub]

theorem RI32_R_bounds (h p a s : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) (hs : 0 ≤ s) :
    max (h * max a 0) (-(p * max a 0)) ≤ max (h * (a + s)) (-(p * (a + s))) ∧
    max (h * max a 0) (-(p * max a 0)) + p * (max a 0 - (a + s))
      ≤ max (h * (a + s)) (-(p * (a + s))) := by
  rcases le_or_gt a 0 with ha | ha
  · rw [max_eq_right ha]
    have e : max (h * 0) (-(p * 0)) = 0 := by simp
    rw [e]
    constructor
    · rcases le_or_gt 0 (a+s) with h1 | h1
      · exact le_trans (mul_nonneg hh h1) (le_max_left _ _)
      · exact le_trans (by nlinarith) (le_max_right _ _)
    · exact le_trans (le_of_eq (by ring)) (le_max_right _ _)
  · rw [max_eq_left ha.le]
    have h1 : max (h * a) (-(p * a)) = h * a := max_eq_left (by nlinarith)
    rw [h1]
    constructor
    · exact le_trans (by nlinarith) (le_max_left _ _)
    · exact le_trans (by nlinarith) (le_max_left _ _)

open RobustInventory.SingleStation Finset in
theorem solution (M : Model) (hK : M.K = 0) (w : ℕ → ℝ) (hw : ∀ k < M.T, 0 ≤ w k) :
    M.IsNominalOptimal w (orderUpTo M.x0 w w) := by
  have hC : ∀ v : ℝ, 0 ≤ v → M.C v = M.c * v := by
    intro v hv
    unfold Model.C
    split_ifs with h
    · rw [hK, zero_add]
    · have : v = 0 := le_antisymm (not_lt.mp h) hv
      rw [this, mul_zero]
  have hustar : ∀ k, 0 ≤ orderUpTo M.x0 w w k := fun k => le_max_right _ _
  refine ⟨fun k _ => hustar k, ?_⟩
  intro u' hu'
  have hp : 0 ≤ M.p := by linarith [M.hc, M.hpc]
  have hb : ∀ k < M.T, M.R (M.stock w (orderUpTo M.x0 w w) k) ≤ M.R (M.stock w u' k) ∧
      M.R (M.stock w (orderUpTo M.x0 w w) k)
        + M.p * (M.stock w (orderUpTo M.x0 w w) k - M.stock w u' k) ≤ M.R (M.stock w u' k) := by
    intro k hk
    have e1 : M.stock w (orderUpTo M.x0 w w) k = max (M.x0 - ∑ i ∈ range (k+1), w i) 0 := by
      rw [RI32_stock_eq, RI32_stock_closed M w hw k hk]
    have hs : 0 ≤ ∑ i ∈ range (k+1), u' i :=
      Finset.sum_nonneg (fun i hi => hu' i (by have := Finset.mem_range.mp hi; omega))
    have e2 : M.stock w u' k = (M.x0 - ∑ i ∈ range (k+1), w i) + ∑ i ∈ range (k+1), u' i := by
      simp only [Model.stock, Finset.sum_sub_distrib]; ring
    rw [e1, e2]
    simp only [Model.R]
    exact RI32_R_bounds M.h M.p _ _ M.hh hp hs
  unfold Model.nominalCost
  rcases Nat.eq_zero_or_pos M.T with hT | hT
  · rw [hT]; simp
  obtain ⟨n, hn⟩ : ∃ n, M.T = n + 1 := ⟨M.T - 1, by omega⟩
  have hsum : ∀ v : ℕ → ℝ, (∀ k < M.T, 0 ≤ v k) →
      ∑ k ∈ range M.T, (M.C (v k) + M.R (M.stock w v k)) =
        M.c * ∑ k ∈ range M.T, v k + ∑ k ∈ range M.T, M.R (M.stock w v k) := by
    intro v hv
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hC (v k) (hv k (Finset.mem_range.mp hk))]
  rw [hsum _ (fun k _ => hustar k), hsum u' hu']
  have hdiff : ∑ k ∈ range M.T, u' k - ∑ k ∈ range M.T, orderUpTo M.x0 w w k
      = M.stock w u' n - M.stock w (orderUpTo M.x0 w w) n := by
    simp only [Model.stock, Finset.sum_sub_distrib]; rw [hn]; ring
  have hcd : M.c * ∑ k ∈ range M.T, u' k - M.c * ∑ k ∈ range M.T, orderUpTo M.x0 w w k
      = M.c * (M.stock w u' n - M.stock w (orderUpTo M.x0 w w) n) := by
    rw [← hdiff]; ring
  have hR : ∑ k ∈ range M.T, M.R (M.stock w (orderUpTo M.x0 w w) k)
      + (M.R (M.stock w u' n) - M.R (M.stock w (orderUpTo M.x0 w w) n))
      ≤ ∑ k ∈ range M.T, M.R (M.stock w u' k) := by
    rw [hn, Finset.sum_range_succ, Finset.sum_range_succ]
    have : ∑ k ∈ range n, M.R (M.stock w (orderUpTo M.x0 w w) k)
        ≤ ∑ k ∈ range n, M.R (M.stock w u' k) :=
      Finset.sum_le_sum (fun k hk => (hb k (by have := Finset.mem_range.mp hk; omega)).1)
    linarith
  obtain ⟨hfirst, hlast⟩ := hb n (by omega)
  have hc := M.hc
  have hpc := M.hpc
  rcases le_total (M.stock w (orderUpTo M.x0 w w) n) (M.stock w u' n) with h | h
  · nlinarith [mul_nonneg hc.le (sub_nonneg.mpr h)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hpc.le) (sub_nonneg.mpr h)]

end
