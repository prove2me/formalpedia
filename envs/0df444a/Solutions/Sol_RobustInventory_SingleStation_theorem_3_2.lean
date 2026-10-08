-- Prove2me | solution 1 for RobustInventory.SingleStation.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T03:36:44.778169+00:00
-- url     : https://prove2.me/submissions/22bfc764-f2d6-45b5-9153-7576bb19ecce

import Mathlib
import Definitions.Def_RobustInventory_SingleStation_Deviation
import Definitions.Def_RobustInventory_SingleStation_Robust

set_option autoImplicit false

/-! ### Generic LP lemmas for the budget LP (13) -/

open Finset in
theorem RI32_weak (n : ℕ) (a z r : ℕ → ℝ) (q G : ℝ)
    (hz : ∀ i < n, 0 ≤ z i ∧ z i ≤ 1) (hzs : ∑ i ∈ range n, z i ≤ G)
    (hq : 0 ≤ q) (hr : ∀ i < n, 0 ≤ r i ∧ a i ≤ q + r i) :
    ∑ i ∈ range n, a i * z i ≤ q * G + ∑ i ∈ range n, r i := by
  have h1 : ∑ i ∈ range n, a i * z i ≤ ∑ i ∈ range n, (q * z i + r i) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' := Finset.mem_range.mp hi
    obtain ⟨hz0, hz1⟩ := hz i hi'
    obtain ⟨hr0, hra⟩ := hr i hi'
    nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hra), mul_nonneg hr0 (sub_nonneg.mpr hz1)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h1
  nlinarith [mul_le_mul_of_nonneg_left hzs hq]

open Finset in
theorem RI32_strong (n : ℕ) (a : ℕ → ℝ) (G : ℝ) (ha : ∀ i, 0 ≤ a i) (hG : 0 ≤ G) :
    ∃ q : ℝ, 0 ≤ q ∧ ∃ z : ℕ → ℝ, (∀ i < n, 0 ≤ z i ∧ z i ≤ 1) ∧ ∑ i ∈ range n, z i ≤ G ∧
      q * G + ∑ i ∈ range n, max (a i - q) 0 ≤ ∑ i ∈ range n, a i * z i := by
  classical
  set S : Finset ℝ := insert 0 ((range n).image a) with hS
  have hS0 : ∀ s ∈ S, 0 ≤ s := by
    intro s hs
    rw [hS, Finset.mem_insert, Finset.mem_image] at hs
    rcases hs with h | ⟨i, _, rfl⟩
    · rw [h]
    · exact ha i
  have haS : ∀ i, i < n → a i ∈ S := fun i hi =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem a (Finset.mem_range.mpr hi))
  set cnt : ℝ → ℝ := fun q => ∑ i ∈ range n, (if q < a i then (1:ℝ) else 0) with hcnt
  set Cs := S.filter (fun q => cnt q ≤ G) with hCs
  have hSne : S.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  have hmaxC : S.max' hSne ∈ Cs := by
    rw [hCs, Finset.mem_filter]
    refine ⟨Finset.max'_mem _ _, ?_⟩
    have h0 : cnt (S.max' hSne) = 0 := by
      rw [hcnt]
      apply Finset.sum_eq_zero
      intro i hi
      have h2 : a i ≤ S.max' hSne := Finset.le_max' _ _ (haS i (Finset.mem_range.mp hi))
      simp [not_lt.mpr h2]
    rw [h0]; exact hG
  have hCne : Cs.Nonempty := ⟨_, hmaxC⟩
  set q := Cs.min' hCne with hqdef
  have hqC : q ∈ Cs := Finset.min'_mem _ _
  have hqS : q ∈ S := (Finset.mem_filter.mp hqC).1
  have hqcnt : cnt q ≤ G := (Finset.mem_filter.mp hqC).2
  have hq0 : 0 ≤ q := hS0 q hqS
  set cge : ℝ := ∑ i ∈ range n, (if q ≤ a i then (1:ℝ) else 0) with hcge
  set ceq : ℝ := ∑ i ∈ range n, (if a i = q then (1:ℝ) else 0) with hceq
  have hsplit : cge = cnt q + ceq := by
    rw [hcge, hceq, hcnt]
    simp only []
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h1 : q < a i
    · have h2 : a i ≠ q := ne_of_gt h1
      simp [h1, h2, le_of_lt h1]
    · by_cases h2 : a i = q
      · simp [h1, h2]
      · have h3 : ¬ q ≤ a i := fun h => h1 (lt_of_le_of_ne h (Ne.symm h2))
        simp [h1, h2, h3]
  have hceq0 : 0 ≤ ceq := Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)
  have hge : 0 < q → G ≤ cge := by
    intro hqpos
    by_contra hlt
    push_neg at hlt
    set L := S.filter (fun s => s < q) with hL
    have hLne : L.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, hqpos⟩⟩
    set q' := L.max' hLne with hq'def
    have hq'L : q' ∈ L := Finset.max'_mem _ _
    have hq'S : q' ∈ S := (Finset.mem_filter.mp hq'L).1
    have hq'lt : q' < q := (Finset.mem_filter.mp hq'L).2
    have hcnt' : cnt q' ≤ cge := by
      rw [hcnt, hcge]
      apply Finset.sum_le_sum
      intro i hi
      by_cases h1 : q' < a i
      · have h2 : q ≤ a i := by
          by_contra h3
          push_neg at h3
          have hm : a i ∈ L := Finset.mem_filter.mpr ⟨haS i (Finset.mem_range.mp hi), h3⟩
          have h4 : a i ≤ q' := Finset.le_max' L (a i) hm
          linarith
        simp [h1, h2]
      · simp only [h1, if_false]
        split_ifs <;> norm_num
    have hq'C : q' ∈ Cs := Finset.mem_filter.mpr ⟨hq'S, by linarith⟩
    have h5 : q ≤ q' := Finset.min'_le Cs q' hq'C
    linarith
  set θ : ℝ := if q = 0 then 0 else (G - cnt q) / ceq with hθ
  have hθ0 : 0 ≤ θ := by
    rw [hθ]; split_ifs
    · exact le_refl _
    · exact div_nonneg (by linarith) hceq0
  have hθ1 : θ ≤ 1 := by
    rw [hθ]; split_ifs with hq
    · norm_num
    · have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
      have := hge hqpos
      rcases eq_or_lt_of_le hceq0 with he | he
      · rw [← he, div_zero]; norm_num
      · rw [div_le_one he]; linarith
  set z : ℕ → ℝ := fun i => if q < a i then 1 else if a i = q then θ else 0 with hz
  have hzsum : ∑ i ∈ range n, z i = cnt q + θ * ceq := by
    rw [hz, hcnt, hceq]
    simp only []
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h1 : q < a i
    · simp [h1, ne_of_gt h1]
    · by_cases h2 : a i = q
      · simp [h1, h2]
      · simp [h1, h2]
  have hcase : q = 0 ∨ cnt q + θ * ceq = G := by
    by_cases hq : q = 0
    · exact Or.inl hq
    · right
      have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
      have hg := hge hqpos
      rw [hsplit] at hg
      rw [hθ, if_neg hq]
      rcases eq_or_lt_of_le hceq0 with he | he
      · rw [← he, mul_zero]; linarith
      · rw [div_mul_cancel₀ _ (ne_of_gt he)]; ring
  have hval : ∑ i ∈ range n, a i * z i
      = ∑ i ∈ range n, max (a i - q) 0 + q * ∑ i ∈ range n, z i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hz]
    simp only []
    by_cases h1 : q < a i
    · rw [if_pos h1, max_eq_left (by linarith)]; ring
    · rw [if_neg h1]
      by_cases h2 : a i = q
      · rw [if_pos h2, h2, sub_self, max_self]; ring
      · rw [if_neg h2, max_eq_right (by push_neg at h1; linarith)]; ring
  refine ⟨q, hq0, z, ?_, ?_, ?_⟩
  · intro i _
    rw [hz]
    simp only []
    split_ifs
    · norm_num
    · exact ⟨hθ0, hθ1⟩
    · norm_num
  · rw [hzsum]
    rcases hcase with h | h
    · have : θ = 0 := by rw [hθ, if_pos h]
      rw [this, zero_mul, add_zero]; exact hqcnt
    · rw [h]
  · rw [hval, hzsum]
    rcases hcase with h | h
    · rw [h]; simp
    · rw [h]; linarith

/-! ### Model-level lemmas -/

open RobustInventory.SingleStation in
theorem RI32_Γ_nonneg (M : Model) (k : ℕ) : 0 ≤ M.Γ k := by
  induction k with
  | zero => exact M.hΓ0
  | succ n ih => exact le_trans ih (M.hΓmono n)

open RobustInventory.SingleStation Finset in
theorem RI32_A_le (M : Model) (k : ℕ) (q : ℝ) (r : ℕ → ℝ) (hd : M.LP13DualFeasible k q r) :
    M.A k ≤ q * M.Γ k + ∑ i ∈ range (k + 1), r i := by
  obtain ⟨hq, hr⟩ := hd
  unfold Model.A
  apply csSup_le
  · refine ⟨∑ i ∈ range (k + 1), M.what i * (fun _ => (0:ℝ)) i, fun _ => 0, ⟨fun i _ => ⟨le_refl _, zero_le_one⟩, ?_⟩, rfl⟩
    simp [RI32_Γ_nonneg M k]
  · rintro v ⟨z, ⟨hz, hzs⟩, rfl⟩
    exact RI32_weak (k+1) M.what z r q (M.Γ k) (fun i hi => hz i (Nat.lt_succ_iff.mp hi)) hzs hq
      (fun i hi => hr i (Nat.lt_succ_iff.mp hi))

open RobustInventory.SingleStation Finset in
theorem RI32_dual_attain (M : Model) (k : ℕ) :
    ∃ q : ℝ, ∃ r : ℕ → ℝ, M.LP13DualFeasible k q r ∧
      q * M.Γ k + ∑ i ∈ range (k + 1), r i = M.A k := by
  obtain ⟨q, hq, z, hz, hzs, hle⟩ := RI32_strong (k+1) M.what (M.Γ k) M.hwhat (RI32_Γ_nonneg M k)
  have hd : M.LP13DualFeasible k q (fun i => max (M.what i - q) 0) :=
    ⟨hq, fun i _ => ⟨le_max_right _ _, by linarith [le_max_left (M.what i - q) 0]⟩⟩
  refine ⟨q, fun i => max (M.what i - q) 0, hd, le_antisymm ?_ (RI32_A_le M k q _ hd)⟩
  unfold Model.A
  refine le_trans hle (le_csSup ?_ ⟨z, ⟨fun i hi => hz i (Nat.lt_succ_of_le hi), hzs⟩, rfl⟩)
  refine ⟨q * M.Γ k + ∑ i ∈ range (k + 1), max (M.what i - q) 0, ?_⟩
  rintro v ⟨z', ⟨hz', hzs'⟩, rfl⟩
  exact RI32_weak (k+1) M.what z' _ q (M.Γ k) (fun i hi => hz' i (Nat.lt_succ_iff.mp hi)) hzs' hq
    (fun i hi => hd.2 i (Nat.lt_succ_iff.mp hi))

/-! ### eq (22), eq (23) (copied from our proofs Sol_pv_180fd428 / Sol_pv_11ea8172) -/

open RobustInventory.SingleStation in
theorem RI32_telescope (M : Model) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), (M.A i - M.Aprev i) = M.A k := by
  induction k with
  | zero => simp [Model.Aprev]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp [Model.Aprev]

open RobustInventory.SingleStation in
theorem RI32_eq22 (M : Model) (u : ℕ → ℝ) (k : ℕ) :
    M.stock M.wmod u k = M.xbar u k - (M.p - M.h) / (M.p + M.h) * M.A k := by
  have ht := RI32_telescope M k
  have hs : ∑ i ∈ Finset.range (k + 1), (u i - M.wmod i)
      = ∑ i ∈ Finset.range (k + 1), (u i - M.wbar i)
        - (M.p - M.h) / (M.p + M.h) * ∑ i ∈ Finset.range (k + 1), (M.A i - M.Aprev i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Model.wmod]
    ring
  simp only [Model.xbar, Model.stock]
  rw [hs, ht]
  ring

theorem RI32_eq23 (h p xbar A : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) (hph : 0 < p + h) :
    max (h * (xbar + A)) (p * (-xbar + A)) =
      max (h * (xbar - (p - h) / (p + h) * A)) (-(p * (xbar - (p - h) / (p + h) * A)))
        + 2 * p * h / (p + h) * A := by
  have hne : p + h ≠ 0 := ne_of_gt hph
  have e1 : h * (xbar + A) = h * (xbar - (p - h) / (p + h) * A) + 2 * p * h / (p + h) * A := by
    field_simp
    ring
  have e2 : p * (-xbar + A) = -(p * (xbar - (p - h) / (p + h) * A)) + 2 * p * h / (p + h) * A := by
    field_simp
    ring
  rw [← max_add_add_right, ← e1, ← e2]

/-! ### eq (21): the robust problem for fixed orders -/

open RobustInventory.SingleStation Finset in
theorem RI32_identity (M : Model) (u : ℕ → ℝ) :
    ∑ k ∈ range M.T, (M.C (u k) + max (M.h * (M.xbar u k + M.A k)) (M.p * (-M.xbar u k + M.A k)))
      = M.nominalCost M.wmod u + 2 * M.p * M.h / (M.p + M.h) * ∑ k ∈ range M.T, M.A k := by
  have hp0 : 0 ≤ M.p := by linarith [M.hc, M.hpc]
  have hph : 0 < M.p + M.h := by linarith [M.hc, M.hpc, M.hh]
  unfold Model.nominalCost
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [RI32_eq22 M u k, RI32_eq23 M.h M.p (M.xbar u k) (M.A k) M.hh hp0 hph]
  simp only [Model.R]
  ring

open RobustInventory.SingleStation Finset in
theorem RI32_lower (M : Model) (u y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ) (hf : M.RobustFeasible u y q r) :
    M.nominalCost M.wmod u + 2 * M.p * M.h / (M.p + M.h) * ∑ k ∈ range M.T, M.A k
      ≤ M.robustObjective u y := by
  rw [← RI32_identity]
  unfold Model.robustObjective
  apply Finset.sum_le_sum
  intro k hk
  obtain ⟨_, hq, hr, hy1, hy2⟩ := hf k (Finset.mem_range.mp hk)
  have hA : M.A k ≤ q k * M.Γ k + ∑ i ∈ range (k + 1), r i k :=
    RI32_A_le M k (q k) (fun i => r i k) ⟨hq, hr⟩
  have hh := M.hh
  have hp : 0 ≤ M.p := by linarith [M.hc, M.hpc]
  have hmax : max (M.h * (M.xbar u k + M.A k)) (M.p * (-M.xbar u k + M.A k)) ≤ y k :=
    max_le (by nlinarith [mul_le_mul_of_nonneg_left hA hh])
      (by nlinarith [mul_le_mul_of_nonneg_left hA hp])
  linarith

open RobustInventory.SingleStation Finset in
theorem RI32_attain (M : Model) (u : ℕ → ℝ) (hu : ∀ k < M.T, 0 ≤ u k) :
    ∃ (y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ), M.RobustFeasible u y q r ∧
      M.robustObjective u y =
        M.nominalCost M.wmod u + 2 * M.p * M.h / (M.p + M.h) * ∑ k ∈ range M.T, M.A k := by
  choose qf rf hf using RI32_dual_attain M
  refine ⟨fun k => max (M.h * (M.xbar u k + M.A k)) (M.p * (-M.xbar u k + M.A k)), qf,
    fun i k => rf k i, ?_, ?_⟩
  · intro k hk
    obtain ⟨hd, hval⟩ := hf k
    obtain ⟨hq, hr⟩ := hd
    refine ⟨hu k hk, hq, hr, ?_, ?_⟩
    · dsimp only
      rw [add_assoc, hval]
      exact le_max_left _ _
    · dsimp only
      rw [add_assoc, hval]
      exact le_max_right _ _
  · rw [← RI32_identity]
    rfl

/-! ### Lemma 3.1(b): base-stock optimality without fixed cost -/

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
theorem RI32_lemma31b (M : Model) (hK : M.K = 0) (w : ℕ → ℝ) (hw : ∀ k < M.T, 0 ≤ w k) :
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

/-! ### Theorem 3.2 -/

open RobustInventory.SingleStation Finset in
theorem solution (M : Model) :
    (∀ u : ℕ → ℝ, (∀ k < M.T, 0 ≤ u k) →
      (∀ (y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ), M.RobustFeasible u y q r →
        M.nominalCost M.wmod u + 2 * M.p * M.h / (M.p + M.h) * ∑ k ∈ range M.T, M.A k
          ≤ M.robustObjective u y) ∧
      (∃ (y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ), M.RobustFeasible u y q r ∧
        M.robustObjective u y =
          M.nominalCost M.wmod u + 2 * M.p * M.h / (M.p + M.h) * ∑ k ∈ range M.T, M.A k)) ∧
    (∀ u : ℕ → ℝ,
      (∃ (y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ), M.IsRobustOptimal u y q r) ↔
        M.IsNominalOptimal M.wmod u) ∧
    (∀ (u y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ) (u' : ℕ → ℝ),
      M.IsRobustOptimal u y q r → M.IsNominalOptimal M.wmod u' →
        M.robustObjective u y =
          M.nominalCost M.wmod u' + 2 * M.p * M.h / (M.p + M.h) * ∑ k ∈ range M.T, M.A k) ∧
    (M.K = 0 → (∀ k < M.T, 0 ≤ M.wmod k) →
      ∃ (y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ),
        M.IsRobustOptimal (orderUpTo M.x0 M.wmod M.wmod) y q r) := by
  have p2 : ∀ u : ℕ → ℝ,
      (∃ (y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ), M.IsRobustOptimal u y q r) ↔
        M.IsNominalOptimal M.wmod u := by
    intro u
    constructor
    · rintro ⟨y, q, r, hf, hopt⟩
      have hu : ∀ k < M.T, 0 ≤ u k := fun k hk => (hf k hk).1
      refine ⟨hu, fun u' hu' => ?_⟩
      obtain ⟨y', q', r', hf', heq'⟩ := RI32_attain M u' hu'
      have h1 := hopt u' y' q' r' hf'
      have h2 := RI32_lower M u y q r hf
      linarith
    · rintro ⟨hu, hopt⟩
      obtain ⟨y, q, r, hf, heq⟩ := RI32_attain M u hu
      refine ⟨y, q, r, hf, fun u' y' q' r' hf' => ?_⟩
      have hu' : ∀ k < M.T, 0 ≤ u' k := fun k hk => (hf' k hk).1
      have h1 := RI32_lower M u' y' q' r' hf'
      have h2 := hopt u' hu'
      linarith
  refine ⟨fun u hu => ⟨fun y q r hf => RI32_lower M u y q r hf, RI32_attain M u hu⟩, p2, ?_, ?_⟩
  · rintro u y q r u' ⟨hf, hopt⟩ ⟨hu', hopt'⟩
    obtain ⟨y', q', r', hf', heq'⟩ := RI32_attain M u' hu'
    have hu : ∀ k < M.T, 0 ≤ u k := fun k hk => (hf k hk).1
    have h1 := hopt u' y' q' r' hf'
    have h2 := RI32_lower M u y q r hf
    have h3 := hopt' u hu
    linarith
  · intro hK hw
    exact (p2 _).mpr (RI32_lemma31b M hK M.wmod hw)
