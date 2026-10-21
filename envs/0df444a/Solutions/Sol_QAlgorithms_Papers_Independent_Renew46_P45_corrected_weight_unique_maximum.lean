-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P45.corrected_weight_unique_maximum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T01:36:40.904405+00:00
-- url     : https://prove2.me/submissions/7be63f67-6766-4d2b-9496-825035d9fbab

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P45
noncomputable section

open scoped Matrix ComplexOrder

open MeasureTheory

open QAlgorithms.Papers.Independent.Renew46.P45

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P45.unitaryMeasurable


open Finset

theorem g65a_pref (d : ℕ) (a b : ℕ → ℤ) (hstep : ∀ j, j + 1 < d → a (j+1) ≤ a j - b j) :
    ∀ n, n < d → a n ≤ a 0 - ∑ j ∈ range n, b j := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have := ih (by omega)
    have := hstep n hn
    rw [sum_range_succ]; linarith

theorem g65a_tele (d : ℕ) (a b : ℕ → ℤ) (hb : ∀ j, 0 ≤ b j)
    (hpref : ∀ n, n < d → a n ≤ a 0 - ∑ j ∈ range n, b j) :
    ∀ n, n ≤ d → ∑ j ∈ range n, b j * (2 * a j - 2 * ((j:ℤ) + 1) - b j) ≤
      2 * a 0 * (∑ j ∈ range n, b j) - (∑ j ∈ range n, b j)^2 - (∑ j ∈ range n, b j)
        - ∑ j ∈ range n, (2 * (j:ℤ) + 1) * b j := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 := mul_le_mul_of_nonneg_left (hpref n (by omega)) (hb n)
    simp only [sum_range_succ]
    push_cast
    nlinarith

set_option maxHeartbeats 1600000 in
theorem g65a_main (D N M : ℕ) (hN : 1 ≤ N) (a b : ℕ → ℤ) (ha : ∀ j, 0 ≤ a j)
    (hb : ∀ j, 0 ≤ b j)
    (hsa : ∑ j ∈ range (D+2), a j = M) (hsb : ∑ j ∈ range (D+2), b j = N)
    (hstep : ∀ j, j + 1 < D + 2 → a (j+1) ≤ a j - b j) :
    (∑ j ∈ range (D+2), b j * (2 * a j - 2 * ((j:ℤ) + 1) - b j)) ≤
      (if N ≤ M then (N:ℤ) * (2 * M - 2 - N) else
        2 * (M:ℤ) * N - (N:ℤ)^2 - 2 * ((D:ℤ)+2) * N + (2 * (D:ℤ) + 2) * M) ∧
    ((∑ j ∈ range (D+2), b j * (2 * a j - 2 * ((j:ℤ) + 1) - b j)) =
      (if N ≤ M then (N:ℤ) * (2 * M - 2 - N) else
        2 * (M:ℤ) * N - (N:ℤ)^2 - 2 * ((D:ℤ)+2) * N + (2 * (D:ℤ) + 2) * M) →
      a 0 = M ∧ (∀ j, 1 ≤ j → j < D + 2 → a j = 0) ∧
      (if N ≤ M then (b 0 = N ∧ ∀ j, 1 ≤ j → j < D + 2 → b j = 0) else
        (b 0 = M ∧ b (D+1) = (N:ℤ) - M ∧ ∀ j, 1 ≤ j → j < D + 1 → b j = 0))) := by
  have hpref := g65a_pref (D+2) a b hstep
  have htele := g65a_tele (D+2) a b hb hpref (D+2) le_rfl
  rw [hsb] at htele
  -- decompositions
  have hsa' : ∑ j ∈ range (D+1), a (j+1) + a 0 = M := by rw [← sum_range_succ']; exact hsa
  have hrest_nonneg : 0 ≤ ∑ j ∈ range (D+1), a (j+1) := sum_nonneg (fun j _ => ha _)
  set Q := ∑ j ∈ range (D+1), b j with hQ
  have hsbQ : Q + b (D+1) = N := by rw [hQ, ← sum_range_succ]; exact hsb
  have hQa : Q ≤ a 0 := by have := hpref (D+1) (by omega); have := ha (D+1); linarith
  set S' := ∑ j ∈ range (D+1), (j:ℤ) * b j with hS'
  have hS'0 : 0 ≤ S' := sum_nonneg (fun j _ => mul_nonneg (by positivity) (hb j))
  have hlin : ∑ j ∈ range (D+2), (2 * (j:ℤ) + 1) * b j = Q + 2 * S' + (2 * (D:ℤ) + 3) * b (D+1) := by
    rw [sum_range_succ, hQ, hS', mul_sum, ← sum_add_distrib]
    push_cast
    have : ∑ x ∈ range (D+1), (2 * (x:ℤ) + 1) * b x = ∑ x ∈ range (D+1), (b x + 2 * ((x:ℤ) * b x)) :=
      sum_congr rfl (fun x _ => by ring)
    rw [this]; ring
  rw [hlin] at htele
  have hbD := hb (D+1)
  -- zero lemmas
  have hS'zero : S' = 0 → ∀ j, 1 ≤ j → j < D + 1 → b j = 0 := by
    intro h j hj1 hj2
    have := (sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (by positivity) (hb j))).1
      (hS' ▸ h) j (mem_range.2 hj2)
    rcases mul_eq_zero.1 this with h' | h'
    · have : (j:ℤ) ≥ 1 := by exact_mod_cast hj1
      omega
    · exact h'
  have hb0 : (∀ j, 1 ≤ j → j < D + 1 → b j = 0) → b 0 = Q := by
    intro h
    rw [hQ, sum_range_succ']
    rw [sum_eq_zero (fun j hj => h (j+1) (by omega) (by simp at hj; omega))]
    simp
  have harest : a 0 = M → ∀ j, 1 ≤ j → j < D + 2 → a j = 0 := by
    intro h j hj1 hj2
    have hz : ∑ j ∈ range (D+1), a (j+1) = 0 := by linarith
    have := (sum_eq_zero_iff_of_nonneg (fun j _ => ha (j+1))).1 hz (j-1) (mem_range.2 (by omega))
    rwa [show j - 1 + 1 = j by omega] at this
  have hNpos : (1:ℤ) ≤ N := by exact_mod_cast hN
  split_ifs with hNM
  · have hNM' : (N:ℤ) ≤ M := by exact_mod_cast hNM
    refine ⟨by nlinarith, fun hEq => ?_⟩
    have hgap : 0 ≤ 2 * (N:ℤ) * (M - a 0) := by nlinarith
    have h1 : 2 * (N:ℤ) * (M - a 0) + 2 * S' + (2 * (D:ℤ) + 2) * b (D+1) ≤ 0 := by nlinarith
    have hDp : (0:ℤ) ≤ 2 * (D:ℤ) + 2 := by positivity
    have e1 : 2 * (N:ℤ) * (M - a 0) = 0 := by nlinarith
    have e2 : S' = 0 := by nlinarith
    have e3 : b (D+1) = 0 := by nlinarith
    have ha0 : a 0 = M := by
      rcases mul_eq_zero.1 e1 with h | h
      · omega
      · linarith
    refine ⟨ha0, harest ha0, ?_, ?_⟩
    · rw [hb0 (hS'zero e2)]; linarith
    · intro j hj1 hj2
      rcases (show j < D + 1 ∨ j = D + 1 by omega) with h | h
      · exact hS'zero e2 j hj1 h
      · rw [h]; exact e3
  · have hNM' : (M:ℤ) < N := by push Not at hNM; exact_mod_cast hNM
    have hDp : (0:ℤ) ≤ 2 * (D:ℤ) + 2 := by positivity
    refine ⟨by nlinarith, fun hEq => ?_⟩
    have h1 : 2 * (N:ℤ) * (M - a 0) + (2 * (D:ℤ) + 2) * (M - Q) + 2 * S' ≤ 0 := by nlinarith
    have hm1 : 0 ≤ 2 * (N:ℤ) * (M - a 0) := by nlinarith
    have hm2 : 0 ≤ (2 * (D:ℤ) + 2) * (M - Q) := by nlinarith
    have e1 : 2 * (N:ℤ) * (M - a 0) = 0 := le_antisymm (by linarith) hm1
    have e2 : S' = 0 := le_antisymm (by linarith) hS'0
    have ha0 : a 0 = M := by
      rcases mul_eq_zero.1 e1 with h | h
      · omega
      · linarith
    have e3 : Q = M := by
      have hMQ : (M:ℤ) - Q ≤ 0 := by
        by_contra hc
        push Not at hc
        have := mul_pos (by positivity : (0:ℤ) < 2 * (D:ℤ) + 2) hc
        linarith
      linarith
    refine ⟨ha0, harest ha0, ?_, ?_, hS'zero e2⟩
    · rw [hb0 (hS'zero e2)]; exact e3
    · linarith

def g65a_T {D : ℕ} (f : Fin (D+2) → ℤ) : ℕ → ℤ := fun j => if h : j < D + 2 then f ⟨j, h⟩ else 0

theorem g65a_T_val {D : ℕ} (f : Fin (D+2) → ℤ) (i : Fin (D+2)) : g65a_T f i.val = f i := by
  simp [g65a_T]

theorem g65a_sumT {D : ℕ} (f : Fin (D+2) → ℤ) : ∑ i, f i = ∑ j ∈ range (D+2), g65a_T f j := by
  rw [← Fin.sum_univ_eq_sum_range]; simp [g65a_T_val]

theorem g65a_objT {D : ℕ} (m mu : Fin (D+2) → ℤ) : weightObjective m mu =
    ∑ j ∈ range (D+2), g65a_T mu j * (2 * g65a_T m j - 2 * ((j:ℤ) + 1) - g65a_T mu j) := by
  unfold weightObjective
  rw [← Fin.sum_univ_eq_sum_range (fun j => g65a_T mu j * (2 * g65a_T m j - 2 * ((j:ℤ) + 1) - g65a_T mu j))]
  simp [g65a_T_val]

theorem g65a_Tsw (D M : ℕ) (j : ℕ) (hj : j < D + 2) :
    g65a_T (symmetricWeight (D+2) M) j = if j = 0 then (M:ℤ) else 0 := by
  simp [g65a_T, hj, symmetricWeight]

theorem g65a_Tmr (D N M : ℕ) (j : ℕ) (hj : j < D + 2) :
    g65a_T (maximizingRemoval (D+2) N M) j = if N ≤ M then (if j = 0 then (N:ℤ) else 0) else
      (if j = 0 then (M:ℤ) else if j = D + 1 then (N:ℤ) - M else 0) := by
  simp only [g65a_T, hj, dif_pos, maximizingRemoval]
  split_ifs <;> first | rfl | omega

theorem g65a_split (D : ℕ) (g : ℕ → ℤ) :
    ∑ j ∈ range (D+2), g j = g 0 + ∑ j ∈ range D, g (j+1) + g (D+1) := by
  rw [sum_range_succ, sum_range_succ']; ring

set_option maxHeartbeats 1600000 in
theorem solution (d N M : ℕ) (hd : 2 ≤ d) (hN : 1 ≤ N) :
    IsWeightFeasible d N M (symmetricWeight d M) (maximizingRemoval d N M) ∧
    ∀ m mu : Fin d → ℤ, IsWeightFeasible d N M m mu →
      weightObjective m mu ≤ weightObjective (symmetricWeight d M) (maximizingRemoval d N M) ∧
      (weightObjective m mu = weightObjective (symmetricWeight d M) (maximizingRemoval d N M) ↔
        m = symmetricWeight d M ∧ mu = maximizingRemoval d N M) := by
  obtain ⟨D, rfl⟩ : ∃ D, d = D + 2 := ⟨d - 2, by omega⟩
  -- candidate value
  have hV : weightObjective (symmetricWeight (D+2) M) (maximizingRemoval (D+2) N M) =
      (if N ≤ M then (N:ℤ) * (2 * M - 2 - N) else
        2 * (M:ℤ) * N - (N:ℤ)^2 - 2 * ((D:ℤ)+2) * N + (2 * (D:ℤ) + 2) * M) := by
    rw [g65a_objT, g65a_split]
    rw [sum_eq_zero (fun j hj => by
      have hj' := mem_range.1 hj
      rw [g65a_Tmr D N M (j+1) (by omega)]
      simp only [show j + 1 ≠ 0 by omega, show j + 1 ≠ D + 1 by omega, if_false, ite_self, zero_mul])]
    rw [g65a_Tmr D N M 0 (by omega), g65a_Tmr D N M (D+1) (by omega),
      g65a_Tsw D M 0 (by omega), g65a_Tsw D M (D+1) (by omega)]
    simp only [show D + 1 ≠ 0 by omega, if_true, if_false]
    split_ifs <;> push_cast <;> ring
  have hfeas : IsWeightFeasible (D+2) N M (symmetricWeight (D+2) M) (maximizingRemoval (D+2) N M) := by
    refine ⟨fun j => ?_, fun j => ?_, fun i j hij => ?_, ?_, ?_, fun i j hij => ?_⟩
    · simp only [symmetricWeight]; split_ifs <;> positivity
    · simp only [maximizingRemoval]; split_ifs <;> omega
    · simp only [symmetricWeight]
      have : (i:ℕ) ≤ j := hij
      split_ifs <;> omega
    · rw [g65a_sumT, g65a_split]
      rw [sum_eq_zero (fun j hj => by
        have hj' := mem_range.1 hj
        rw [g65a_Tsw D M (j+1) (by omega)]; simp)]
      rw [g65a_Tsw D M 0 (by omega), g65a_Tsw D M (D+1) (by omega)]
      simp
    · rw [g65a_sumT, g65a_split]
      rw [sum_eq_zero (fun j hj => by
        have hj' := mem_range.1 hj
        rw [g65a_Tmr D N M (j+1) (by omega)]
        simp only [show j + 1 ≠ 0 by omega, show j + 1 ≠ D + 1 by omega, if_false, ite_self])]
      rw [g65a_Tmr D N M 0 (by omega), g65a_Tmr D N M (D+1) (by omega)]
      simp only [show D + 1 ≠ 0 by omega, if_true, if_false]
      split_ifs <;> push_cast <;> ring
    · simp only [symmetricWeight, maximizingRemoval]
      have := j.isLt
      split_ifs <;> omega
  refine ⟨hfeas, fun m mu hmu => ?_⟩
  obtain ⟨hm0, hmu0, hmono, hsm, hsmu, hint⟩ := hmu
  have ha : ∀ j, 0 ≤ g65a_T m j := fun j => by
    unfold g65a_T; split_ifs
    · exact hm0 _
    · exact le_rfl
  have hb : ∀ j, 0 ≤ g65a_T mu j := fun j => by
    unfold g65a_T; split_ifs
    · exact hmu0 _
    · exact le_rfl
  have hstep : ∀ j, j + 1 < D + 2 → g65a_T m (j+1) ≤ g65a_T m j - g65a_T mu j := by
    intro j hj
    have := hint ⟨j, by omega⟩ ⟨j+1, hj⟩ rfl
    simp only [g65a_T, dif_pos hj, dif_pos (show j < D + 2 by omega)]
    linarith
  have hsa : ∑ j ∈ range (D+2), g65a_T m j = M := by rw [← g65a_sumT]; exact hsm
  have hsb : ∑ j ∈ range (D+2), g65a_T mu j = N := by rw [← g65a_sumT]; exact hsmu
  obtain ⟨hle, heq⟩ := g65a_main D N M hN (g65a_T m) (g65a_T mu) ha hb hsa hsb hstep
  rw [g65a_objT m mu, hV]
  refine ⟨hle, ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨h1, h2, h3⟩ := heq h
    constructor
    · funext i
      rw [← g65a_T_val m i, symmetricWeight]
      by_cases hi : i.val = 0
      · rw [hi, h1]; simp
      · rw [h2 i.val (by omega) i.isLt]; simp [hi]
    · funext i
      rw [← g65a_T_val mu i, ← g65a_T_val (maximizingRemoval (D+2) N M) i,
        g65a_Tmr D N M i.val i.isLt]
      have hi := i.isLt
      split_ifs at h3 ⊢ with hNM hi0 hi0 hiD
      · rw [hi0]; exact h3.1
      · exact h3.2 _ (by omega) hi
      · rw [hi0]; exact h3.1
      · rw [hiD]; exact h3.2.1
      · exact h3.2.2 _ (by omega) (by omega)
  · obtain ⟨rfl, rfl⟩ := h
    rw [← hV, g65a_objT]
