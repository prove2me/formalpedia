-- Prove2me | solution 1 for RegMCBSDE.Projection.discrete_gronwall
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-25T23:14:22.168797+00:00
-- url     : https://prove2.me/submissions/a18f05c5-79c2-46ca-99c1-99edf4ff752b

import Mathlib

theorem solution (T : ℝ) (hT : 0 < T) (N : ℕ) (hN : 0 < N) (γ : ℝ) (hγ : 0 < γ)
    (a b c : ℕ → ℝ) (ha : ∀ k ≤ N, 0 ≤ a k) (hb : ∀ k ≤ N, 0 ≤ b k) (hc : ∀ k ≤ N, 0 ≤ c k)
    (hrec : ∀ k, 1 ≤ k → k ≤ N →
      a (k - 1) + c (k - 1) ≤ (1 + γ * (T / N)) * a k + b (k - 1)) :
    ∀ k ≤ N, a k + ∑ i ∈ Finset.Ico k N, c i
      ≤ Real.exp (γ * (T - (k : ℝ) * (T / N))) * (a N + ∑ i ∈ Finset.Ico k N, b i) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  set h : ℝ := T / N with hh
  have hh0 : 0 ≤ h := by positivity
  have key : ∀ j, j ≤ N → a (N - j) + ∑ i ∈ Finset.Ico (N - j) N, c i
      ≤ Real.exp (γ * (T - ((N - j : ℕ) : ℝ) * h)) * (a N + ∑ i ∈ Finset.Ico (N - j) N, b i) := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [Nat.sub_zero, Finset.Ico_self, Finset.sum_empty, add_zero]
      have : γ * (T - (N : ℝ) * h) = 0 := by
        rw [hh]; field_simp; ring
      rw [this]; simp
    | succ j ih =>
      intro hj
      have ih := ih (by omega)
      set m := N - (j+1) with hm
      have hm1 : N - j = m + 1 := by omega
      rw [hm1] at ih
      have hmN : m < N := by omega
      have hr := hrec (m+1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at hr
      rw [Finset.sum_eq_sum_Ico_succ_bot hmN, Finset.sum_eq_sum_Ico_succ_bot hmN]
      have hSc : 0 ≤ ∑ i ∈ Finset.Ico (m+1) N, c i :=
        Finset.sum_nonneg (fun i hi => hc i (Finset.mem_Ico.mp hi).2.le)
      have hSb : 0 ≤ ∑ i ∈ Finset.Ico (m+1) N, b i :=
        Finset.sum_nonneg (fun i hi => hb i (Finset.mem_Ico.mp hi).2.le)
      have ha1 := ha (m+1) (by omega)
      have haN := ha N le_rfl
      have hbm := hb m hmN.le
      set X := a N + ∑ i ∈ Finset.Ico (m+1) N, b i with hX
      have hX0 : 0 ≤ X := by positivity
      set E1 := Real.exp (γ * (T - ((m+1 : ℕ) : ℝ) * h)) with hE1
      have hE1pos : 0 < E1 := Real.exp_pos _
      have hEm : Real.exp (γ * (T - (m : ℝ) * h)) = E1 * Real.exp (γ * h) := by
        rw [hE1, ← Real.exp_add]; congr 1; push_cast; ring
      rw [hEm]
      have hexp : 1 + γ * h ≤ Real.exp (γ * h) := by linarith [Real.add_one_le_exp (γ * h)]
      have hge1 : 1 ≤ Real.exp (γ * h) := Real.one_le_exp (by positivity)
      have hg0 : 0 ≤ γ * h := by positivity
      have s1 : (1 + γ * h) * a (m+1) + ∑ i ∈ Finset.Ico (m+1) N, c i
          ≤ (1 + γ * h) * (a (m+1) + ∑ i ∈ Finset.Ico (m+1) N, c i) := by
        nlinarith
      have s2 : (1 + γ * h) * (a (m+1) + ∑ i ∈ Finset.Ico (m+1) N, c i) ≤ (1 + γ * h) * (E1 * X) :=
        mul_le_mul_of_nonneg_left ih (by linarith)
      have s3 : (1 + γ * h) * (E1 * X) ≤ Real.exp (γ * h) * (E1 * X) :=
        mul_le_mul_of_nonneg_right hexp (by positivity)
      have s4 : b m ≤ E1 * Real.exp (γ * h) * b m := by
        have : 1 ≤ E1 * Real.exp (γ * h) := by
          rw [← hEm]; exact Real.one_le_exp (by
            have : (m:ℝ) * h ≤ T := by
              have : (m:ℝ) ≤ N := by exact_mod_cast hmN.le
              calc (m:ℝ) * h ≤ N * h := by gcongr
                _ = T := by rw [hh]; field_simp
            nlinarith)
        nlinarith
      calc a m + (c m + ∑ i ∈ Finset.Ico (m+1) N, c i)
          = (a m + c m) + ∑ i ∈ Finset.Ico (m+1) N, c i := by ring
        _ ≤ ((1 + γ * h) * a (m+1) + b m) + ∑ i ∈ Finset.Ico (m+1) N, c i := by linarith
        _ ≤ Real.exp (γ * h) * (E1 * X) + E1 * Real.exp (γ * h) * b m := by linarith
        _ = E1 * Real.exp (γ * h) * (a N + (b m + ∑ i ∈ Finset.Ico (m+1) N, b i)) := by
          rw [hX]; ring
  intro k hk
  have := key (N - k) (by omega)
  rwa [Nat.sub_sub_self hk] at this
