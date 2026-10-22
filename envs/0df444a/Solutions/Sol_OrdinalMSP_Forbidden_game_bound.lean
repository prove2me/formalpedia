-- Prove2me | solution 1 for OrdinalMSP.Forbidden.game_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T13:19:25.973761+00:00
-- url     : https://prove2.me/submissions/9f186aec-9035-40a5-affa-8427924734c0

import Mathlib

namespace OMSPgame

open intervalIntegral

/-- Beta integral on `[p,1]`. -/
theorem beta_int (p : ℝ) : ∀ b a : ℕ,
    (∫ τ in p..1, (τ - p) ^ a * (1 - τ) ^ b) =
      (1 - p) ^ (a + b + 1) * (a.factorial : ℝ) * (b.factorial : ℝ) / ((a + b + 1).factorial : ℝ) := by
  intro b
  induction b with
  | zero =>
    intro a
    simp only [pow_zero, mul_one, add_zero, Nat.factorial_zero, Nat.cast_one]
    rw [intervalIntegral.integral_comp_sub_right (fun x => x ^ a) p, integral_pow]
    rw [Nat.factorial_succ]
    push_cast
    have : (a.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  | succ b ih =>
    intro a
    have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := p) (b := 1)
      (u := fun τ : ℝ => (1 - τ) ^ (b + 1))
      (u' := fun τ : ℝ => -((b : ℝ) + 1) * (1 - τ) ^ b)
      (v := fun τ : ℝ => (τ - p) ^ (a + 1) / ((a : ℝ) + 1))
      (v' := fun τ : ℝ => (τ - p) ^ a)
      (fun x _ => by
        have h := ((hasDerivAt_id' x).const_sub (1:ℝ)).pow (b + 1)
        refine h.congr_deriv ?_
        simp; ring)
      (fun x _ => by
        have h := (((hasDerivAt_id' x).sub_const p).pow (a + 1)).div_const ((a : ℝ) + 1)
        refine h.congr_deriv ?_
        simp; field_simp)
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)
    have e1 : (∫ τ in p..1, (τ - p) ^ a * (1 - τ) ^ (b + 1)) =
        ∫ τ in p..1, (1 - τ) ^ (b + 1) * (τ - p) ^ a := by
      congr 1; ext τ; ring
    have e2 : (∫ τ in p..1, (-((b : ℝ) + 1) * (1 - τ) ^ b) * ((τ - p) ^ (a + 1) / ((a : ℝ) + 1)))
        = (-((b : ℝ) + 1) / ((a : ℝ) + 1)) * ∫ τ in p..1, (τ - p) ^ (a + 1) * (1 - τ) ^ b := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1; ext τ; field_simp
    rw [e1, hparts, e2, ih (a + 1)]
    simp only [sub_self, zero_pow (Nat.succ_ne_zero _), zero_mul, zero_div, mul_zero]
    have h1 : a + 1 + b + 1 = a + (b + 1) + 1 := by ring
    rw [h1, Nat.factorial_succ a, Nat.factorial_succ b]
    push_cast
    have : (a.factorial : ℝ) ≠ 0 := by positivity
    have : ((a + (b + 1) + 1).factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring


/-- `∏_{j=s+1}^{t-1} (1 - k/j)_+`. -/
noncomputable def fK (k s t : ℕ) : ℝ := ∏ j ∈ Finset.Ico (s + 1) t, max 0 (1 - (k : ℝ) / (j : ℝ))

lemma fK_nonneg (k s t : ℕ) : 0 ≤ fK k s t :=
  Finset.prod_nonneg (fun _ _ => le_max_left _ _)

lemma fK_self (k s : ℕ) : fK k s (s + 1) = 1 := by
  simp [fK]

lemma fK_ge (k s m : ℕ) (hkm : k ≤ m) (hsm : s ≤ m) :
    ((s.choose k : ℕ) : ℝ) / ((m.choose k : ℕ) : ℝ) ≤ fK k s (m + 1) := by
  by_cases hks : k ≤ s
  · obtain ⟨d, rfl⟩ : ∃ d, m = s + d := ⟨m - s, by omega⟩
    clear hkm hsm
    induction d with
    | zero =>
      rw [add_zero, fK_self]
      exact div_self_le_one _
    | succ d ih =>
      have hM : fK k s (s + (d + 1) + 1) = fK k s (s + d + 1) *
          max 0 (1 - (k : ℝ) / (((s + d + 1 : ℕ)) : ℝ)) := by
        unfold fK
        rw [show s + (d + 1) + 1 = (s + d + 1) + 1 by ring]
        rw [Finset.prod_Ico_succ_top (by omega)]
      rw [hM]
      set M := s + d with hMdef
      have hkM : k ≤ M := by omega
      have hpos : (0 : ℝ) < ((M.choose k : ℕ) : ℝ) := by
        exact_mod_cast Nat.choose_pos hkM
      have hrel := Nat.choose_mul_succ_eq M k
      have hrelR : ((M.choose k : ℕ) : ℝ) * ((M : ℝ) + 1) =
          (((M + 1).choose k : ℕ) : ℝ) * ((M : ℝ) + 1 - k) := by
        have : ((M.choose k * (M + 1) : ℕ) : ℝ) = (((M + 1).choose k * (M + 1 - k) : ℕ) : ℝ) := by
          rw [hrel]
        push_cast [Nat.cast_sub (by omega : k ≤ M + 1)] at this
        exact this
      have hpos2 : (0 : ℝ) < (((M + 1).choose k : ℕ) : ℝ) := by
        exact_mod_cast Nat.choose_pos (by omega)
      have hfac : 0 ≤ 1 - (k : ℝ) / (((M + 1 : ℕ)) : ℝ) := by
        rw [sub_nonneg, div_le_one (by positivity)]
        push_cast
        have : (k : ℝ) ≤ M := by exact_mod_cast hkM
        linarith
      rw [show s + (d + 1) = M + 1 by omega, max_eq_right hfac]
      have key : ((s.choose k : ℕ) : ℝ) / (((M + 1).choose k : ℕ) : ℝ) =
          ((s.choose k : ℕ) : ℝ) / ((M.choose k : ℕ) : ℝ) * (1 - (k : ℝ) / (((M + 1 : ℕ)) : ℝ)) := by
        push_cast
        field_simp
        linear_combination (((s.choose k : ℕ) : ℝ)) * hrelR
      rw [key]
      exact mul_le_mul_of_nonneg_right ih hfac
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp only [Nat.cast_zero, zero_div]
    exact fK_nonneg _ _ _

lemma binom_id (m k : ℕ) (hkm : k ≤ m) (x y : ℝ) :
    ∑ s ∈ Finset.range (m + 1), ((m.choose s : ℕ) : ℝ) * ((s.choose k : ℕ) : ℝ) * x ^ s * y ^ (m - s)
      = ((m.choose k : ℕ) : ℝ) * x ^ k * (x + y) ^ (m - k) := by
  have hsplit : m + 1 = k + (m - k + 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  rw [add_pow]
  rw [show (∑ s ∈ Finset.range k,
      ((m.choose s : ℕ) : ℝ) * ((s.choose k : ℕ) : ℝ) * x ^ s * y ^ (m - s)) = 0 by
    apply Finset.sum_eq_zero
    intro s hs
    rw [Finset.mem_range] at hs
    rw [Nat.choose_eq_zero_of_lt hs]; simp, zero_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.mem_range] at hu
  have hc := Nat.choose_mul (n := m) (k := k + u) (s := k) (by omega)
  rw [show k + u - k = u by omega] at hc
  have hcR : ((m.choose (k + u) : ℕ) : ℝ) * (((k + u).choose k : ℕ) : ℝ) =
      ((m.choose k : ℕ) : ℝ) * (((m - k).choose u : ℕ) : ℝ) := by exact_mod_cast hc
  rw [show m - (k + u) = m - k - u by omega, pow_add]
  linear_combination (x ^ k * x ^ u * y ^ (m - k - u)) * hcR

lemma inner_bound (m k : ℕ) (p τ : ℝ) (hp : 0 < p) (hpτ : p ≤ τ) :
    τ ^ m * (p / τ) ^ k ≤
      ∑ s ∈ Finset.range (m + 1),
        ((m.choose s : ℕ) : ℝ) * p ^ s * (τ - p) ^ (m - s) * fK k s (m + 1) := by
  have hτ : 0 < τ := lt_of_lt_of_le hp hpτ
  have hq0 : 0 ≤ p / τ := by positivity
  have hq1 : p / τ ≤ 1 := by rw [div_le_one hτ]; exact hpτ
  have hnn : ∀ s ∈ Finset.range (m + 1),
      0 ≤ ((m.choose s : ℕ) : ℝ) * p ^ s * (τ - p) ^ (m - s) * fK k s (m + 1) := by
    intro s _
    have : 0 ≤ τ - p := by linarith
    have := fK_nonneg k s (m + 1)
    positivity
  by_cases hkm : k ≤ m
  · -- use the binomial identity
    have hb := binom_id m k hkm p (τ - p)
    rw [show p + (τ - p) = τ by ring] at hb
    have hpos : (0 : ℝ) < ((m.choose k : ℕ) : ℝ) := by exact_mod_cast Nat.choose_pos hkm
    have hlhs : τ ^ m * (p / τ) ^ k = p ^ k * τ ^ (m - k) := by
      rw [div_pow]
      have : τ ^ m = τ ^ k * τ ^ (m - k) := by rw [← pow_add]; congr 1; omega
      rw [this]; field_simp
    rw [hlhs]
    calc p ^ k * τ ^ (m - k)
        = (∑ s ∈ Finset.range (m + 1), ((m.choose s : ℕ) : ℝ) * ((s.choose k : ℕ) : ℝ) *
            p ^ s * (τ - p) ^ (m - s)) / ((m.choose k : ℕ) : ℝ) := by
          rw [hb]; field_simp
      _ = ∑ s ∈ Finset.range (m + 1), ((m.choose s : ℕ) : ℝ) * p ^ s * (τ - p) ^ (m - s) *
            (((s.choose k : ℕ) : ℝ) / ((m.choose k : ℕ) : ℝ)) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl; intro s _; ring
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro s hs
          rw [Finset.mem_range] at hs
          have : 0 ≤ τ - p := by linarith
          apply mul_le_mul_of_nonneg_left (fK_ge k s m hkm (by omega))
          positivity
  · -- the term s = m alone suffices
    have hsingle := Finset.single_le_sum hnn (Finset.self_mem_range_succ m)
    rw [Nat.choose_self, Nat.sub_self, pow_zero, fK_self] at hsingle
    simp only [Nat.cast_one, one_mul, mul_one] at hsingle
    refine le_trans ?_ hsingle
    have : (p / τ) ^ k ≤ (p / τ) ^ m := pow_le_pow_of_le_one hq0 hq1 (by omega)
    calc τ ^ m * (p / τ) ^ k ≤ τ ^ m * (p / τ) ^ m :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = p ^ m := by rw [div_pow]; field_simp

lemma comb_id (N s m : ℕ) (hsm : s ≤ m) (hmN : m ≤ N) :
    ((N.choose m : ℕ) : ℝ) * ((m.choose s : ℕ) : ℝ) *
        (((m - s).factorial : ℝ) * ((N - m).factorial : ℝ) / ((N + 1 - s).factorial : ℝ)) =
      (((N + 1).choose s : ℕ) : ℝ) * (1 / ((N : ℝ) + 1)) := by
  rw [Nat.cast_choose ℝ hmN, Nat.cast_choose ℝ hsm, Nat.cast_choose ℝ (by omega : s ≤ N + 1)]
  rw [Nat.factorial_succ N]
  push_cast
  have h1 : ((m.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have h2 : (((N - m).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have h3 : (((m - s).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have h4 : (((N + 1 - s).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have h5 : ((s.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have h6 : (N : ℝ) + 1 ≠ 0 := by positivity
  field_simp

lemma weight (N s m : ℕ) (hsm : s ≤ m) (hmN : m ≤ N) (p : ℝ) :
    (∫ τ in p..1, (((N.choose m : ℕ) : ℝ) * ((m.choose s : ℕ) : ℝ) * p ^ s) *
        ((τ - p) ^ (m - s) * (1 - τ) ^ (N - m))) =
      (((N + 1).choose s : ℕ) : ℝ) * p ^ s * (1 - p) ^ (N + 1 - s) * (1 / ((N : ℝ) + 1)) := by
  rw [intervalIntegral.integral_const_mul, beta_int p (N - m) (m - s)]
  rw [show m - s + (N - m) + 1 = N + 1 - s by omega]
  have hc := comb_id N s m hsm hmN
  calc ((N.choose m : ℕ) : ℝ) * ((m.choose s : ℕ) : ℝ) * p ^ s *
        ((1 - p) ^ (N + 1 - s) * ((m - s).factorial : ℝ) * ((N - m).factorial : ℝ) /
          ((N + 1 - s).factorial : ℝ))
      = (((N.choose m : ℕ) : ℝ) * ((m.choose s : ℕ) : ℝ) *
        (((m - s).factorial : ℝ) * ((N - m).factorial : ℝ) / ((N + 1 - s).factorial : ℝ))) *
          (p ^ s * (1 - p) ^ (N + 1 - s)) := by ring
    _ = _ := by rw [hc]; ring

end OMSPgame

open OMSPgame in
theorem solution (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    (∫ τ in p..1, (p / τ) ^ k) ≤
      ∑ s ∈ Finset.range (n + 1),
        (n.choose s : ℝ) * p ^ s * (1 - p) ^ (n - s) *
          ((1 / (n : ℝ)) *
            ∑ t ∈ Finset.Icc (s + 1) n,
              ∏ j ∈ Finset.Ico (s + 1) t, max 0 (1 - (k : ℝ) / (j : ℝ))) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  set g : ℕ → ℕ → ℝ → ℝ := fun s t τ =>
    ((((N.choose (t - 1) : ℕ) : ℝ) * (((t - 1).choose s : ℕ) : ℝ) * p ^ s) *
        ((τ - p) ^ (t - 1 - s) * (1 - τ) ^ (N - (t - 1)))) * fK k s t with hg
  have hgc : ∀ s t, Continuous (g s t) := by
    intro s t; simp only [hg]; fun_prop
  -- RHS as a sum of integrals
  have hRHS : ∑ s ∈ Finset.range (N + 1 + 1),
        ((N + 1).choose s : ℝ) * p ^ s * (1 - p) ^ (N + 1 - s) *
          ((1 / ((N + 1 : ℕ) : ℝ)) *
            ∑ t ∈ Finset.Icc (s + 1) (N + 1),
              ∏ j ∈ Finset.Ico (s + 1) t, max 0 (1 - (k : ℝ) / (j : ℝ))) =
      ∑ s ∈ Finset.range (N + 1 + 1), ∑ t ∈ Finset.Icc (s + 1) (N + 1), ∫ τ in p..1, g s t τ := by
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_Icc] at ht
    simp only [hg]
    rw [intervalIntegral.integral_mul_const, weight N s (t - 1) (by omega) (by omega) p]
    simp only [fK]
    push_cast
    ring
  rw [hRHS]
  have hswap : ∑ s ∈ Finset.range (N + 1 + 1), ∑ t ∈ Finset.Icc (s + 1) (N + 1),
      ∫ τ in p..1, g s t τ =
      ∫ τ in p..1, ∑ s ∈ Finset.range (N + 1 + 1), ∑ t ∈ Finset.Icc (s + 1) (N + 1), g s t τ := by
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro s _
      rw [intervalIntegral.integral_finsetSum]
      intro t _
      exact (hgc s t).intervalIntegrable _ _
    · intro s _
      apply Continuous.intervalIntegrable
      exact continuous_finset_sum _ (fun t _ => hgc s t)
  rw [hswap]
  apply intervalIntegral.integral_mono_on hp1
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.pow
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro x hx
    rw [Set.uIcc_of_le hp1] at hx
    exact (lt_of_lt_of_le hp0 hx.1).ne'
  · apply Continuous.intervalIntegrable
    exact continuous_finset_sum _ (fun s _ => continuous_finset_sum _ (fun t _ => hgc s t))
  intro τ hτ
  obtain ⟨hpτ, hτ1⟩ := hτ
  have hτpos : 0 < τ := lt_of_lt_of_le hp0 hpτ
  -- reorganize the double sum by t = m + 1
  rw [Finset.sum_comm' (t' := Finset.Icc 1 (N + 1)) (s' := fun t => Finset.range t) (by
    intro x y
    simp only [Finset.mem_range, Finset.mem_Icc]
    omega)]
  have hIcc : Finset.Icc 1 (N + 1) = Finset.Ico (0 + 1) (N + 1 + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, ← Finset.sum_Ico_add', ← Finset.range_eq_Ico]
  -- binomial identity for the outer weights
  have hbin : (p / τ) ^ k = ∑ m ∈ Finset.range (N + 1),
      ((N.choose m : ℕ) : ℝ) * (1 - τ) ^ (N - m) * (τ ^ m * (p / τ) ^ k) := by
    have h := add_pow τ (1 - τ) N
    rw [show τ + (1 - τ) = 1 by ring, one_pow] at h
    calc (p / τ) ^ k = (p / τ) ^ k * 1 := by ring
      _ = (p / τ) ^ k * ∑ m ∈ Finset.range (N + 1), τ ^ m * (1 - τ) ^ (N - m) * (N.choose m : ℝ) := by
          rw [← h]
      _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _; ring
  rw [hbin]
  apply Finset.sum_le_sum
  intro m hm
  rw [Finset.mem_range] at hm
  have hin := inner_bound m k p τ hp0 hpτ
  have hw : 0 ≤ ((N.choose m : ℕ) : ℝ) * (1 - τ) ^ (N - m) := by
    have : 0 ≤ 1 - τ := by linarith
    positivity
  calc ((N.choose m : ℕ) : ℝ) * (1 - τ) ^ (N - m) * (τ ^ m * (p / τ) ^ k)
      ≤ ((N.choose m : ℕ) : ℝ) * (1 - τ) ^ (N - m) *
          ∑ s ∈ Finset.range (m + 1),
            ((m.choose s : ℕ) : ℝ) * p ^ s * (τ - p) ^ (m - s) * fK k s (m + 1) :=
        mul_le_mul_of_nonneg_left hin hw
    _ = ∑ s ∈ Finset.range (m + 1), g s (m + 1) τ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        simp only [hg, Nat.add_sub_cancel]
        ring
