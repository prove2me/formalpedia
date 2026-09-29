-- Prove2me | solution 1 for OnlineConvexOpt.ChangingEnv.fixed_share_regret
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T20:03:31.890532+00:00
-- url     : https://prove2.me/submissions/98b242f2-9fc1-4737-973e-45581f219011

import Mathlib
import Definitions.Def_OnlineConvexOpt_ChangingEnv_FixedShare
import Definitions.Def_OnlineConvexOpt_ChangingEnv_ExpConcave

set_option autoImplicit false

/-- Telescoping over a round interval `[r, s]`: per-round bounds
`a t ≤ b (t+1) - b t - c` add up to `b (s+1) - b r - (s+1-r) c`. -/
theorem fsr_telescope (a b : ℕ → ℝ) (c : ℝ) (r : ℕ)
    (h : ∀ t, a t ≤ b (t + 1) - b t - c) :
    ∀ s, r ≤ s →
      (∑ t ∈ Finset.Icc r s, a t) ≤ b (s + 1) - b r - ((s + 1 - r : ℕ) : ℝ) * c := by
  intro s hrs
  induction s, hrs using Nat.le_induction with
  | base =>
    simp only [Finset.Icc_self, Finset.sum_singleton]
    have h1 : (r + 1 - r : ℕ) = 1 := by omega
    rw [h1, Nat.cast_one, one_mul]
    exact h r
  | succ n hrn ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h1 : (n + 1 + 1 - r : ℕ) = (n + 1 - r) + 1 := by omega
    rw [h1, Nat.cast_succ]
    have h2 := h (n + 1)
    linarith

open OnlineConvexOpt.ChangingEnv in
theorem solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {N : ℕ} (hN : 0 < N)
    (α : ℝ) (hαpos : 0 < α)
    (f : ℕ → E → ℝ) (hfexp : ∀ t, IsAlphaExpConcaveOn Set.univ (f t) α)
    (T : ℕ) (hT : 1 ≤ T)
    (δ : ℝ) (hδ : δ = 1 / (2 * T))
    (xi : ℕ → Fin N → E) (p phat : ℕ → Fin N → ℝ) (x : ℕ → E)
    (hrun : IsFixedShareRun f α δ xi p phat x)
    (r s : ℕ) (hrs : r ≤ s) (hsT : s < T) (i : Fin N) :
    (∑ t ∈ Finset.Icc r s, f t (x t)) - ∑ t ∈ Finset.Icc r s, f t (xi t i) ≤
      (1 / α) * Real.log (2 * N * T) + 1 / α := by
  obtain ⟨hp0, hx, hphat, hp⟩ := hrun
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδT : δ * T = 1 / 2 := by rw [hδ]; field_simp
  have hδle : δ ≤ 1 / 2 := by nlinarith
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩
  have hZpos : ∀ t, (∀ j, 0 < p t j) →
      0 < ∑ j : Fin N, p t j * Real.exp (-α * f t (xi t j)) := by
    intro t hpos
    exact Finset.sum_pos (fun j _ => mul_pos (hpos j) (Real.exp_pos _)) hne
  have hprob : ∀ t, (∀ j, 0 < p t j) ∧ ∑ j : Fin N, p t j = 1 := by
    intro t
    induction t with
    | zero =>
      refine ⟨fun j => by rw [hp0 j]; positivity, ?_⟩
      simp only [hp0, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    | succ t ih =>
      obtain ⟨hpos, hsum⟩ := ih
      have hZ := hZpos t hpos
      have hph : ∀ j, 0 < phat (t + 1) j := fun j => by
        rw [hphat t j]; exact div_pos (mul_pos (hpos j) (Real.exp_pos _)) hZ
      have hphsum : ∑ j : Fin N, phat (t + 1) j = 1 := by
        simp only [hphat t]
        rw [← Finset.sum_div, div_self hZ.ne']
      refine ⟨fun j => ?_, ?_⟩
      · rw [hp t j]
        have h1 : 0 ≤ (1 - δ) * phat (t + 1) j := mul_nonneg (by linarith) (hph j).le
        have h2 : 0 < δ / N := div_pos hδpos hNr
        linarith
      · simp only [hp t]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hphsum, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        field_simp
        ring
  have hpos : ∀ t j, 0 < p t j := fun t j => (hprob t).1 j
  have hph : ∀ t j, 0 < phat (t + 1) j := fun t j => by
    rw [hphat t j]
    exact div_pos (mul_pos (hpos t j) (Real.exp_pos _)) (hZpos t (hpos t))
  have hle1 : ∀ t j, p t j ≤ 1 := by
    intro t j
    rw [← (hprob t).2]
    exact Finset.single_le_sum (fun k _ => (hpos t k).le) (Finset.mem_univ j)
  have hlow : ∀ t, δ / N ≤ p t i := by
    intro t
    cases t with
    | zero =>
      rw [hp0 i]
      exact (div_le_div_iff_of_pos_right hNr).mpr (by linarith)
    | succ t =>
      rw [hp t i]
      have h1 : 0 ≤ (1 - δ) * phat (t + 1) i := mul_nonneg (by linarith) (hph t i).le
      linarith
  have hround : ∀ t, α * (f t (x t) - f t (xi t i)) ≤
      Real.log (p (t + 1) i) - Real.log (p t i) - Real.log (1 - δ) := by
    intro t
    have hZ := hZpos t (hpos t)
    have hc : ConcaveOn ℝ Set.univ (fun y => Real.exp (-α * f t y)) := hfexp t
    have hJ0 := hc.le_map_sum (fun j _ => (hpos t j).le) (hprob t).2
      (fun j _ => Set.mem_univ (xi t j))
    simp only [smul_eq_mul] at hJ0
    rw [← hx t] at hJ0
    have hlogZ := Real.log_le_log hZ hJ0
    rw [Real.log_exp] at hlogZ
    have hphat_eq : Real.log (phat (t + 1) i) =
        Real.log (p t i) + (-α * f t (xi t i)) -
          Real.log (∑ j : Fin N, p t j * Real.exp (-α * f t (xi t j))) := by
      rw [hphat t i, Real.log_div (mul_pos (hpos t i) (Real.exp_pos _)).ne' hZ.ne',
        Real.log_mul (hpos t i).ne' (Real.exp_pos _).ne', Real.log_exp]
    have hstep : Real.log (phat (t + 1) i) + Real.log (1 - δ) ≤ Real.log (p (t + 1) i) := by
      rw [← Real.log_mul (hph t i).ne' (by linarith : (1 : ℝ) - δ ≠ 0)]
      apply Real.log_le_log (mul_pos (hph t i) (by linarith))
      rw [hp t i]
      have h2 : 0 < δ / N := div_pos hδpos hNr
      linarith [mul_comm (phat (t + 1) i) (1 - δ)]
    rw [neg_mul] at hlogZ hphat_eq
    rw [mul_sub]
    linarith
  have htel := fsr_telescope (fun t => α * (f t (x t) - f t (xi t i)))
    (fun t => Real.log (p t i)) (Real.log (1 - δ)) r hround s hrs
  rw [← Finset.mul_sum, Finset.sum_sub_distrib] at htel
  -- the three bounds
  have hA : Real.log (p (s + 1) i) ≤ 0 := Real.log_nonpos (hpos _ _).le (hle1 _ _)
  have hδN : δ / N = (2 * (N : ℝ) * T)⁻¹ := by rw [hδ]; field_simp
  have hB : -Real.log (2 * N * T) ≤ Real.log (p r i) := by
    have h1 := Real.log_le_log (div_pos hδpos hNr) (hlow r)
    rw [hδN, Real.log_inv] at h1
    exact h1
  have hL0 : Real.log (1 - δ) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have hm0 : (0 : ℝ) ≤ ((s + 1 - r : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmT : ((s + 1 - r : ℕ) : ℝ) ≤ T := by exact_mod_cast (by omega : s + 1 - r ≤ T)
  have hTL : -1 ≤ (T : ℝ) * Real.log (1 - δ) := by
    have h1d : (0 : ℝ) < 1 - δ := by linarith
    have hlog := Real.one_sub_inv_le_log_of_pos h1d
    set y := (1 - δ)⁻¹ with hydef
    have hy : y * (1 - δ) = 1 := inv_mul_cancel₀ h1d.ne'
    have hy2 : y ≤ 2 := by
      have := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) (by linarith : (1 : ℝ) / 2 ≤ 1 - δ)
      rw [← hydef] at this
      norm_num at this
      linarith
    have e1 : (T : ℝ) * (1 - y) = -(y * (δ * T)) := by linear_combination (-(T : ℝ)) * hy
    rw [hδT] at e1
    have hT0 : (0 : ℝ) ≤ T := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hlog hT0]
  have hmL : -(((s + 1 - r : ℕ) : ℝ) * Real.log (1 - δ)) ≤ 1 := by
    nlinarith [mul_le_mul_of_nonpos_right hmT hL0]
  have hfinal : α * ((∑ t ∈ Finset.Icc r s, f t (x t)) - ∑ t ∈ Finset.Icc r s, f t (xi t i)) ≤
      Real.log (2 * N * T) + 1 := by linarith
  rw [show (1 / α) * Real.log (2 * N * T) + 1 / α = (Real.log (2 * N * T) + 1) / α by ring,
    le_div_iff₀ hαpos]
  linarith [mul_comm α ((∑ t ∈ Finset.Icc r s, f t (x t)) - ∑ t ∈ Finset.Icc r s, f t (xi t i))]
