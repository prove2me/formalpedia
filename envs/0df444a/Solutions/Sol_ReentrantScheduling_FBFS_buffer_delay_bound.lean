-- Prove2me | solution 1 for ReentrantScheduling.FBFS.buffer_delay_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T08:18:46.203922+00:00
-- url     : https://prove2.me/submissions/16125b9a-5ec2-4478-b867-d4bc92866011

import Mathlib
import Definitions.Def_ReentrantScheduling_FBFS_Model
import Definitions.Def_ReentrantScheduling_FBFS_Constants
import Theorems.Thm_ReentrantScheduling_FBFS_busy_period_bound

open ReentrantScheduling.FBFS Finset

theorem solution
    (L : Line) (lam γ : ℝ) (hlam : 0 ≤ lam) (hγ : 0 ≤ γ) (hload : L.load lam < 1)
    (R : Run L) (hR : R.Admissible L.fbfs) (harr : R.Arrivals lam γ) :
    ∃ T : Fin L.l → ℝ, ∀ (j : Fin L.l) (p : R.Part), R.entry p ≤ j →
      ((T j : ℝ) : WithTop ℝ) < R.arrive p j →
      R.start p j + ((L.τ j : ℝ) : WithTop ℝ) ≤
        R.arrive p j + ((L.Gamma lam γ j + L.τ j : ℝ) : WithTop ℝ) := by
  -- the denominator of Γ^(i) is positive
  have hden : ∀ i : Fin L.l, 0 < 1 - ∑ j ∈ univ.filter (fun j => j ≤ i ∧ L.center j = L.center i),
      lam * L.τ j / (L.m (L.center i) : ℝ) := by
    intro i
    have hm : (0 : ℝ) < L.m (L.center i) := by exact_mod_cast L.m_pos _
    have h1 : ∑ j ∈ univ.filter (fun j => j ≤ i ∧ L.center j = L.center i),
        lam * L.τ j / (L.m (L.center i) : ℝ) ≤ lam * L.w (L.center i) := by
      unfold Line.w
      rw [mul_sum]
      calc ∑ j ∈ univ.filter (fun j => j ≤ i ∧ L.center j = L.center i),
            lam * L.τ j / (L.m (L.center i) : ℝ)
          = ∑ j ∈ univ.filter (fun j => j ≤ i ∧ L.center j = L.center i),
            lam * (L.τ j / (L.m (L.center i) : ℝ)) := by
            refine sum_congr rfl fun j _ => by ring
        _ ≤ ∑ j ∈ univ.filter (fun j => L.center j = L.center i),
            lam * (L.τ j / (L.m (L.center i) : ℝ)) := by
            apply sum_le_sum_of_subset_of_nonneg
            · intro j hj; simp only [mem_filter, mem_univ, true_and] at hj ⊢; exact hj.2
            · intro j _ _; exact mul_nonneg hlam (div_nonneg (L.τ_pos j).le hm.le)
    have h2 : L.w (L.center i) ≤ L.wbar := by
      unfold Line.wbar; exact le_sup' L.w (mem_univ _)
    have h3 : lam * L.w (L.center i) ≤ L.load lam := by
      unfold Line.load; exact mul_le_mul_of_nonneg_left h2 hlam
    linarith
  have hτbar : 0 ≤ L.τbar := by
    unfold Line.τbar
    exact le_trans (L.τ_pos ⟨0, L.l_pos⟩).le (le_sup' L.τ (mem_univ _))
  -- Γ^(i) ≥ 0
  have hGnn : ∀ i : Fin L.l, 0 ≤ L.Gamma lam γ i := by
    suffices H : ∀ n : ℕ, ∀ i : Fin L.l, i.val = n → 0 ≤ L.Gamma lam γ i from
      fun i => H _ i rfl
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
      intro i hin
      have ih : ∀ k : Fin L.l, k < i → 0 ≤ L.Gamma lam γ k :=
        fun k hk => ihn k.val (by rw [← hin]; exact hk) k rfl
      rw [Line.Gamma_eq]
      apply div_nonneg _ (hden i).le
      have hGB : 0 ≤ L.GammaBar lam γ i := by
        unfold Line.GammaBar
        apply sum_nonneg
        intro k hk
        simp only [mem_filter, mem_univ, true_and] at hk
        exact add_nonneg (ih k hk) (L.τ_pos k).le
      have hm : (0 : ℝ) < L.m (L.center i) := by exact_mod_cast L.m_pos _
      apply add_nonneg (by linarith)
      apply sum_nonneg
      intro j _
      apply div_nonneg _ hm.le
      have := (L.τ_pos j).le
      positivity
  obtain ⟨T, hT⟩ := busy_period_bound L lam γ hlam hγ hload R hR harr
  refine ⟨T, fun j p hpj hTa => ?_⟩
  have hG := hGnn j
  -- case analysis on the arrival time
  cases ha : R.arrive p j with
  | top => simp
  | coe a =>
    rw [ha] at hTa
    have hTa' : T j < a := by exact_mod_cast hTa
    -- all t ∈ [a, start) are busy
    have hbusy : ∀ t : ℝ, a ≤ t → (t : WithTop ℝ) < R.start p j → R.Busy j t := by
      intro t hat hts
      refine ⟨p, j, rfl, le_refl _, hpj, ?_, hts⟩
      rw [ha]; exact_mod_cast hat
    have key : R.start p j ≤ ((a + L.Gamma lam γ j : ℝ) : WithTop ℝ) := by
      by_contra hcon
      push Not at hcon
      -- choose T₂ strictly between a + Γ and start
      obtain ⟨T₂, hT₂1, hT₂2⟩ : ∃ T₂ : ℝ, a + L.Gamma lam γ j < T₂ ∧ (T₂ : WithTop ℝ) < R.start p j := by
        cases hs : R.start p j with
        | top => exact ⟨a + L.Gamma lam γ j + 1, by linarith, by simp⟩
        | coe s =>
          rw [hs] at hcon
          have : a + L.Gamma lam γ j < s := by exact_mod_cast hcon
          exact ⟨(a + L.Gamma lam γ j + s) / 2, by linarith, by
            rw [WithTop.coe_lt_coe]; linarith⟩
      have := hT j a T₂ hTa' (by linarith) (fun t h1 h2 =>
        hbusy t h1 (lt_of_le_of_lt (by exact_mod_cast h2) hT₂2))
      linarith
    calc R.start p j + ((L.τ j : ℝ) : WithTop ℝ)
        ≤ ((a + L.Gamma lam γ j : ℝ) : WithTop ℝ) + ((L.τ j : ℝ) : WithTop ℝ) := by
          gcongr
      _ = ((a : ℝ) : WithTop ℝ) + ((L.Gamma lam γ j + L.τ j : ℝ) : WithTop ℝ) := by
          rw [← WithTop.coe_add, ← WithTop.coe_add, add_assoc]
