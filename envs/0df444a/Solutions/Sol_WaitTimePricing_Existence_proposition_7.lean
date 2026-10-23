-- Prove2me | solution 1 for WaitTimePricing.Existence.proposition_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T09:36:16.631635+00:00
-- url     : https://prove2.me/submissions/6dee5154-148c-4a8a-8f53-79962dc6c047

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Setting
import Definitions.Def_WaitTimePricing_Existence_Algorithm1
import Theorems.Thm_WaitTimePricing_Existence_lemma_7
import Theorems.Thm_WaitTimePricing_Existence_proposition_6

open Set Filter WaitTimePricing.Existence

lemma sSup_image_close {S : Set ℝ} (f h : ℝ → ℝ) (δ : ℝ) (hS : S.Nonempty)
    (hfh : ∀ x ∈ S, |f x - h x| ≤ δ) (hf : BddAbove (f '' S)) :
    |sSup (f '' S) - sSup (h '' S)| ≤ δ := by
  obtain ⟨B, hB⟩ := hf
  have hh : BddAbove (h '' S) := ⟨B + δ, by
    rintro _ ⟨x, hx, rfl⟩
    have := hB ⟨x, hx, rfl⟩; have := (abs_le.1 (hfh x hx)); linarith⟩
  have hfb : BddAbove (f '' S) := ⟨B, hB⟩
  rw [abs_le]; constructor
  · have : sSup (h '' S) ≤ sSup (f '' S) + δ := by
      apply csSup_le (hS.image _)
      rintro _ ⟨x, hx, rfl⟩
      have h1 := le_csSup hfb ⟨x, hx, rfl⟩
      have := (abs_le.1 (hfh x hx)); linarith
    linarith
  · have : sSup (f '' S) ≤ sSup (h '' S) + δ := by
      apply csSup_le (hS.image _)
      rintro _ ⟨x, hx, rfl⟩
      have h1 := le_csSup hh ⟨x, hx, rfl⟩
      have := (abs_le.1 (hfh x hx)); linarith
    linarith

theorem solution (M : Model) (hM : M.Standing) (obj : Objective) :
    gbar M obj = M.lam * max (innerMax M obj (Vbar M obj) 0) 0 := by
  have hw0 : 0 ≤ wbar M := Real.sSup_nonneg (fun x hx => le_of_lt hx.1)
  have hC := hM.C_pos
  obtain ⟨-, hunif, -, -, hlip⟩ := proposition_6 M hM obj
  have h7 := lemma_7 M hM obj
  set I := Icc 0 (wbar M + M.C) with hI
  have hU0 : 0 ≤ deriv M.U 0 := hM.deriv_U_nonneg 0 ⟨le_rfl, hC.le⟩
  have htI : ∀ p, 0 + tOf M p ∈ I := by
    intro p
    have h1 : 0 ≤ tOf M p := Real.sSup_nonneg (fun x hx => hx.1.1)
    have h2 : tOf M p ≤ M.C := Real.sSup_le (fun x hx => hx.1.2) hC.le
    exact ⟨by linarith, by linarith⟩
  have h0I : (0:ℝ) ∈ I := ⟨le_rfl, by linarith⟩
  set S := Icc 0 (Gamma M 0) with hS
  have hSne : S.Nonempty := ⟨0, le_rfl, Real.sSup_nonneg (fun x hx => hx.1.1)⟩
  have hGle : Gamma M 0 ≤ deriv M.U 0 := Real.sSup_le (fun x hx => hx.1.2) hU0
  -- boundedness of the objective `v` on `[0, Γ(0)]`
  obtain ⟨Bu, hBu⟩ := (isCompact_Icc (a := (0:ℝ)) (b := M.C)).bddAbove_image
    (hM.U_contDiff.continuous.continuousOn)
  have hv : ∀ p ∈ S, v M obj p ≤ max (deriv M.U 0 * M.C) Bu := by
    intro p hp
    have h1 : 0 ≤ tOf M p := Real.sSup_nonneg (fun x hx => hx.1.1)
    have h2 : tOf M p ≤ M.C := Real.sSup_le (fun x hx => hx.1.2) hC.le
    cases obj with
    | revenue =>
      show p * tOf M p ≤ _
      have : p * tOf M p ≤ deriv M.U 0 * M.C :=
        mul_le_mul (le_trans hp.2 hGle) h2 h1 hU0
      exact le_trans this (le_max_left _ _)
    | welfare =>
      show M.U (tOf M p) ≤ _
      exact le_trans (hBu ⟨tOf M p, ⟨h1, h2⟩, rfl⟩) (le_max_right _ _)
  -- Lipschitz bound gives boundedness of `V^ḡ` on `I`
  have hg0 : 0 ≤ gbar M obj := by
    have h := hlip (wbar M + M.C) ⟨by linarith, le_rfl⟩ 0 h0I
    rw [sub_zero, abs_of_pos (by linarith : (0:ℝ) < wbar M + M.C)] at h
    have h' : 0 * (wbar M + M.C) ≤ gbar M obj * (wbar M + M.C) := by
      rw [zero_mul]; exact le_trans (abs_nonneg _) h
    exact le_of_mul_le_mul_right h' (by linarith)
  have hVb : ∀ x ∈ I, Vbar M obj x ≤ Vbar M obj 0 + gbar M obj * (wbar M + M.C) + |gbar M obj| * 0 := by
    intro x hx
    have h := hlip x hx 0 h0I
    have h2 : |x - 0| ≤ wbar M + M.C := by rw [sub_zero, abs_of_nonneg hx.1]; exact hx.2
    have := le_trans h (mul_le_mul_of_nonneg_left h2 hg0)
    linarith [le_abs_self (Vbar M obj x - Vbar M obj 0)]
  have hbdd : BddAbove ((fun p => v M obj p - alpha obj * M.c 0 + Vbar M obj (0 + tOf M p)
      - Vbar M obj 0) '' S) := by
    refine ⟨max (deriv M.U 0 * M.C) Bu + |alpha obj * M.c 0| + gbar M obj * (wbar M + M.C), ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    have := hv p hp
    have := hVb _ (htI p)
    have := neg_abs_le (alpha obj * M.c 0)
    simp only [mul_zero, add_zero] at *
    linarith
  -- convergence of the inner maxima
  have hconv : Tendsto (fun j : ℕ => innerMax M obj (VgN M obj (gbar M obj) (2 ^ j)) 0) atTop
      (nhds (innerMax M obj (Vbar M obj) 0)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    rw [Metric.tendstoUniformlyOn_iff] at hunif
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hunif (ε / 3) (by linarith))
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    have hd := sSup_image_close
      (fun p => v M obj p - alpha obj * M.c 0 + Vbar M obj (0 + tOf M p) - Vbar M obj 0)
      (fun p => v M obj p - alpha obj * M.c 0 + VgN M obj (gbar M obj) (2 ^ n) (0 + tOf M p)
        - VgN M obj (gbar M obj) (2 ^ n) 0) (2 * (ε / 3)) hSne (by
        intro p _
        have a1 := hN n hn _ (htI p)
        have a2 := hN n hn 0 h0I
        rw [Real.dist_eq] at a1 a2
        have := abs_sub_lt_iff.1 a1; have := abs_sub_lt_iff.1 a2
        rw [abs_le]; constructor <;> linarith) hbdd
    unfold innerMax
    rw [abs_sub_comm]
    linarith
  have hlimK : Tendsto (fun j : ℕ => KgN M obj (gbar M obj) (2 ^ j) 0) atTop
      (nhds (M.lam * max (innerMax M obj (Vbar M obj) 0) 0)) := by
    have : (fun j : ℕ => KgN M obj (gbar M obj) (2 ^ j) 0) =
        fun j => M.lam * max (innerMax M obj (VgN M obj (gbar M obj) (2 ^ j)) 0) 0 := by
      funext j; simp [KgN, slopeAdj]
    rw [this]
    exact (hconv.max tendsto_const_nhds).const_mul _
  exact tendsto_nhds_unique h7 hlimK
