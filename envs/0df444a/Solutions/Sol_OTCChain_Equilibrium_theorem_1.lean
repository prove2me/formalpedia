-- Prove2me | solution 1 for OTCChain.Equilibrium.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T21:45:32.421994+00:00
-- url     : https://prove2.me/submissions/2e485f21-101e-4c27-8da6-1d46c3b7dda5

import Mathlib
import Definitions.Def_OTCChain_Equilibrium_Model
import Definitions.Def_OTCChain_Equilibrium_ClosedForm
import Theorems.Thm_OTCChain_Equilibrium_eq_55_57
import Theorems.Thm_OTCChain_Equilibrium_eq_61_63
import Theorems.Thm_OTCChain_Equilibrium_eq_64_Ns
import Theorems.Thm_OTCChain_Equilibrium_eq_65_66_Nb
import Theorems.Thm_OTCChain_Equilibrium_eq_59_60_corrected
import Theorems.Thm_OTCChain_Equilibrium_eq_79_82
import Theorems.Thm_OTCChain_Equilibrium_eq_83_trade_rule
import Theorems.Thm_OTCChain_Equilibrium_eq_20
import Theorems.Thm_OTCChain_Equilibrium_eq_21
import Theorems.Thm_OTCChain_Equilibrium_eq_84
import Theorems.Thm_OTCChain_Equilibrium_step_III

open Set OTCChain.Equilibrium

theorem solution (M : Params) (hM : M.Standing) (hc : 0 < M.c) (hcs : M.c < cStar M) :
    (∃! δ, δ ∈ Icc 0 M.Δbar ∧ rhs20 M δ = M.c) ∧
    (∃! δ, δ ∈ Icc 0 M.Δbar ∧ rhs21 M δ = M.c) ∧
    (∃ (Δb Δs : ℝ) (μ : Densities) (V : Values), IsIntermEq M Δb Δs μ V) ∧
    ∀ (Δb Δs : ℝ) (μ : Densities) (V : Values), IsIntermEq M Δb Δs μ V →
      rhs20 M Δb = M.c ∧ rhs21 M Δs = M.c ∧
      μ.Nb M = NbOf M (M.F Δb) ∧ μ.Ns M = NsOf M (M.F Δs) ∧
      (∀ Δ ∈ Icc 0 M.Δbar, Δ ≠ Δb → Δ ≠ Δs →
        μ.μb Δ = (candDensities M Δb Δs).μb Δ ∧ μ.μs Δ = (candDensities M Δb Δs).μs Δ ∧
        μ.μn Δ = (candDensities M Δb Δs).μn Δ ∧ μ.μh Δ = (candDensities M Δb Δs).μh Δ) ∧
      (∀ Δ ∈ Icc 0 M.Δbar, V.V0 Δ = candV0 M Δb Δs Δ ∧ V.V1 Δ = candV1 M Δb Δs Δ) ∧
      (∀ x ∈ Ioc Δb M.Δbar, ∀ y ∈ Ico 0 Δs,
        (0 < surplus V x y ↔ y < x) ∧
        (y < x → price M V x y = candV1 M Δb Δs x - candV0 M Δb Δs x
          - M.η * (candV1 M Δb Δs x + candV0 M Δb Δs y
            - (candV0 M Δb Δs x + candV1 M Δb Δs y)))) := by
  obtain ⟨h20a, -, h20u, h20e⟩ := eq_20 M hM
  obtain ⟨h21a, -, h21u, h21e⟩ := eq_21 M hM
  obtain ⟨-, -, -, -, hc20, hc21, hcross⟩ := eq_84 M hM
  have hU20 := h20u M.c hc (by linarith)
  have hU21 := h21u M.c hc (by linarith)
  refine ⟨hU20, hU21, ?_, ?_⟩
  · obtain ⟨Δb, ⟨hbI, hb⟩, -⟩ := hU20
    obtain ⟨Δs, ⟨hsI, hs⟩, -⟩ := hU21
    have hlt : Δb < Δs := (hcross M.c Δb Δs hc hbI hb hsI hs).2 hcs
    have hb0 : 0 < Δb := by
      rcases hbI.1.lt_or_eq with h | h
      · exact h
      · subst h; rw [h20a] at hb; linarith
    have hsD : Δs < M.Δbar := by
      rcases hsI.2.lt_or_eq with h | h
      · exact h
      · rw [h, h21a] at hs; linarith
    obtain ⟨hB, hO⟩ := step_III M hM hc hcs Δb Δs hbI hb hsI hs
    exact ⟨Δb, Δs, candDensities M Δb Δs, candValues M Δb Δs,
      hb0, hlt, hsD, (eq_59_60_corrected M hM Δb Δs hb0 hlt hsD).1, hB, hO⟩
  · intro Δb Δs μ V hE
    obtain ⟨h0, h1, h2, hSS, -, -⟩ := id hE
    have hNb := (eq_65_66_Nb M hM Δb Δs h0 h1 h2 μ hSS).2
    have hNs := (eq_64_Ns M hM Δb Δs h0 h1 h2 μ hSS).2
    have hV := eq_79_82 M hM hc hcs Δb Δs μ V hE
    refine ⟨h20e hc hcs Δb Δs μ V hE, h21e hc hcs Δb Δs μ V hE, hNb, hNs, ?_, ?_, ?_⟩
    · intro Δ hΔ hne1 hne2
      rcases lt_trichotomy Δ Δb with hlt | heq | hgt
      · obtain ⟨e1, e2, e3, e4⟩ := eq_55_57 M hM Δb Δs h0 h1 h2 μ hSS Δ ⟨hΔ.1, hlt⟩
        have hlt' : Δ < Δs := lt_trans hlt h1
        simp only [candDensities, if_pos hlt, if_pos hlt']
        rw [e1, e2, e3, e4, hNb]
        exact ⟨rfl, rfl, rfl, rfl⟩
      · exact absurd heq hne1
      · rcases lt_trichotomy Δ Δs with hlt2 | heq2 | hgt2
        · obtain ⟨e1, e2, -, e4, e5⟩ :=
            (eq_59_60_corrected M hM Δb Δs h0 h1 h2).2 μ hSS Δ ⟨hgt, hlt2⟩
          have hn : ¬ Δ < Δb := not_lt.2 hgt.le
          simp only [candDensities, if_neg hn, if_pos hlt2]
          rw [e5, e4]
          exact ⟨rfl, rfl, e1, e2⟩
        · exact absurd heq2 hne2
        · obtain ⟨e1, e2, e3, e4⟩ := eq_61_63 M hM Δb Δs h0 h1 h2 μ hSS Δ ⟨hgt2, hΔ.2⟩
          have hn : ¬ Δ < Δb := not_lt.2 (le_trans h1.le hgt2.le)
          have hn2 : ¬ Δ < Δs := not_lt.2 hgt2.le
          simp only [candDensities, if_neg hn, if_neg hn2]
          rw [e1, e2, e3, e4, hNs]
          exact ⟨rfl, rfl, rfl, rfl⟩
    · intro Δ hΔ
      exact ⟨(hV Δ hΔ).2.2.1, (hV Δ hΔ).2.2.2⟩
    · intro x hx y hy
      refine ⟨(eq_83_trade_rule M hM hc hcs Δb Δs μ V hE).2 x hx y hy, fun _ => ?_⟩
      have hxI : x ∈ Icc 0 M.Δbar := ⟨le_trans h0.le hx.1.le, hx.2⟩
      have hyI : y ∈ Icc 0 M.Δbar := ⟨hy.1, le_trans hy.2.le h2.le⟩
      unfold price surplus
      rw [(hV x hxI).2.2.1, (hV x hxI).2.2.2, (hV y hyI).2.2.1, (hV y hyI).2.2.2]
