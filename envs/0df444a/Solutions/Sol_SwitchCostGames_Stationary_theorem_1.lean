-- Prove2me | solution 1 for SwitchCostGames.Stationary.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:15:58.354988+00:00
-- url     : https://prove2.me/submissions/6b08fedb-121e-4069-aadf-48bd6f27cb03

import Mathlib
import Definitions.Def_SwitchCostGames_Stationary_Model
import Theorems.Thm_SwitchCostGames_Stationary_value_exists
import Theorems.Thm_SwitchCostGames_Stationary_value_regular
import Theorems.Thm_SwitchCostGames_Stationary_value_le_pure_minimax
import Theorems.Thm_SwitchCostGames_Stationary_stationary_response_affine

open SwitchCostGames.Stationary

theorem solution {m n : ℕ} [NeZero m] [NeZero n] (G : Game m n) :
    ∃ v : ℝ → ℝ,
      (∀ c : ℝ, 0 ≤ c → IsValue G c (v c)) ∧
      ContinuousOn v (Set.Ici 0) ∧ MonotoneOn v (Set.Ici 0) ∧ ConcaveOn ℝ (Set.Ici 0) v ∧
      IsPiecewiseAffineOn v (Set.Ici 0) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, C ≤ c → v c = v C) ∧
      (∀ cLo cHi : ℝ, 0 ≤ cLo → cLo < cHi →
        (∃ α β : ℝ, ∀ c ∈ Set.Icc cLo cHi, v c = α + β * c) →
        ∃ τ : Strategy2 m n, IsStationary2 τ ∧
          ∀ c ∈ Set.Icc cLo cHi, ∀ σ : Strategy1 m n, payoff G c σ τ ≤ v c) := by
  classical
  -- choose the value at every weight
  let v : ℝ → ℝ := fun c =>
    if hc : 0 ≤ c then Classical.choose (value_exists G c hc) else 0
  have hv : ∀ c : ℝ, 0 ≤ c → IsValue G c (v c) := by
    intro c hc
    simp only [v, dif_pos hc]
    exact Classical.choose_spec (value_exists G c hc)
  obtain ⟨hcont, hmono, hconc, hpw⟩ := value_regular G v hv
  refine ⟨v, hv, hcont, hmono, hconc, hpw, ?_, ?_⟩
  · -- eventually constant
    obtain ⟨B, hB⟩ := hpw
    set M := Finset.univ.inf' Finset.univ_nonempty
      (fun j : Fin n => Finset.univ.sup' Finset.univ_nonempty (fun i : Fin m => G.A i j))
    have hbd : ∀ c : ℝ, 0 ≤ c → v c ≤ M := fun c hc =>
      value_le_pure_minimax G c (v c) hc (hv c hc)
    let C : ℝ := (insert 0 B).sup' (Finset.insert_nonempty 0 B) id
    have hC0 : 0 ≤ C := Finset.le_sup' id (Finset.mem_insert_self 0 B)
    have hCB : ∀ x ∈ B, x ≤ C := fun x hx =>
      Finset.le_sup' id (Finset.mem_insert_of_mem hx)
    refine ⟨C, hC0, ?_⟩
    intro c hc
    by_contra hne
    have hlt : v C < v c := lt_of_le_of_ne
      (hmono (Set.mem_Ici.2 hC0) (Set.mem_Ici.2 (hC0.trans hc)) hc) (Ne.symm hne)
    have hCc : C < c := by
      rcases eq_or_lt_of_le hc with h | h
      · exact absurd (by rw [h]) hne
      · exact h
    -- a far point
    set K : ℝ := c + (M - v C + 1) * (c - C) / (v c - v C) + 1 with hK
    have hpos : 0 < v c - v C := by linarith
    have hdc : 0 < c - C := by linarith
    have hMv : v C ≤ M := hbd C hC0
    have hcK : c ≤ K := by
      have : 0 ≤ (M - v C + 1) * (c - C) / (v c - v C) := by
        apply div_nonneg _ hpos.le
        exact mul_nonneg (by linarith) hdc.le
      linarith
    obtain ⟨α, β, hab⟩ := hB C K (by linarith) (fun x hx => Set.mem_Ici.2 (hC0.trans hx.1))
      (fun x hx hx' => by
        have := hCB x hx
        exact absurd hx'.1 (not_lt.2 this))
    have h1 := hab C ⟨le_refl _, by linarith⟩
    have h2 := hab c ⟨hc, hcK⟩
    have h3 := hab K ⟨by linarith, le_refl _⟩
    have hβ : β = (v c - v C) / (c - C) := by
      field_simp
      linarith
    have hvK : v K = v C + β * (K - C) := by linarith
    have hKM : v K ≤ M := hbd K (by linarith)
    have : v C + β * (K - C) > M := by
      rw [hβ]
      have e : K - C = (c - C) + (M - v C + 1) * (c - C) / (v c - v C) + 1 := by
        rw [hK]; ring
      rw [e]
      have e2 : (v c - v C) / (c - C) * ((c - C) + (M - v C + 1) * (c - C) / (v c - v C) + 1)
          = (v c - v C) + (M - v C + 1) + (v c - v C) / (c - C) := by
        field_simp
      rw [e2]
      have : 0 < (v c - v C) / (c - C) := div_pos hpos hdc
      linarith
    linarith
  · -- robustness of optimal strategies along a linear piece
    intro cLo cHi hLo hlt ⟨α, β, hab⟩
    set cs : ℝ := (cLo + cHi) / 2 with hcs
    have hcs0 : 0 ≤ cs := by rw [hcs]; linarith
    obtain ⟨σs, τs, _, hτs, hσs_guar, hτs_guar⟩ := hv cs hcs0
    obtain ⟨α', β', σ0, _, hresp⟩ := stationary_response_affine G τs hτs
    refine ⟨τs, hτs, ?_⟩
    -- upper bound: v c ≤ α' + β' c for every c ≥ 0
    have hup : ∀ c : ℝ, 0 ≤ c → v c ≤ α' + β' * c := by
      intro c hc
      obtain ⟨σc, _, _, _, hσc, _⟩ := hv c hc
      exact (hσc τs).trans ((hresp c hc).2 σc)
    -- equality at the midpoint
    have hmid : α' + β' * cs ≤ v cs := by
      rw [← (hresp cs hcs0).1]
      exact hτs_guar σ0
    have eLo := hab cLo ⟨le_refl _, hlt.le⟩
    have eHi := hab cHi ⟨hlt.le, le_refl _⟩
    have eMid := hab cs ⟨by rw [hcs]; linarith, by rw [hcs]; linarith⟩
    have uLo := hup cLo hLo
    have uHi := hup cHi (by linarith)
    have gLo : α' + β' * cLo = α + β * cLo := by
      rw [hcs] at hmid eMid; nlinarith
    have gHi : α' + β' * cHi = α + β * cHi := by
      rw [hcs] at hmid eMid; nlinarith
    have hβ' : β' = β := by
      have : (β' - β) * (cHi - cLo) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · linarith
    have hα' : α' = α := by rw [hβ'] at gLo; linarith
    intro c hc σ
    have h0 : 0 ≤ c := hLo.trans hc.1
    rw [hab c hc, ← hα', ← hβ']
    exact (hresp c h0).2 σ
