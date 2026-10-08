-- Prove2me | solution 1 for RegretBandits.Stochastic.ucb_three_events
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:45:47.386592+00:00
-- url     : https://prove2.me/submissions/279dc6ba-e3f9-452e-b29f-a56f163cbd79

import Mathlib
import Definitions.Def_ImprovedLinBandits_UCBDelta_armModel
import Definitions.Def_RegretBandits_Stochastic_model
import Definitions.Def_RegretBandits_Stochastic_alphaPsiUCB

set_option autoImplicit false

open RegretBandits.Stochastic ImprovedLinBandits.UCBDelta in
theorem solution {Ω : Type*} {K : ℕ} (hK : 2 ≤ K) (ψ : ℝ → ℝ) (α : ℝ) (hα : 0 < α)
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (I : ℕ → Ω → Fin K)
    (hrun : IsAlphaPsiUCBRun ψ α X I) (n t : ℕ) (htn : t + 1 ≤ n) (ω : Ω) (i istar : Fin K)
    (hstar : μ istar = bestMean μ) (hgap : 0 < gap μ i)
    (hψpos : (0 : EReal) < legendreFenchel ψ (gap μ i / 2))
    (hplayed : ∀ j, pullCount I j t ω ≠ 0) (hIt : I (t + 1) ω = i) :
    ucbIndex ψ α X I istar t ω ≤ bestMean μ ∨
      μ i + lfInv ψ (α * Real.log ((t : ℝ) + 1) / (pullCount I i t ω : ℝ)) <
        sampleMean X i (pullCount I i t ω) ω ∨
      (pullCount I i t ω : ℝ) <
        α * Real.log (n : ℝ) / (legendreFenchel ψ (gap μ i / 2)).toReal := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hA, hB, hC⟩ := hcon
  set T : ℕ := pullCount I i t ω with hT
  set y : ℝ := α * Real.log ((t : ℝ) + 1) / (T : ℝ) with hy
  set L : ℝ := lfInv ψ y with hL
  have hTpos : (0 : ℝ) < (T : ℝ) := by
    have := hplayed i
    exact_mod_cast Nat.pos_of_ne_zero this
  -- UCB maximality
  have hmax := (hrun ω t).2 hplayed istar
  rw [hIt] at hmax
  have hidx : ucbIndex ψ α X I i t ω = sampleMean X i T ω + L := rfl
  have hgapdef : gap μ i = bestMean μ - μ i := rfl
  -- L > Δ/2
  have hLgt : gap μ i / 2 < L := by
    have h1 : bestMean μ < sampleMean X i T ω + L := lt_of_lt_of_le hA (hidx ▸ hmax)
    rw [hgapdef]; linarith
  -- L ≤ Δ/2
  have hmem : gap μ i / 2 ∈ {ε : ℝ | 0 ≤ ε ∧ (y : EReal) ≤ legendreFenchel ψ ε} := by
    refine ⟨by linarith, ?_⟩
    have hlog : Real.log ((t : ℝ) + 1) ≤ Real.log (n : ℝ) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast htn
    have hlog0 : 0 ≤ Real.log ((t : ℝ) + 1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg t : (0:ℝ) ≤ t)])
    by_cases htop : legendreFenchel ψ (gap μ i / 2) = ⊤
    · rw [htop]; exact le_top
    · have hbot : legendreFenchel ψ (gap μ i / 2) ≠ ⊥ := ne_bot_of_gt hψpos
      have hcoe : legendreFenchel ψ (gap μ i / 2) =
          ((legendreFenchel ψ (gap μ i / 2)).toReal : EReal) := (EReal.coe_toReal htop hbot).symm
      generalize hcd : (legendreFenchel ψ (gap μ i / 2)).toReal = c at hcoe hC
      rw [hcoe] at hψpos ⊢
      have hc : (0 : ℝ) < c := by exact_mod_cast hψpos
      have hTc : α * Real.log (n : ℝ) ≤ (T : ℝ) * c := by
        rw [div_le_iff₀ hc] at hC; exact hC
      have : y ≤ c := by
        rw [hy, div_le_iff₀ hTpos]
        nlinarith
      exact_mod_cast this
  have hLle : L ≤ gap μ i / 2 := csInf_le ⟨0, fun x hx => hx.1⟩ hmem
  linarith
